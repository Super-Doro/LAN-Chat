const http = require('http');
const fs = require('fs');
const path = require('path');
const os = require('os');
const crypto = require('crypto');
const net = require('net');
const { Transform } = require('stream');
const { pipeline } = require('stream/promises');

const configuredPort = Number(process.env.VOID_CHAT_PORT);
const PORT = Number.isInteger(configuredPort) && configuredPort > 0 && configuredPort < 65536 ? configuredPort : 9000;
const PAGE = (() => {
  try {
    const sea = require('node:sea');
    if (sea.isSea()) return sea.getAsset('page.html', 'utf8');
  } catch {}
  const source = fs.readFileSync(__filename, 'utf8');
  const startIndex = source.lastIndexOf('/* PAGE_START');
  const endIndex = source.lastIndexOf('PAGE_END */');
  if (startIndex === -1 || endIndex === -1 || endIndex <= startIndex) {
    return '<!doctype html><html lang="zh-CN"><body><h1>页面加载失败</h1></body></html>';
  }
  return source.slice(startIndex + '/* PAGE_START'.length, endIndex).trimStart();
})();
const RETENTION_MS = 5 * 60 * 1000;
const MAX_MESSAGES = 1000;
const MAX_CONNECTIONS = 100;
const ACTIVE_WINDOW_MS = 6000;
const MAX_BODY_BYTES = 16 * 1024;
const MAX_FILE_BYTES = 1024 * 1024;
const ADMIN_PASSWORD = process.env.ADMIN_PASSWORD || '666666';
const RENDER_BATCH = 100;
const POLL_HINT = 1500;
const BLOCK_HINT = 5000;
const MAX_CONNECTIONS_PER_IP = 1;
const SEND_WINDOW_MS = 5000;
const SEND_WINDOW_LIMIT = 2;
const RECALL_WINDOW_MS = 3 * 60 * 1000;
const FILE_DIR = path.join(os.tmpdir(), 'void-chat-files');
fs.mkdirSync(FILE_DIR,{recursive:true});
const channels = [
  { id: 'channel1', name: '唠嗑' },
  { id: 'channel2', name: '吐槽' },
  { id: 'channel3', name: '频道3' },
  { id: 'channel4', name: '频道4' },
  { id: 'channel5', name: '频道5' }
];
const messages = new Map(channels.map(channel => [channel.id, []]));
const privateMessages = new Map();
const clients = new Map();
const reservedNames = new Map();
const adminTokens = new Map();
const bannedIps = new Map();
const ownedFileIds = new Set();
const localAddresses = new Set(['127.0.0.1','::1',...Object.values(os.networkInterfaces()).flat().filter(Boolean).map(item=>item.address)]);
const defaultNames = ['雾中信号','午夜电台','路过的人','蓝色回声','未读消息','七号窗口','风的背面','纸上月光','无名之声','半格电量','雨后电台','凌晨三点','玻璃海岸','远方来客','静默频道','白噪音','南墙以北','小行星带','旧磁带','临时月亮','低空飞行','纸船渡口','橘色回声','没有署名','第九街角','慢速星球','失眠旅人','空白信笺','北纬三十','候车室里','微光入口','借过一下','晴天留声机','倒带之前','未完句号','晚风收件箱','路灯下面','隐身模式','落日存档','匿名观测员','月面漫步者','雨伞借我','发呆俱乐部','半夜醒来','蓝调星期五','海边的字','轻声路过','没有目的地','风筝线外','借来的名字'];
let cursor = 0;

function json(res, status, data) { res.writeHead(status, {'Content-Type':'application/json; charset=utf-8','Access-Control-Allow-Origin':'*'}); res.end(JSON.stringify(data)); }
function body(req) { return new Promise((resolve, reject) => { let raw=''; let size=0; let settled=false; req.on('data', chunk => { if(settled) return; size+=chunk.length; if(size>MAX_BODY_BYTES) { settled=true; reject(new Error('body too large')); return; } raw+=chunk; }); req.on('end', () => { if(settled) return; try { settled=true; resolve(JSON.parse(raw)); } catch { settled=true; reject(new Error('invalid json')); } }); req.on('error', () => { if(!settled) { settled=true; reject(new Error('request error')); } }); }); }
function requestIp(req) { return String(req.socket.remoteAddress||'').replace(/^::ffff:/,''); }
function isLocalRequest(req) { return localAddresses.has(requestIp(req)); }
function getAdmin(req) { const token=String(req.headers['x-admin-token']||''); const record=adminTokens.get(token); if(!record||record.expiresAt<Date.now()||record.ip!==requestIp(req)) { if(token) adminTokens.delete(token); return null; } record.expiresAt=Date.now()+60*60*1000; return record; }
function allocateName(client, requested) { const wanted=Array.from(String(requested||'').trim()).slice(0,5).join(''); const current=reservedNames.get(client); if(current===wanted && wanted) return wanted; if(current) reservedNames.delete(client); const used=new Set(reservedNames.values()); if(wanted && !used.has(wanted)) { reservedNames.set(client,wanted); return wanted; } const available=defaultNames.find(name=>!used.has(name)); if(available) { reservedNames.set(client,available); return available; } let index=1; let fallback=''; do { fallback=index<10?`匿名用户${index}`:`匿名${index}`; index++; } while(used.has(fallback)); reservedNames.set(client,fallback); return fallback; }
function getChannel(id) { return messages.has(id) ? id : null; }
function pruneClients(now=Date.now()) { for(const [id,client] of clients) if(now-client.lastSeen>ACTIVE_WINDOW_MS) { clients.delete(id); reservedNames.delete(id); } }
function onlineByChannel(now=Date.now()) { const counts=Object.fromEntries(channels.map(channel=>[channel.id,0])); for(const client of clients.values()) if(now-client.lastSeen<=ACTIVE_WINDOW_MS) counts[client.channel]++; return counts; }
function onlineUsers(now=Date.now()) { return [...clients.entries()].filter(([,client])=>now-client.lastSeen<=ACTIVE_WINDOW_MS).map(([id,client])=>({id,name:reservedNames.get(id)||client.name||'匿名用户',avatar:client.avatar||'○',channel:client.channel})).sort((a,b)=>a.name.localeCompare(b.name,'zh-CN')); }
function privateKey(first,second) { return JSON.stringify([first,second].sort()); }
function getPrivateMessages(first,second,create=false) { const key=privateKey(first,second); if(create&&!privateMessages.has(key)) privateMessages.set(key,[]); return privateMessages.get(key)||[]; }
function privateUnreadFor(clientId) {
  const record=clients.get(clientId); const read=record?.privateRead||new Map(); const counts={};
  for(const thread of privateMessages.values()) for(const message of thread) {
    if(message.recipientId!==clientId||message.recalled||message.cursor<=(read.get(message.senderId)||0)) continue;
    counts[message.senderId]=(counts[message.senderId]||0)+1;
  }
  return counts;
}
function privateActivityFor(clientId) {
  const activity={};
  for(const thread of privateMessages.values()) for(const message of thread) {
    if(message.senderId!==clientId&&message.recipientId!==clientId) continue;
    const peerId=message.senderId===clientId?message.recipientId:message.senderId;
    activity[peerId]=Math.max(activity[peerId]||0,message.at);
  }
  return activity;
}
function filePath(fileId) { return path.join(FILE_DIR, fileId); }
function forgetFile(fileId) { ownedFileIds.delete(fileId); return fs.promises.rm(filePath(fileId),{force:true}).catch(()=>{}); }
function deleteMessageFile(message) { if(message?.file?.id) forgetFile(message.file.id); }
function cleanExpiredFilesOnDisk(now=Date.now()) {
  fs.readdir(FILE_DIR,{withFileTypes:true},(error,entries)=>{ if(error) return; entries.filter(entry=>entry.isFile()).forEach(entry=>{ const target=path.join(FILE_DIR,entry.name); fs.stat(target,(statError,stat)=>{ if(!statError&&now-stat.mtimeMs>=RETENTION_MS) fs.rm(target,{force:true},()=>{}); }); }); });
}
function keepFreshMessages(items,cutoff) { return items.filter(message=>{ if(message.at>cutoff) return true; deleteMessageFile(message); return false; }); }
function pruneMessages(now=Date.now()) {
  const cutoff=now-RETENTION_MS;
  for(const [channelId,channelMessages] of messages) messages.set(channelId,keepFreshMessages(channelMessages,cutoff));
  for(const [key,thread] of privateMessages) { const active=keepFreshMessages(thread,cutoff); if(active.length) privateMessages.set(key,active); else privateMessages.delete(key); }
}
function cleanExpiredTokens(now=Date.now()) { for(const [token,record] of adminTokens) if(record.expiresAt<now) adminTokens.delete(token); }
function disconnectClient(id) { clients.delete(id); reservedNames.delete(id); }
function disconnectIp(ip) { for(const [id,client] of clients) if(client.ip===ip) disconnectClient(id); }
function isIpBanned(ip) { return bannedIps.has(ip); }
function banList() { return [...bannedIps.entries()].map(([ip,record])=>({ip,at:record.at})).sort((a,b)=>b.at-a.at); }
function reserveSendSlot(client,now) {
  const sentAt=(client.sentAt||[]).filter(at=>now-at<SEND_WINDOW_MS);
  if(sentAt.length>=SEND_WINDOW_LIMIT) return {retryAfter:Math.max(1,SEND_WINDOW_MS-(now-sentAt[0]))};
  sentAt.push(now); return {sentAt};
}
function safeFileName(raw) {
  let decoded='';
  try { decoded=decodeURIComponent(String(raw||'')); } catch { return ''; }
  const base=path.basename(decoded).replace(/[\x00-\x1f<>:"/\\|?*]/g,'_').trim();
  return Array.from(base).slice(0,120).join('');
}
function findFileMessage(fileId) {
  for(const thread of privateMessages.values()) { const message=thread.find(item=>item.file?.id===fileId); if(message) return message; }
  return null;
}
async function receivePrivateFile(req,res,url) {
  const clientId=String(url.searchParams.get('client')||'');
  const peerId=String(url.searchParams.get('peer')||'');
  const now=Date.now(); const ip=requestIp(req);
  pruneClients(now); pruneMessages(now);
  if(isIpBanned(ip)) { req.resume(); return json(res,403,{error:'ip banned'}); }
  if(!clientId||clientId.length>128||!peerId||peerId.length>128||clientId===peerId) { req.resume(); return json(res,400,{error:'invalid private session'}); }
  const sender=clients.get(clientId); const peer=clients.get(peerId);
  if(!sender||sender.ip!==ip) { req.resume(); return json(res,403,{error:'not connected'}); }
  if(!peer) { req.resume(); return json(res,404,{error:'peer offline'}); }
  const name=safeFileName(req.headers['x-file-name']);
  if(!name) { req.resume(); return json(res,400,{error:'invalid file name'}); }
  const declaredSize=Number(req.headers['content-length']);
  if(Number.isFinite(declaredSize)&&(declaredSize<=0||declaredSize>MAX_FILE_BYTES)) { req.resume(); return json(res,413,{error:'file too large',limit:MAX_FILE_BYTES}); }
  const slot=reserveSendSlot(sender,now);
  if(slot.retryAfter) { req.resume(); return json(res,429,{error:'rate limit',retryAfter:slot.retryAfter}); }
  clients.set(clientId,{...sender,lastSeen:now,sentAt:slot.sentAt});
  const fileId=crypto.randomUUID(); const downloadToken=crypto.randomBytes(24).toString('hex');
  const target=filePath(fileId); let size=0; ownedFileIds.add(fileId);
  const limiter=new Transform({transform(chunk,encoding,callback) { size+=chunk.length; if(size>MAX_FILE_BYTES) { const error=new Error('file too large'); error.code='FILE_TOO_LARGE'; callback(error); } else callback(null,chunk); }});
  try {
    await pipeline(req,limiter,fs.createWriteStream(target,{flags:'wx'}));
  } catch(error) {
    await forgetFile(fileId);
    if(!res.headersSent) return json(res,error.code==='FILE_TOO_LARGE'?413:400,{error:error.code==='FILE_TOO_LARGE'?'file too large':'upload failed',limit:MAX_FILE_BYTES});
    return;
  }
  if(!size) { await forgetFile(fileId); return json(res,400,{error:'empty file'}); }
  const completedAt=Date.now(); pruneClients(completedAt);
  if(!clients.has(peerId)) { await forgetFile(fileId); return json(res,404,{error:'peer offline'}); }
  const currentSender=clients.get(clientId);
  if(!currentSender||currentSender.ip!==ip) { await forgetFile(fileId); return json(res,403,{error:'not connected'}); }
  const type=String(req.headers['content-type']||'application/octet-stream').replace(/[\r\n]/g,'').slice(0,100)||'application/octet-stream';
  const message={id:crypto.randomUUID(),cursor:++cursor,at:completedAt,mode:'private',channel:'private',senderId:clientId,recipientId:peerId,name:reservedNames.get(clientId)||currentSender.name||'匿名用户',avatar:currentSender.avatar||'○',text:'',file:{id:fileId,name,size,type,token:downloadToken},recalled:false};
  const thread=getPrivateMessages(clientId,peerId,true); thread.push(message);
  if(thread.length>MAX_MESSAGES) thread.splice(0,thread.length-MAX_MESSAGES).forEach(deleteMessageFile);
  json(res,201,{ok:true,message});
}
async function sendPrivateFile(req,res,url) {
  const match=url.pathname.match(/^\/api\/file\/([0-9a-f-]{36})$/i);
  if(!match) { json(res,404,{error:'not found'}); return true; }
  const fileId=match[1]; const clientId=String(url.searchParams.get('client')||''); const token=String(url.searchParams.get('token')||'');
  const now=Date.now(); const ip=requestIp(req); pruneClients(now); pruneMessages(now);
  const connected=clients.get(clientId); const message=findFileMessage(fileId);
  if(!connected||connected.ip!==ip||!message||message.recalled||now-message.at>=RETENTION_MS) { json(res,404,{error:'file unavailable'}); return true; }
  if(clientId!==message.senderId&&clientId!==message.recipientId) { json(res,403,{error:'private file'}); return true; }
  if(!message.file||token!==message.file.token) { json(res,403,{error:'invalid file token'}); return true; }
  let stat;
  try { stat=await fs.promises.stat(filePath(fileId)); } catch { json(res,410,{error:'file expired'}); return true; }
  const encoded=encodeURIComponent(message.file.name).replace(/['()*]/g,char=>'%'+char.charCodeAt(0).toString(16).toUpperCase());
  res.writeHead(200,{'Content-Type':'application/octet-stream','Content-Length':stat.size,'Content-Disposition':`attachment; filename*=UTF-8''${encoded}`,'Cache-Control':'no-store','X-Content-Type-Options':'nosniff'});
  const stream=fs.createReadStream(filePath(fileId)); stream.on('error',()=>res.destroy()); stream.pipe(res); return true;
}
function serve(req,res) {
  const url = new URL(req.url, 'http://localhost');
  if (req.method==='GET' && url.pathname==='/api/status') return json(res,200,{canAdmin:isLocalRequest(req),limit:MAX_CONNECTIONS,maxFileBytes:MAX_FILE_BYTES});
  if (req.method==='POST' && url.pathname==='/api/admin/login') return body(req).then(data => { if(!isLocalRequest(req)) return json(res,403,{error:'local only'}); if(String(data.password||'')!==ADMIN_PASSWORD) return json(res,401,{error:'wrong password'}); const token=crypto.randomBytes(24).toString('hex'); adminTokens.set(token,{ip:requestIp(req),expiresAt:Date.now()+60*60*1000}); json(res,200,{token}); }).catch(error=>json(res,error.message==='body too large'?413:400,{error:error.message==='body too large'?'body too large':'invalid'}));
  if (req.method==='POST' && url.pathname==='/api/admin/channel') return body(req).then(data => { if(!getAdmin(req)) return json(res,403,{error:'admin required'}); const channel=channels.find(item=>item.id===data.id); const name=Array.from(String(data.name||'').trim()).slice(0,10).join(''); if(!channel||!name) return json(res,400,{error:'invalid channel'}); channel.name=name; json(res,200,{channels}); }).catch(()=>json(res,400,{error:'invalid'}));
  if (req.method==='GET' && url.pathname==='/api/admin/user') { if(!getAdmin(req)) return json(res,403,{error:'admin required'}); const clientId=String(url.searchParams.get('client')||''); const client=clients.get(clientId); if(!client) return json(res,404,{error:'offline'}); return json(res,200,{id:clientId,name:reservedNames.get(clientId)||'匿名用户',ip:client.ip,channel:client.channel,lastSeen:client.lastSeen,banned:isIpBanned(client.ip)}); }
  if (req.method==='GET' && url.pathname==='/api/admin/bans') { if(!getAdmin(req)) return json(res,403,{error:'admin required'}); return json(res,200,{bans:banList()}); }
  if (req.method==='POST' && url.pathname==='/api/admin/ban') return body(req).then(data => {
    if(!getAdmin(req)) return json(res,403,{error:'admin required'});
    const ip=String(data.ip||'').trim();
    if(!net.isIP(ip)) return json(res,400,{error:'invalid ip'});
    if(localAddresses.has(ip)) return json(res,400,{error:'cannot ban local address'});
    if(data.banned===false) bannedIps.delete(ip);
    else { bannedIps.set(ip,{at:Date.now()}); disconnectIp(ip); }
    json(res,200,{ok:true,bans:banList()});
  }).catch(error=>json(res,error.message==='body too large'?413:400,{error:error.message==='body too large'?'body too large':'invalid'}));
  if (req.method==='POST' && url.pathname==='/api/file') return receivePrivateFile(req,res,url).catch(()=>{ if(!res.headersSent) json(res,500,{error:'upload failed'}); });
  if (req.method==='GET' && url.pathname.startsWith('/api/file/')) return sendPrivateFile(req,res,url).catch(()=>{ if(!res.headersSent) json(res,500,{error:'download failed'}); });
  if (req.method==='GET' && url.pathname==='/api/poll') {
    const client=String(url.searchParams.get('client') || '');
    const channel=getChannel(url.searchParams.get('channel') || 'channel1');
    const peer=String(url.searchParams.get('peer')||'');
    if(!client || client.length>128 || !channel || peer.length>128 || peer===client) return json(res,400,{error:'invalid client, channel or peer'});
    const now=Date.now(); const ip=requestIp(req); pruneClients(now);
    if(isIpBanned(ip)) return json(res,403,{error:'ip banned'});
    const existing=clients.get(client);
    if(existing && existing.ip!==ip) return json(res,403,{error:'invalid session'});
    const isExisting=!!existing;
    const ipConnections=[...clients.entries()].filter(([id,item])=>id!==client&&item.ip===ip&&now-item.lastSeen<=ACTIVE_WINDOW_MS).length;
    if(!isExisting && !isLocalRequest(req) && ipConnections>=MAX_CONNECTIONS_PER_IP) return json(res,429,{error:'ip connection limit',limit:MAX_CONNECTIONS_PER_IP,retryAfter:BLOCK_HINT});
    if(!isExisting && clients.size>=MAX_CONNECTIONS) return json(res,429,{error:'room full',limit:MAX_CONNECTIONS,retryAfter:BLOCK_HINT,online:clients.size,onlineByChannel:onlineByChannel(now),channels});
    const assignedName=allocateName(client,url.searchParams.get('name')||'');
    const avatar=Array.from(String(url.searchParams.get('avatar')||existing?.avatar||'○')).slice(0,2).join('');
    const privateRead=existing?.privateRead||new Map();
    clients.set(client,{...existing,lastSeen:now,channel,ip,name:assignedName,avatar,sentAt:existing?.sentAt||[],privateRead});
    const since=Number(url.searchParams.get('since')) || 0;
    pruneMessages(now);
    let activeMessages=messages.get(channel);
    let peerInfo=null;
    if(peer) {
      activeMessages=getPrivateMessages(client,peer);
      const newestIncoming=activeMessages.filter(message=>message.recipientId===client).reduce((latest,message)=>Math.max(latest,message.cursor),0);
      if(newestIncoming) privateRead.set(peer,Math.max(privateRead.get(peer)||0,newestIncoming));
      const peerRecord=clients.get(peer);
      peerInfo={id:peer,name:reservedNames.get(peer)||peerRecord?.name||'已离线用户',avatar:peerRecord?.avatar||'○',online:!!peerRecord};
    }
    return json(res,200,{cursor,messages:activeMessages.filter(m=>m.cursor>since),mode:peer?'private':'channel',peer:peerInfo,privateUnread:privateUnreadFor(client),privateActivity:privateActivityFor(client),online:clients.size,onlineByChannel:onlineByChannel(now),users:onlineUsers(now),channels,retentionMs:RETENTION_MS,recallWindowMs:RECALL_WINDOW_MS,maxFileBytes:MAX_FILE_BYTES,assignedName,limit:MAX_CONNECTIONS,renderBatch:RENDER_BATCH,pollInterval:POLL_HINT});
  }
  if (req.method==='POST' && url.pathname==='/api/message') return body(req).then(data => {
    if(typeof data.text!=='string'||!data.text.trim()) return json(res,400,{error:'empty'});
    const client=String(data.id||''); const channel=getChannel(data.channel); const peer=String(data.peer||''); const isPrivate=data.mode==='private'; const now=Date.now(); const ip=requestIp(req);
    pruneClients(now); pruneMessages(now);
    if(isIpBanned(ip)) return json(res,403,{error:'ip banned'});
    if(!client||client.length>128||!channel||!clients.has(client)) return json(res,403,{error:'not connected'});
    const existing=clients.get(client);
    if(existing.ip!==ip) return json(res,403,{error:'invalid session'});
    if(isPrivate&&(!peer||peer===client||peer.length>128)) return json(res,400,{error:'invalid peer'});
    if(isPrivate&&!clients.has(peer)) return json(res,404,{error:'peer offline'});
    const slot=reserveSendSlot(existing,now);
    if(slot.retryAfter) return json(res,429,{error:'rate limit',retryAfter:slot.retryAfter});
    const name=allocateName(client,data.name);
    const avatar=Array.from(String(data.avatar||'○')).slice(0,2).join('');
    clients.set(client,{...existing,lastSeen:now,channel,name,avatar,sentAt:slot.sentAt});
    const message={id:crypto.randomUUID(),cursor:++cursor,at:now,mode:isPrivate?'private':'channel',channel:isPrivate?'private':channel,senderId:client,recipientId:isPrivate?peer:null,name,avatar,text:Array.from(data.text.trim()).slice(0,500).join(''),recalled:false};
    const targetMessages=isPrivate?getPrivateMessages(client,peer,true):messages.get(channel); targetMessages.push(message);
    if(targetMessages.length>MAX_MESSAGES) targetMessages.splice(0,targetMessages.length-MAX_MESSAGES);
    json(res,201,{ok:true,name,message});
  }).catch(error=>json(res,error.message==='body too large'?413:400,{error:error.message==='body too large'?'body too large':'invalid'}));
  if (req.method==='POST' && url.pathname==='/api/message/recall') return body(req).then(data => {
    const client=String(data.id||''); const messageId=String(data.messageId||''); const now=Date.now(); const ip=requestIp(req);
    if(isIpBanned(ip)) return json(res,403,{error:'ip banned'});
    const connected=clients.get(client);
    if(!connected||connected.ip!==ip) return json(res,403,{error:'not connected'});
    let target=null;
    for(const channelMessages of messages.values()) { target=channelMessages.find(message=>message.id===messageId); if(target) break; }
    if(!target) for(const thread of privateMessages.values()) { target=thread.find(message=>message.id===messageId); if(target) break; }
    if(!target) return json(res,404,{error:'message not found'});
    if(target.senderId!==client) return json(res,403,{error:'not owner'});
    if(target.recalled) return json(res,409,{error:'already recalled'});
    if(now-target.at>RECALL_WINDOW_MS) return json(res,410,{error:'recall expired'});
    deleteMessageFile(target);
    target.recalled=true; target.recalledAt=now; target.text=''; target.cursor=++cursor;
    json(res,200,{ok:true,message:target});
  }).catch(error=>json(res,error.message==='body too large'?413:400,{error:error.message==='body too large'?'body too large':'invalid'}));
  if (req.method==='GET' && (url.pathname==='/' || url.pathname==='/index.html')) { res.writeHead(200,{'Content-Type':'text/html; charset=utf-8'}); return res.end(PAGE); }
  json(res,404,{error:'not found'});
}
setInterval(pruneClients,5000);
setInterval(pruneMessages,1000);
setInterval(cleanExpiredTokens,60*1000);
setInterval(cleanExpiredFilesOnDisk,60*1000);
cleanExpiredFilesOnDisk();
process.once('exit',()=>{ for(const fileId of ownedFileIds) { try { fs.rmSync(filePath(fileId),{force:true}); } catch {} } });
process.once('SIGINT',()=>process.exit(0));
process.once('SIGTERM',()=>process.exit(0));
const localIPv4Addresses = [...new Set(Object.values(os.networkInterfaces()).flat().filter(item => item && !item.internal && (item.family === 'IPv4' || item.family === 4)).map(item => item.address))];
http.createServer(serve).listen(PORT,'0.0.0.0',()=>{
  console.log(`VOID chat running on http://localhost:${PORT}`);
  localIPv4Addresses.forEach(address => console.log(`LAN access: http://${address}:${PORT}`));
});

/* PAGE_START
<!doctype html>
<html lang="zh-CN">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>VOID / 匿名聊天室</title>
  <style>
    :root { --ink:#17211b; --muted:#718078; --line:#d9e0d9; --paper:#eef1eb; --lime:#d9ff55; --coral:#ff7059; --white:#fffef9; --dark:#1c251f; --amber:#ffb347; --font:'Microsoft YaHei', 'PingFang SC', sans-serif; }
    * { box-sizing:border-box; }
    html, body { height:100%; min-height:0; }
    body { margin:0; color:var(--ink); background:var(--paper); font-family:var(--font); font-variant-numeric:tabular-nums; overflow:hidden; }
    button, input { font:inherit; }
    .shell { width:100%; height:100vh; height:100dvh; min-height:0; overflow:hidden; display:grid; grid-template-rows:64px minmax(0,1fr); position:relative; }
    header { display:flex; justify-content:space-between; align-items:center; padding:0 24px; background:var(--dark); color:var(--white); border-bottom:1px solid #354239; }
    .brand { display:flex; align-items:center; gap:12px; font:700 17px var(--font); letter-spacing:2px; }
    .mark { width:18px; height:18px; border:2px solid var(--white); background:var(--lime); display:inline-block; transform:rotate(45deg); }
    .status { display:flex; gap:9px; align-items:center; color:#b7c2ba; font:12px var(--font); }
    .pulse { width:8px; height:8px; background:#51ad72; border-radius:50%; box-shadow:0 0 0 5px #51ad7225; }
    main { min-height:0; overflow:hidden; display:grid; grid-template-columns:minmax(260px,22vw) minmax(480px,1fr) minmax(210px,16vw); }
    .profile-panel { min-width:0; min-height:0; overflow-y:auto; padding:32px 26px; background:#f7f8f4; border-right:1px solid var(--line); display:flex; flex-direction:column; gap:20px; }
    .kicker { color:var(--coral); font:700 11px var(--font); letter-spacing:2px; }
    h1 { margin:13px 0 14px; font-size:clamp(34px,3vw,48px); line-height:1.02; font-weight:400; letter-spacing:0; }
    .intro { max-width:260px; color:var(--muted); font-size:13px; line-height:1.75; }
    .identity { border:1px solid var(--ink); background:var(--white); padding:14px; display:grid; grid-template-columns:52px minmax(0,1fr); gap:12px; align-items:center; box-shadow:5px 5px 0 var(--lime); }
    .avatar { width:52px; height:52px; border:1px solid var(--ink); display:grid; place-items:center; font-size:26px; background:var(--lime); }
    .identity small { display:block; color:var(--muted); font:10px var(--font); margin-bottom:5px; }
    .identity input { width:100%; min-width:0; padding:2px 0; border:0; border-bottom:1px solid transparent; background:transparent; font-size:16px; color:var(--ink); outline:none; }
    .identity input:focus { border-bottom-color:var(--coral); box-shadow:none; }
    .user-directory { min-height:140px; flex:1 1 0; display:flex; flex-direction:column; gap:9px; }
    .user-directory-head { display:flex; justify-content:space-between; align-items:center; font:700 10px var(--font); letter-spacing:1.5px; }
    .user-directory-head span:last-child { color:var(--muted); letter-spacing:0; }
    .user-search { width:100%; height:36px; flex:none; padding:8px 10px; font-size:12px; }
    .user-list { min-height:0; flex:1; overflow-x:hidden; overflow-y:auto; display:flex; flex-direction:column; gap:5px; padding-right:3px; scrollbar-width:thin; }
    .user-entry { display:grid; grid-template-columns:minmax(0,1fr) auto; gap:4px; }
    .user-row { width:100%; height:38px; min-width:0; padding:0 9px; display:grid; grid-template-columns:24px minmax(0,1fr) auto auto; gap:8px; align-items:center; border-color:var(--line); background:transparent; font-weight:400; }
    .user-row:hover { transform:none; box-shadow:none; border-color:var(--ink); background:var(--white); }
    .user-row.active { border-color:var(--ink); background:var(--dark); color:var(--white); }
    .user-row.self { cursor:default; }
    .user-row-avatar { font-size:16px; }
    .user-row-name { overflow:hidden; text-overflow:ellipsis; white-space:nowrap; text-align:left; font-size:12px; }
    .user-row-channel { color:var(--muted); font-size:9px; }
    .unread-dot { min-width:17px; height:17px; padding:0 4px; display:grid; place-items:center; border-radius:9px; background:#e53935; color:white; font:700 9px var(--font); box-shadow:0 0 0 2px #e5393520; }
    .user-admin-button { width:34px; min-width:34px; height:38px; padding:0; border-color:var(--line); background:var(--amber); font-size:13px; }
    .user-admin-button:hover { transform:none; box-shadow:none; }
    .user-empty { padding:16px 4px; color:var(--muted); text-align:center; font-size:11px; }
    .rules { border-top:1px solid var(--line); padding-top:16px; color:var(--muted); font:11px/1.8 var(--font); }
    .rules b { color:var(--ink); font-weight:400; }
    .chat { min-width:0; min-height:0; height:100%; overflow:hidden; background:var(--white); display:grid; grid-template-rows:76px minmax(0,1fr) 76px; }
    .chat-top { display:flex; justify-content:space-between; align-items:center; padding:0 26px; border-bottom:1px solid var(--line); }
    .chat-title { font-size:25px; }
    .mobile-channel-select { display:none; height:38px; max-width:150px; border:1px solid var(--ink); background:var(--white); padding:0 10px; color:var(--ink); font-family:var(--font); }
    .mobile-users-toggle, .mobile-users-close { display:none; }
    .chat-meta { display:flex; align-items:center; gap:18px; color:var(--muted); font:10px var(--font); }
    .chat-meta span { white-space:nowrap; }
    .chat-meta b { color:var(--ink); font-size:12px; }
    .messages { position:relative; padding:0; overflow:auto; scrollbar-color:#bdc7bf transparent; scrollbar-width:thin; background:linear-gradient(180deg,#ffffff 0%, #fbfaf6 100%); }
    .messages-spacer { position:relative; width:100%; }
    .messages-window { position:absolute; left:0; right:0; top:0; padding:24px 26px; display:flex; flex-direction:column; gap:16px; will-change:transform; }
    .empty { color:var(--muted); margin:auto; text-align:center; font-size:14px; line-height:1.8; padding:40px 20px; }
    .message { display:grid; grid-template-columns:38px minmax(0,1fr); grid-template-areas:'avatar meta' 'avatar bubble'; column-gap:12px; row-gap:4px; align-items:start; max-width:940px; width:100%; }
    .message-avatar { grid-area:avatar; width:38px; height:38px; display:grid; place-items:center; border:1px solid var(--line); background:#e7eee1; font-size:18px; user-select:none; border-radius:10px; }
    .message-meta { grid-area:meta; display:flex; align-items:baseline; gap:10px; }
    .message-name { font:700 11px var(--font); color:var(--coral); letter-spacing:1px; }
    .message-tag { font:10px var(--font); color:var(--muted); padding:1px 6px; border:1px dashed var(--line); border-radius:10px; }
    .message-bubble { position:relative; grid-area:bubble; padding:10px 14px 38px; border:1px solid var(--line); border-radius:14px; background:#f4f6f2; box-shadow:2px 3px 0 #dfe7de; font-size:16px; line-height:1.6; overflow-wrap:anywhere; white-space:pre-wrap; width:fit-content; max-width:50%; min-width:150px; }
    .message-text { display:block; }
    .message-file { min-width:230px; max-width:360px; display:grid; grid-template-columns:minmax(0,1fr) auto; grid-template-areas:'name download' 'meta download'; gap:1px 12px; align-items:center; white-space:normal; }
    .message-file[hidden] { display:none; }
    .file-name { grid-area:name; min-width:0; overflow:hidden; text-overflow:ellipsis; white-space:nowrap; font-size:14px; font-weight:700; }
    .file-meta { grid-area:meta; color:var(--muted); font-size:10px; }
    .file-download { grid-area:download; min-width:54px; height:32px; padding:0 10px; display:inline-flex; align-items:center; justify-content:center; border:1px solid var(--ink); border-radius:8px; background:var(--white); color:var(--ink); font:700 11px var(--font); text-decoration:none; }
    .file-download:hover { background:var(--dark); color:var(--white); }
    .message-footer { position:absolute; left:8px; right:8px; bottom:6px; display:flex; align-items:center; }
    .message-action { flex:1 1 0; width:auto; min-width:0; height:24px; padding:0; border:0; border-radius:6px; background:transparent; color:var(--muted); box-shadow:none; font:14px/1 var(--font); }
    .message-action:hover { transform:none; box-shadow:none; background:#dde4dc; color:var(--ink); }
    .message-action:disabled { visibility:hidden; }
    .message-footer .message-action[hidden] { display:block; visibility:hidden; }
    .message.recalled .message-bubble { background:#ecefeb; border-style:dashed; box-shadow:none; color:var(--muted); font-style:italic; }
    .message-time { flex:1 1 0; color:#718078; font:700 11px var(--font); line-height:24px; font-variant-numeric:tabular-nums; white-space:nowrap; text-align:center; }
    .message.self { grid-template-columns:minmax(0,1fr) 38px; grid-template-areas:'meta avatar' 'bubble avatar'; justify-items:end; margin-left:auto; }
    .message.self .message-meta { flex-direction:row-reverse; }
    .message.self .message-name { color:#2d6a4f; }
    .message.self .message-bubble { background:linear-gradient(180deg, var(--lime) 0%, #c9f23d 100%); border-color:#a8c93b; box-shadow:3px 4px 0 #1c251f; }
    .message.self .message-avatar { background:var(--amber); }
    .message.is-new .message-bubble { animation:rise .28s ease-out; }
    .composer { position:relative; z-index:5; overflow:visible; display:flex; align-items:stretch; gap:10px; padding:14px 26px; border-top:1px solid var(--line); background:#f7f8f4; }
    .emoji-wrap { position:relative; z-index:6; }
    .emoji-toggle { width:48px; height:48px; min-width:48px; flex:0 0 48px; padding:0; background:var(--white); font-size:20px; }
    .file-toggle { width:48px; height:48px; min-width:48px; flex:0 0 48px; padding:0; background:var(--white); font-size:18px; }
    .file-toggle[hidden] { display:none; }
    .file-input { display:none; }
    .emoji-panel { position:absolute; left:0; right:auto; bottom:54px; z-index:10; width:250px; height:238px; padding:12px; border:1px solid var(--ink); background:var(--white); box-shadow:5px 5px 0 var(--lime); display:grid; grid-template-rows:1fr 25px; gap:8px; }
    .emoji-panel[hidden] { display:none; }
    .emoji-grid { min-height:0; display:grid; grid-template-columns:repeat(6,1fr); grid-template-rows:repeat(4,1fr); gap:4px; }
    .emoji-option { min-width:0; min-height:0; height:auto; padding:0; border:0; background:transparent; font-size:20px; box-shadow:none; }
    .emoji-option:hover { transform:none; box-shadow:none; background:#eef1eb; }
    .emoji-pagination { display:flex; align-items:center; justify-content:space-between; gap:6px; }
    .emoji-page-button { width:30px; min-width:30px; height:25px; padding:0; border:1px solid var(--line); background:var(--paper); font-size:13px; }
    .emoji-page-button:disabled { opacity:.35; }
    .emoji-page-label { flex:1; text-align:center; color:var(--muted); font:10px var(--font); }
    input { flex:1; min-width:0; height:48px; border:1px solid #aab5ad; background:var(--white); padding:13px 15px; color:var(--ink); outline:none; }
    input:focus { border-color:var(--ink); box-shadow:3px 3px 0 var(--lime); }
    button { min-width:92px; height:48px; border:1px solid var(--ink); background:var(--lime); color:var(--ink); padding:0 18px; cursor:pointer; font:700 12px var(--font); transition:transform .15s, box-shadow .15s; }
    button:hover { transform:translate(-2px,-2px); box-shadow:4px 4px 0 var(--ink); }
    button:disabled { opacity:.5; cursor:not-allowed; transform:none; box-shadow:none; }
    .room-panel { min-width:0; min-height:0; overflow-y:auto; padding:28px 20px; background:var(--paper); border-left:1px solid var(--line); display:flex; flex-direction:column; gap:22px; }
    .room-panel h2 { margin:0; font:700 11px var(--font); letter-spacing:2px; }
    .channel-list { display:flex; flex-direction:column; gap:7px; }
    .channel-button { width:100%; height:44px; min-width:0; padding:0 10px; display:flex; align-items:center; justify-content:space-between; border-color:var(--line); background:transparent; font-family:var(--font); font-weight:400; }
    .channel-button:hover { transform:none; box-shadow:none; border-color:var(--ink); }
    .channel-button.active { background:var(--dark); color:var(--white); border-color:var(--dark); }
    .channel-count { min-width:24px; text-align:right; color:var(--muted); }
    .channel-button.active .channel-count { color:var(--lime); }
    .room-admin-entry { margin-top:auto; display:flex; flex-direction:column; gap:10px; }
    .admin-status { font:11px/1.6 var(--font); color:var(--muted); }
    .admin-status b { color:#2d6a4f; }
    .fab-admin { position:fixed; right:20px; bottom:20px; z-index:9; min-width:120px; height:42px; background:var(--amber); box-shadow:5px 5px 0 var(--ink); border-radius:21px; display:none; }
    .fab-admin:not([hidden]) { display:inline-flex; align-items:center; justify-content:center; gap:6px; }
    .fab-admin::before { content:''; display:inline-block; width:8px; height:8px; border-radius:50%; background:var(--coral); }
    .fab-admin.verified::before { background:#2d6a4f; }
    .modal-backdrop { position:fixed; inset:0; z-index:20; display:grid; place-items:center; padding:20px; background:#17211bcc; backdrop-filter:blur(2px); }
    .modal-backdrop[hidden] { display:none; }
    .modal { width:min(460px,100%); padding:22px; border:1px solid var(--ink); background:var(--white); box-shadow:7px 7px 0 var(--lime); }
    .modal h2 { margin:0 0 18px; font-size:22px; font-weight:400; }
    .modal input { width:100%; margin-bottom:12px; }
    .modal-actions { display:flex; justify-content:flex-end; gap:8px; }
    .modal-actions button { height:40px; }
    .admin-channels { display:flex; flex-direction:column; gap:10px; margin-bottom:18px; }
    .admin-channel-row { display:grid; grid-template-columns:75px 1fr 60px; gap:8px; align-items:center; font-size:13px; }
    .admin-channel-row input { height:38px; margin:0; }
    .admin-channel-row button { min-width:0; height:38px; padding:0 8px; }
    .admin-ban-tools { border-top:1px solid var(--line); padding-top:16px; margin-top:4px; }
    .admin-ban-tools h3 { margin:0 0 10px; font:700 11px var(--font); letter-spacing:1.5px; }
    .admin-ban-entry { display:grid; grid-template-columns:minmax(0,1fr) 72px; gap:8px; }
    .admin-ban-entry input, .admin-ban-entry button { height:40px; margin:0; }
    .admin-ban-entry button { min-width:0; padding:0 8px; }
    .banned-list { max-height:126px; overflow:auto; margin-top:10px; display:flex; flex-direction:column; gap:5px; }
    .banned-row { display:grid; grid-template-columns:minmax(0,1fr) 60px; gap:8px; align-items:center; font:12px var(--font); }
    .banned-row button { min-width:0; height:32px; padding:0 6px; background:var(--paper); }
    .banned-empty { color:var(--muted); font-size:11px; padding:5px 0; }
    .user-detail { color:var(--muted); font:14px/1.8 var(--font); }
    .user-detail b { color:var(--ink); font-weight:400; }
    .metric { padding:18px 0; border-top:1px solid #cbd3cc; }
    .metric-label { display:block; margin-bottom:8px; color:var(--muted); font:10px var(--font); }
    .metric-value { font-size:29px; line-height:1; }
    .online-value::before { content:''; display:inline-block; width:8px; height:8px; margin-right:9px; border-radius:50%; background:#51ad72; vertical-align:4px; }
    .time-value { color:var(--ink); font-family:var(--font); font-weight:400; font-variant-numeric:tabular-nums; letter-spacing:0; }
    .chat-meta .time-value { font-size:12px; line-height:1; vertical-align:baseline; }
    .sync { color:var(--muted); font:10px/1.7 var(--font); }
    .sync::before { content:'SYNC STATUS'; display:block; color:var(--ink); margin-bottom:7px; }
    .blocker { position:fixed; inset:0; z-index:30; display:grid; place-items:center; background:#17211bf0; color:var(--white); }
    .blocker[hidden] { display:none; }
    .blocker-card { width:min(520px,92vw); padding:28px; border:1px solid var(--lime); background:#111915; box-shadow:8px 8px 0 #000; }
    .blocker-card h2 { margin:0 0 12px; font-size:26px; color:var(--lime); letter-spacing:1px; }
    .blocker-card p { margin:0 0 18px; color:#cfd7d1; line-height:1.75; font-family:var(--font); font-size:15px; }
    .blocker-meta { display:flex; justify-content:space-between; color:#8a9891; font:12px var(--font); margin-top:18px; }
    .toast-host { position:fixed; z-index:60; top:20px; left:50%; width:min(420px,calc(100vw - 32px)); transform:translateX(-50%); display:flex; justify-content:center; pointer-events:none; }
    .toast-message { --toast-color:#4f718c; width:max-content; max-width:100%; min-width:280px; min-height:44px; padding:10px 16px; display:flex; align-items:center; justify-content:center; gap:10px; border:1px solid #d8dee4; border-radius:8px; background:#fff; color:#44515b; box-shadow:0 6px 22px #17211b24; font:13px/1.5 var(--font); opacity:0; transform:translateY(-14px); transition:opacity .18s ease,transform .18s ease; }
    .toast-message.visible { opacity:1; transform:translateY(0); }
    .toast-message.success { --toast-color:#4d9b69; border-color:#c9e7d3; background:#f1faf4; color:#356d49; }
    .toast-message.warning { --toast-color:#d49632; border-color:#f0d7ad; background:#fff8eb; color:#94651f; }
    .toast-message.error { --toast-color:#d95b57; border-color:#efc5c3; background:#fff2f1; color:#a5423e; }
    .toast-icon { width:18px; height:18px; flex:0 0 18px; display:grid; place-items:center; border:1px solid currentColor; border-radius:50%; color:var(--toast-color); font:700 11px/1 var(--font); }
    .toast-text { min-width:0; overflow-wrap:anywhere; }
    @keyframes rise { from { opacity:0; transform:translateY(6px); } to { opacity:1; transform:none; } }
    @media (max-width:1000px) { main { grid-template-columns:220px minmax(0,1fr); } .room-panel { display:none; } .mobile-channel-select { display:block; } .chat-title { display:none; } }
    @media (max-width:700px) { body { overflow:hidden; } .shell { height:100vh; height:100dvh; min-height:0; grid-template-rows:56px minmax(0,1fr); } header { padding:0 16px; } main { height:100%; min-height:0; overflow:hidden; display:grid; grid-template-columns:1fr; grid-template-rows:auto minmax(0,1fr); } .profile-panel { overflow:hidden; padding:12px 16px; border-right:0; border-bottom:1px solid var(--line); display:grid; grid-template-columns:minmax(0,1fr) auto; gap:12px; align-items:center; } .profile-panel > div:first-child, .user-directory, .rules { display:none; } .identity { width:min(100%,280px); padding:8px 10px; grid-template-columns:42px minmax(0,1fr); box-shadow:3px 3px 0 var(--lime); } .avatar { width:42px; height:42px; font-size:22px; } .chat { height:100%; min-height:0; grid-template-rows:60px minmax(0,1fr) 70px; } .chat-top, .messages-window { padding-left:16px; padding-right:16px; } .composer { padding:12px 16px; } button { min-width:70px; padding:0 12px; } .emoji-toggle, .file-toggle { width:48px; min-width:48px; flex-basis:48px; padding:0; } .mobile-channel-select { max-width:120px; } .chat-meta { gap:9px; } .chat-meta span:first-child { display:none; } .message-bubble { width:100%; } .message-file { min-width:0; width:100%; } .emoji-panel { left:-8px; right:auto; bottom:52px; } .toast-host { top:12px; } .toast-message { min-width:0; width:100%; } .fab-admin { right:14px; bottom:14px; min-width:108px; height:40px; } }
    @media (max-width:700px) {
      .chat-top { gap:8px; }
      .mobile-channel-select { flex:1 1 auto; min-width:0; max-width:none; }
      .mobile-users-toggle { position:relative; flex:0 0 auto; min-width:64px; height:38px; padding:0 10px; display:inline-flex; align-items:center; justify-content:center; gap:5px; background:var(--white); }
      .mobile-unread-count { min-width:17px; height:17px; padding:0 4px; display:grid; place-items:center; border-radius:9px; background:#e53935; color:#fff; font:700 9px var(--font); }
      .mobile-unread-count[hidden] { display:none; }
      .chat-meta { flex:0 0 auto; }
      .chat-meta span:last-child { display:none; }
      body.mobile-users-open .profile-panel { position:fixed; z-index:18; inset:56px 0 0; width:100%; min-height:0; padding:16px; overflow:hidden; display:flex; flex-direction:column; align-items:stretch; gap:14px; border:0; background:#f7f8f4; }
      body.mobile-users-open .profile-panel .mobile-users-close { width:100%; height:40px; min-height:40px; flex:none; display:block; background:var(--dark); color:var(--white); }
      body.mobile-users-open .profile-panel .identity { width:100%; max-width:none; flex:none; }
      body.mobile-users-open .profile-panel .user-directory { width:100%; min-height:0; flex:1 1 0; display:flex; }
      body.mobile-users-open .profile-panel .user-list { padding-bottom:10px; }
      body.mobile-users-open .profile-panel .user-row { height:44px; }
    }
  </style>
</head>
<body>
  <div class="shell">
    <header><div class="brand"><i class="mark"></i> VOID / CHAT</div><div class="status"><i class="pulse"></i><span id="connection">正在连接</span></div></header>
    <main>
      <aside class="profile-panel">
        <div><div class="kicker" id="kicker">LOCAL / 001</div><h1>没有名字<br>也能说话。</h1><div class="intro">同一网络里的临时房间。没有账号，没有档案，只有此刻。</div></div>
        <button class="mobile-users-close" id="mobile-users-close" type="button">返回聊天</button>
        <div class="identity"><div class="avatar" id="my-avatar">?</div><div><small>你是</small><input id="my-name" maxlength="5" value="匿名访客" aria-label="编辑用户名"></div></div>
        <div class="user-directory"><div class="user-directory-head"><span>ONLINE USERS</span><span id="user-count">0</span></div><input class="user-search" id="user-search" type="search" placeholder="搜索用户名" aria-label="搜索在线用户"><div class="user-list" id="user-list"></div></div>
      </aside>
      <section class="chat"><div class="chat-top"><div class="chat-title" id="channel-title">唠嗑</div><select class="mobile-channel-select" id="mobile-channel-select" aria-label="切换频道"></select><button class="mobile-users-toggle" id="mobile-users-toggle" type="button" aria-label="查看在线用户" aria-expanded="false">用户 <span class="mobile-unread-count" id="mobile-unread-count" hidden></span></button><div class="chat-meta"><span id="channel-code">CHANNEL / 01</span><span><span id="scope-label">本频道</span> <b id="online">0</b></span><span>全站 <b id="total-online-inline">0</b>/100</span></div></div><div class="messages" id="messages"><div class="messages-spacer" id="messages-spacer"><div class="messages-window" id="messages-window"></div></div></div><form class="composer" id="composer"><div class="emoji-wrap"><button class="emoji-toggle" id="emoji-toggle" type="button" aria-label="打开表情面板">☺</button><div class="emoji-panel" id="emoji-panel" hidden></div></div><button class="file-toggle" id="file-toggle" type="button" title="发送文件（最大 1 MB，5 分钟后销毁）" aria-label="选择私聊文件" hidden>📎</button><input class="file-input" id="file-input" type="file" tabindex="-1"><input id="message" maxlength="500" autocomplete="off" placeholder="说点什么……"><button id="send" type="submit">发送 ↗</button></form></section>
      <aside class="room-panel"><h2>CHANNELS</h2><div class="channel-list" id="channel-list"></div><div class="metric"><span class="metric-label">全站在线</span><div class="metric-value"><span id="total-online">0</span> / 100</div></div><div class="rules"><b>ROOM PROTOCOL</b><br><b>消息与文件仅保留 5 分钟</b><br>发送后 3 分钟内可以撤回<br>文件仅限在线私聊，最大 1 MB<br>每 5 秒只能发送 2 条消息</div><div class="room-admin-entry"><div class="admin-status" id="admin-status" hidden></div><div class="sync" id="refresh">等待同步</div></div></aside>
    </main>
  </div>
  <div class="toast-host" id="toast-host" aria-live="polite" aria-atomic="true"></div>
  <button class="fab-admin" id="fab-admin" type="button" hidden>验证管理员</button>
  <div class="modal-backdrop" id="admin-modal" hidden><div class="modal"><h2 id="admin-modal-title">验证管理员</h2><div id="admin-login"><input id="admin-password" type="password" inputmode="numeric" placeholder="输入管理员密码"><div class="modal-actions"><button type="button" data-close="admin-modal">取消</button><button type="button" id="admin-login-button">验证</button></div></div><div id="admin-tools" hidden><div class="admin-channels" id="admin-channels"></div><div class="admin-ban-tools"><h3>IP 封禁管理</h3><div class="admin-ban-entry"><input id="admin-ban-ip" placeholder="输入 IP 地址" aria-label="要封禁的 IP 地址"><button type="button" id="admin-ban-button">封禁</button></div><div class="banned-list" id="banned-list"></div></div><div class="modal-actions"><button type="button" data-close="admin-modal">完成</button></div></div></div></div>
  <div class="modal-backdrop" id="user-modal" hidden><div class="modal"><h2>用户信息</h2><div class="user-detail" id="user-detail">正在读取</div><div class="modal-actions"><button type="button" data-close="user-modal">关闭</button></div></div></div>
  <div class="blocker" id="blocker" hidden><div class="blocker-card"><h2 id="blocker-title">ROOM IS FULL</h2><p id="blocker-message">当前聊天室同时在线已满，新的连接暂时无法进入。请稍后刷新再试，或等待现有连接超时释放。</p><div class="blocker-meta"><span id="blocker-meta-limit">LIMIT 100</span><span id="blocker-retry">RETRY IN 5s</span></div></div></div>
  <script>
    const names = ['雾中信号','午夜电台','路过的人','蓝色回声','未读消息','七号窗口','风的背面','纸上月光','无名之声','半格电量','雨后电台','凌晨三点','玻璃海岸','远方来客','静默频道','白噪音','南墙以北','小行星带','旧磁带','临时月亮','低空飞行','纸船渡口','橘色回声','没有署名','第九街角','慢速星球','失眠旅人','空白信笺','北纬三十','候车室里','微光入口','借过一下','晴天留声机','倒带之前','未完句号','晚风收件箱','路灯下面','隐身模式','落日存档','匿名观测员','月面漫步者','雨伞借我','发呆俱乐部','半夜醒来','蓝调星期五','海边的字','轻声路过','没有目的地','风筝线外','借来的名字'];
    const faces = ['◒','◓','◐','◑','✦','⊙','◇','△','□','○'];
    const identity = { name:names[Math.floor(Math.random()*names.length)], avatar:faces[Math.floor(Math.random()*faces.length)], id:crypto.randomUUID ? crypto.randomUUID() : Math.random().toString(36).slice(2) };
    const state = { messages:[], users:[], privateUnread:{}, privateActivity:{}, online:0, cursor:0, polling:false, uploading:false, nameEdited:false, mode:'channel', peer:null, channel:'channel1', channels:[], onlineByChannel:{}, adminToken:'', full:false, blockedReason:'', sendCooldownUntil:0, retentionMs:300000, recallWindowMs:180000, maxFileBytes:1048576, renderBatch:100, pollInterval:1500, blockRetry:5000, canAdmin:false, scrollLocked:true };
    const $ = id => document.getElementById(id);
    let toastTimer=0;
    function showToast(message,type='info') {
      const host=$('toast-host');
      clearTimeout(toastTimer); host.replaceChildren();
      const toast=document.createElement('div'); toast.className='toast-message '+type; toast.setAttribute('role',type==='error'?'alert':'status');
      const icon=document.createElement('span'); icon.className='toast-icon'; icon.textContent=({success:'✓',warning:'!',error:'×',info:'i'})[type]||'i';
      const text=document.createElement('span'); text.className='toast-text'; text.textContent=String(message||'');
      toast.append(icon,text); host.append(toast); requestAnimationFrame(()=>toast.classList.add('visible'));
      toastTimer=setTimeout(()=>{ toast.classList.remove('visible'); setTimeout(()=>{ if(toast.parentNode===host) toast.remove(); },180); },2000);
    }
    function setMobileUsersOpen(open) {
      document.body.classList.toggle('mobile-users-open',!!open);
      $('mobile-users-toggle').setAttribute('aria-expanded',open?'true':'false');
    }
    const emojis = [
      '😀','😃','😄','😁','😆','😅','🤣','😂','🙂','🙃','😉','😊',
      '😇','🥰','😍','🤩','😘','😎','🤔','🫡','🤗','🥳','😴','🤤',
      '😮','😱','😢','😭','😠','😡','🤬','😤','🤯','😳','🥺','😶',
      '🙄','😏','🤪','😜','🤡','💀','👻','👽','🤖','😈','👿','🙌',
      '👏','👍','👎','👌','✌️','🤞','🤟','🤘','👊','✊','🤝','🙏',
      '💪','👋','🤚','🖐️','✋','🫶','💅','👀','🧠','🫀','🗣️','👤',
      '❤️','🧡','💛','💚','💙','💜','🖤','🤍','🤎','💔','💕','💯',
      '✨','⭐','🌟','🔥','🎉','🎊','✅','❌','⚡','💡','🎈','🎁',
      '🍎','🍕','🍔','🍟','🍰','🍩','☕','🍺','🥤','🍉','🍓','🍒',
      '🌞','🌙','☁️','🌈','🌸','🌻','🌲','🌊','❄️','🌍','🌵','🍀',
      '🐶','🐱','🐭','🐼','🦊','🐸','🐵','🦄','🐝','🦋','🐧','🐯',
      '🚀','✈️','🚗','🚲','⏰','📌','📎','✏️','📚','🎵','🎮','🏆'
    ];
    const emojiGrid = document.createElement('div');
    emojiGrid.className = 'emoji-grid';
    const emojiPagination = document.createElement('div');
    emojiPagination.className = 'emoji-pagination';
    const previousEmojiPage = document.createElement('button');
    previousEmojiPage.className = 'emoji-page-button';
    previousEmojiPage.type = 'button';
    previousEmojiPage.textContent = '‹';
    const emojiPageLabel = document.createElement('span');
    emojiPageLabel.className = 'emoji-page-label';
    const nextEmojiPage = document.createElement('button');
    nextEmojiPage.className = 'emoji-page-button';
    nextEmojiPage.type = 'button';
    nextEmojiPage.textContent = '›';
    emojiPagination.append(previousEmojiPage, emojiPageLabel, nextEmojiPage);
    $('emoji-panel').append(emojiGrid, emojiPagination);
    const emojiPageSize = 24;
    let emojiPage = 0;
    function renderEmojiPage() {
      emojiGrid.replaceChildren();
      emojis.slice(emojiPage * emojiPageSize, (emojiPage + 1) * emojiPageSize).forEach(emoji => {
      const button = document.createElement('button');
      button.className = 'emoji-option';
      button.type = 'button';
      button.textContent = emoji;
      button.setAttribute('aria-label', '插入表情 ' + emoji);
      emojiGrid.append(button);
      button.addEventListener('click', () => { const input=$('message'); const start=input.selectionStart; input.value=input.value.slice(0,start)+button.textContent+input.value.slice(input.selectionEnd); input.focus(); input.selectionStart=input.selectionEnd=start+button.textContent.length; $('emoji-panel').hidden=true; });
      });
      const pageCount=Math.ceil(emojis.length/emojiPageSize); emojiPageLabel.textContent=(emojiPage+1)+' / '+pageCount; previousEmojiPage.disabled=emojiPage===0; nextEmojiPage.disabled=emojiPage===pageCount-1;
    }
    previousEmojiPage.addEventListener('click', () => { if(emojiPage>0) { emojiPage--; renderEmojiPage(); } });
    nextEmojiPage.addEventListener('click', () => { if(emojiPage<Math.ceil(emojis.length/emojiPageSize)-1) { emojiPage++; renderEmojiPage(); } });
    renderEmojiPage();
    $('my-name').value = identity.name; $('my-avatar').textContent = identity.avatar;
    const apiBase = location.protocol === 'file:' ? 'http://localhost:9000' : '';
    const DEFAULT_ROW = 80;
    const ROW_GAP = 16;
    const BLOCK_PADDING = 48;
    const OVERSCAN = 6;
    const vlist = {
      nodeMap: new Map(),
      heights: new Map(),
      prefixSum: [0],
      lastStart: -1,
      lastEnd: -1,
      lastChannel: null
    };
    function resetVlist() {
      vlist.nodeMap.forEach(node => node.remove());
      vlist.nodeMap.clear();
      vlist.heights.clear();
      vlist.prefixSum = [0];
      vlist.lastStart = -1;
      vlist.lastEnd = -1;
      vlist.lastChannel = state.channel;
    }
    function syncPrefix() {
      const arr = state.messages;
      if (vlist.lastChannel !== state.channel) { resetVlist(); }
      if (vlist.prefixSum.length !== arr.length + 1) vlist.prefixSum = new Array(arr.length + 1).fill(0);
      for (let i = 0; i < arr.length; i++) {
        const h = (vlist.heights.get(arr[i].id) ?? DEFAULT_ROW) + ROW_GAP;
        vlist.prefixSum[i + 1] = vlist.prefixSum[i] + h;
      }
    }
    function findSlice(viewportTop, viewportBottom) {
      const sums = vlist.prefixSum;
      let start = 0;
      let end = state.messages.length;
      for (let i = 0; i < sums.length - 1; i++) {
        if (sums[i + 1] < viewportTop - 160) start = i + 1;
        if (sums[i] > viewportBottom + 160) { end = i + OVERSCAN; break; }
      }
      start = Math.max(0, start - OVERSCAN);
      end = Math.min(state.messages.length, end);
      return [start, end];
    }
    async function copyMessageText(text, button) {
      try {
        if(navigator.clipboard && window.isSecureContext) await navigator.clipboard.writeText(text);
        else {
          const area=document.createElement('textarea');
          area.value=text; area.style.position='fixed'; area.style.opacity='0';
          document.body.append(area); area.select(); document.execCommand('copy'); area.remove();
        }
        const original=button.textContent; button.textContent='✓'; setTimeout(()=>button.textContent=original,900);
        showToast('消息内容已复制','success');
      } catch { button.textContent='×'; setTimeout(()=>button.textContent='⧉',900); showToast('复制失败，请重试','error'); }
    }
    async function recallMessage(messageId, button) {
      button.disabled=true;
      try {
        const response=await fetch(apiBase+'/api/message/recall',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({id:identity.id,messageId})});
        const data=await response.json().catch(()=>({}));
        if(!response.ok) throw Error(data.error||'recall failed');
        const index=state.messages.findIndex(message=>message.id===messageId);
        if(index!==-1) state.messages[index]=data.message;
        const oldNode=vlist.nodeMap.get(messageId); if(oldNode) oldNode.remove(); vlist.nodeMap.delete(messageId);
        render({force:true});
        showToast('消息已撤回','success');
      } catch(error) {
        button.disabled=false;
        button.textContent=error.message==='recall expired'?'超时':'!';
        setTimeout(()=>button.textContent='↶',1000);
        showToast(error.message==='recall expired'?'已超过 3 分钟，无法撤回':'撤回失败，请重试',error.message==='recall expired'?'warning':'error');
      }
    }
    function createRow(m, isNew) {
      const self = m.senderId === identity.id;
      const row = document.createElement('div');
      row.className = 'message' + (self ? ' self' : '') + (isNew ? ' is-new' : '') + (m.recalled ? ' recalled' : '');
      row.dataset.id = m.id;
      row.dataset.sender = m.senderId || '';
      row.dataset.at = String(m.at);
      row.dataset.expiresAt = String(m.at + state.retentionMs);
      row.innerHTML = '<div class="message-avatar"></div><div class="message-meta"><div class="message-name"></div><div class="message-tag" hidden></div></div><div class="message-bubble"><span class="message-text"></span><div class="message-file" hidden><div class="file-name"></div><div class="file-meta"></div><a class="file-download">下载</a></div><div class="message-footer"><button class="message-action copy-action" type="button" title="复制消息" aria-label="复制消息">⧉</button><time class="message-time"></time><button class="message-action recall-action" type="button" title="撤回消息" aria-label="撤回消息">↶</button></div></div>';
      row.querySelector('.message-avatar').textContent = m.avatar;
      row.querySelector('.message-name').textContent = m.name;
      const textNode=row.querySelector('.message-text');
      textNode.textContent = m.recalled ? '该消息已撤回' : m.text;
      const fileCard=row.querySelector('.message-file');
      if(m.file&&!m.recalled) {
        textNode.hidden=true; fileCard.hidden=false;
        row.querySelector('.file-name').textContent=m.file.name;
        row.querySelector('.file-meta').textContent=formatFileSize(m.file.size)+' · 5 分钟后销毁';
        const download=row.querySelector('.file-download');
        download.href=apiBase+'/api/file/'+encodeURIComponent(m.file.id)+'?client='+encodeURIComponent(identity.id)+'&token='+encodeURIComponent(m.file.token);
        download.download=m.file.name; download.title='下载 '+m.file.name;
      }
      const tag = row.querySelector('.message-tag');
      if (self) { tag.hidden = false; tag.textContent = '我'; }
      const copyButton=row.querySelector('.copy-action');
      const recallButton=row.querySelector('.recall-action');
      copyButton.hidden=!!m.recalled||!m.text;
      recallButton.hidden=!self||!!m.recalled||Date.now()-m.at>state.recallWindowMs;
      if(m.text) copyButton.addEventListener('click',()=>copyMessageText(m.text,copyButton));
      recallButton.addEventListener('click',()=>recallMessage(m.id,recallButton));
      updateMessageCountdown(row, m.at);
      return row;
    }
    function formatFileSize(bytes) { return bytes<1024?bytes+' B':(bytes/1024).toFixed(bytes<10240?1:0)+' KB'; }
    function formatRemaining(ms) {
      const seconds = Math.max(0, Math.ceil(ms / 1000));
      return String(Math.floor(seconds / 60)).padStart(2, '0') + ':' + String(seconds % 60).padStart(2, '0');
    }
    function updateMessageCountdown(row, at) {
      row.querySelector('.message-time').textContent = '剩余 ' + formatRemaining(at + state.retentionMs - Date.now());
    }
    function measureInserted(ids) {
      ids.forEach(id => {
        const node = vlist.nodeMap.get(id);
        if (!node) return;
        const h = node.getBoundingClientRect().height;
        if (h && h !== vlist.heights.get(id)) vlist.heights.set(id, h);
      });
    }
    function render(options = {}) {
      const root = $('messages');
      const spacer = $('messages-spacer');
      const win = $('messages-window');
      if (!state.messages.length) {
        resetVlist();
        spacer.style.height = 'auto';
        win.style.transform = 'translateY(0px)';
        win.innerHTML = state.mode==='private'?'<div class="empty">还没有私聊消息。<br>发一句问候开始吧。</div>':'<div class="empty">房间是安静的。<br>发一条消息开始吧。</div>';
        return;
      }
      syncPrefix();
      const total = vlist.prefixSum[vlist.prefixSum.length - 1] + BLOCK_PADDING;
      spacer.style.height = total + 'px';
      const [startIndex, endIndex] = findSlice(root.scrollTop, root.scrollTop + root.clientHeight);
      const offsetTop = vlist.prefixSum[startIndex];
      win.style.transform = 'translateY(' + offsetTop + 'px)';
      if (startIndex === vlist.lastStart && endIndex === vlist.lastEnd && !options.force && !options.scrollToBottom) {
        measureInserted(collectVisibleIds(startIndex, endIndex));
        return;
      }
      vlist.lastStart = startIndex;
      vlist.lastEnd = endIndex;
      const wanted = new Set();
      const freshIds = new Set(options.newIds || []);
      for (let i = startIndex; i < endIndex; i++) {
        const m = state.messages[i];
        wanted.add(m.id);
        if (!vlist.nodeMap.has(m.id)) vlist.nodeMap.set(m.id, createRow(m, freshIds.has(m.id)));
      }
      for (const [id, node] of Array.from(vlist.nodeMap)) {
        if (!wanted.has(id)) { vlist.nodeMap.delete(id); node.remove(); }
      }
      const frag = document.createDocumentFragment();
      for (let i = startIndex; i < endIndex; i++) frag.appendChild(vlist.nodeMap.get(state.messages[i].id));
      win.replaceChildren(frag);
      requestAnimationFrame(() => {
        measureInserted(collectVisibleIds(startIndex, endIndex));
        if (vlist.lastStart !== startIndex || vlist.lastEnd !== endIndex) return;
        syncPrefix();
        spacer.style.height = (vlist.prefixSum[vlist.prefixSum.length - 1] + BLOCK_PADDING) + 'px';
        if (state.scrollLocked || options.scrollToBottom) root.scrollTop = root.scrollHeight;
        if (freshIds.size) setTimeout(() => freshIds.forEach(id => { vlist.nodeMap.get(id)?.classList.remove('is-new'); }), 350);
      });
    }
    function collectVisibleIds(start, end) {
      const out = [];
      for (let i = start; i < end; i++) out.push(state.messages[i].id);
      return out;
    }
    function updateComposerControls() {
      const cooling=Date.now()<state.sendCooldownUntil;
      const peerOffline=state.mode==='private'&&state.peer?.online===false;
      const privateMode=state.mode==='private'&&!!state.peer;
      $('send').disabled=state.full||state.uploading||cooling||peerOffline;
      $('file-toggle').hidden=!privateMode;
      $('file-toggle').disabled=state.full||state.uploading||cooling;
      $('file-toggle').title=peerOffline?'对方已离线':state.uploading?'正在上传文件':'发送文件（最大 1 MB，5 分钟后销毁）';
      $('file-toggle').textContent=state.uploading?'…':'📎';
    }
    function renderChannels() {
      const root=$('channel-list');
      const fragment=document.createDocumentFragment();
      const selectFragment=document.createDocumentFragment();
      if(state.mode==='private'&&state.peer) {
        const privateOption=document.createElement('option'); privateOption.value='__private__'; privateOption.textContent='私聊 · '+state.peer.name; selectFragment.append(privateOption);
      }
      state.channels.forEach(channel => {
        const button=document.createElement('button');
        button.type='button';
        button.className='channel-button'+(state.mode==='channel'&&channel.id===state.channel?' active':'');
        button.innerHTML='<span></span><span class="channel-count"></span>';
        button.querySelector('span').textContent=channel.name;
        button.querySelector('.channel-count').textContent=state.onlineByChannel[channel.id]||0;
        button.addEventListener('click',()=>switchChannel(channel.id));
        fragment.append(button);
        const option=document.createElement('option');
        option.value=channel.id;
        option.textContent=channel.name+' · '+(state.onlineByChannel[channel.id]||0)+' 人';
        selectFragment.append(option);
      });
      root.replaceChildren(fragment);
      $('mobile-channel-select').replaceChildren(selectFragment);
      $('mobile-channel-select').value=state.mode==='private'?'__private__':state.channel;
      const current=state.channels.find(channel=>channel.id===state.channel);
      if(state.mode==='private'&&state.peer) {
        $('kicker').textContent='PRIVATE / 1:1';
        $('channel-title').textContent='与 '+state.peer.name+' 私聊';
        $('channel-code').textContent='PRIVATE / 1:1';
        $('scope-label').textContent='对方';
        $('online').textContent=state.peer.online===false?'离线':'在线';
        $('message').placeholder=state.peer.online===false?'对方已离线':'私下说点什么……';
        if(state.peer.online===false) $('send').disabled=true;
        else if(!state.full&&Date.now()>=state.sendCooldownUntil) $('send').disabled=false;
      } else if(current) {
        const idx = state.channels.indexOf(current)+1;
        $('kicker').textContent = 'LOCAL / ' + String(idx).padStart(3,'0');
        $('channel-title').textContent=current.name;
        $('channel-code').textContent='CHANNEL / '+String(idx).padStart(2,'0');
        $('scope-label').textContent='本频道';
        $('online').textContent=state.onlineByChannel[state.channel]||0;
        $('message').placeholder='说点什么……';
        if(!state.full&&Date.now()>=state.sendCooldownUntil) $('send').disabled=false;
      }
      $('total-online').textContent=state.online;
      $('total-online-inline').textContent=state.online;
      updateComposerControls();
    }
    function renderUsers() {
      const root=$('user-list');
      const query=$('user-search').value.trim().toLocaleLowerCase('zh-CN');
      const unreadTotal=state.users.reduce((total,user)=>total+(user.id===identity.id?0:(state.privateUnread[user.id]||0)),0);
      const mobileUnread=$('mobile-unread-count'); mobileUnread.hidden=!unreadTotal; mobileUnread.textContent=unreadTotal>99?'99+':String(unreadTotal);
      const filtered=state.users.filter(user=>user.name.toLocaleLowerCase('zh-CN').includes(query)).sort((first,second)=>{
        const firstUnread=(state.privateUnread[first.id]||0)>0;
        const secondUnread=(state.privateUnread[second.id]||0)>0;
        if(firstUnread!==secondUnread) return secondUnread-firstUnread;
        const firstActive=state.mode==='private'&&state.peer?.id===first.id;
        const secondActive=state.mode==='private'&&state.peer?.id===second.id;
        if(firstActive!==secondActive) return secondActive-firstActive;
        const activityDifference=(state.privateActivity[second.id]||0)-(state.privateActivity[first.id]||0);
        return activityDifference||first.name.localeCompare(second.name,'zh-CN');
      });
      $('user-count').textContent=query?filtered.length+'/'+state.users.length:state.users.length;
      if(!filtered.length) {
        const empty=document.createElement('div'); empty.className='user-empty'; empty.textContent=query?'没有匹配的在线用户':'暂无在线用户';
        root.replaceChildren(empty); return;
      }
      const fragment=document.createDocumentFragment();
      filtered.forEach(user=>{
        const entry=document.createElement('div'); entry.className='user-entry';
        const button=document.createElement('button'); button.type='button'; button.className='user-row'+(user.id===identity.id?' self':'')+(state.mode==='private'&&state.peer?.id===user.id?' active':'');
        const avatar=document.createElement('span'); avatar.className='user-row-avatar'; avatar.textContent=user.avatar;
        const name=document.createElement('span'); name.className='user-row-name'; name.textContent=user.name+(user.id===identity.id?'（我）':'');
        const channel=document.createElement('span'); channel.className='user-row-channel';
        const channelInfo=state.channels.find(item=>item.id===user.channel); channel.textContent=channelInfo?channelInfo.name:user.channel;
        button.append(avatar,name,channel);
        const unread=state.privateUnread[user.id]||0;
        if(unread) { const dot=document.createElement('span'); dot.className='unread-dot'; dot.textContent=unread>99?'99+':String(unread); button.append(dot); }
        if(user.id!==identity.id) button.addEventListener('click',()=>switchPrivate(user));
        entry.append(button);
        if(state.adminToken) {
          const admin=document.createElement('button'); admin.type='button'; admin.className='user-admin-button'; admin.textContent='⚙'; admin.title='查看用户信息'; admin.setAttribute('aria-label','管理 '+user.name);
          admin.addEventListener('click',()=>openUserDetails(user.id)); entry.append(admin);
        }
        fragment.append(entry);
      });
      root.replaceChildren(fragment);
    }
    async function openUserDetails(clientId) {
      const modal=$('user-modal'); const detail=$('user-detail');
      modal.hidden=false; detail.textContent='正在读取';
      const response=await fetch(apiBase+'/api/admin/user?client='+encodeURIComponent(clientId),{headers:{'X-Admin-Token':state.adminToken}});
      const data=await response.json().catch(()=>({}));
      if(!response.ok) { detail.textContent=data.error==='offline'?'该用户已经离线':'读取失败'; return; }
      const channel=state.channels.find(item=>item.id===data.channel);
      detail.replaceChildren();
      [['用户名',data.name],['IP 地址',data.ip],['所在频道',channel?channel.name:data.channel],['最后在线',new Date(data.lastSeen).toLocaleString()]].forEach(([label,value])=>{
        const line=document.createElement('div'); const strong=document.createElement('b'); strong.textContent=label+'：'; line.append(strong,document.createTextNode(String(value))); detail.append(line);
      });
      const ban=document.createElement('button'); ban.type='button'; ban.style.marginTop='14px'; ban.textContent=data.banned?'解除 IP 封禁':'封禁此 IP';
      ban.addEventListener('click',async()=>{ ban.disabled=true; const ok=await setIpBan(data.ip,!data.banned); if(ok) modal.hidden=true; else ban.disabled=false; });
      detail.append(ban);
    }
    function switchChannel(channel) {
      if((state.mode==='channel'&&channel===state.channel)||!state.channels.some(item=>item.id===channel)) return;
      setMobileUsersOpen(false);
      state.mode='channel';
      state.peer=null;
      state.channel=channel;
      state.cursor=0;
      state.messages=[];
      state.scrollLocked=true;
      resetVlist();
      render();
      renderChannels();
      renderUsers();
      poll();
    }
    function switchPrivate(user) {
      if(!user||user.id===identity.id) return;
      if(state.mode==='private'&&state.peer?.id===user.id) { setMobileUsersOpen(false); return; }
      setMobileUsersOpen(false);
      state.mode='private';
      state.peer={...user,online:true};
      state.privateUnread[user.id]=0;
      state.cursor=0;
      state.messages=[];
      state.scrollLocked=true;
      resetVlist();
      render();
      renderChannels();
      renderUsers();
      poll();
    }
    function renderAdminChannels() {
      const root=$('admin-channels');
      const fragment=document.createDocumentFragment();
      state.channels.forEach(channel => {
        const row=document.createElement('div');
        row.className='admin-channel-row';
        const label=document.createElement('span');
        label.textContent=channel.id.replace('channel','频道');
        const input=document.createElement('input');
        input.maxLength=10;
        input.value=channel.name;
        const save=document.createElement('button');
        save.type='button';
        save.textContent='保存';
        save.addEventListener('click',async()=>{
          save.disabled=true;
          const response=await fetch(apiBase+'/api/admin/channel',{method:'POST',headers:{'Content-Type':'application/json','X-Admin-Token':state.adminToken},body:JSON.stringify({id:channel.id,name:input.value})});
          save.disabled=false;
          if(response.ok) {
            const data=await response.json();
            state.channels=data.channels;
            renderChannels();
            renderAdminChannels();
            save.textContent='已保存';
            showToast('频道名称已保存','success');
            setTimeout(()=>save.textContent='保存',900);
          } else {
            save.textContent='失败';
            showToast('频道名称保存失败','error');
            setTimeout(()=>save.textContent='保存',900);
          }
        });
        row.append(label,input,save);
        fragment.append(row);
      });
      root.replaceChildren(fragment);
    }
    function renderBans(bans) {
      const root=$('banned-list');
      if(!bans.length) { const empty=document.createElement('div'); empty.className='banned-empty'; empty.textContent='当前没有被封禁的 IP'; root.replaceChildren(empty); return; }
      const fragment=document.createDocumentFragment();
      bans.forEach(item=>{
        const row=document.createElement('div'); row.className='banned-row';
        const label=document.createElement('span'); label.textContent=item.ip;
        const unban=document.createElement('button'); unban.type='button'; unban.textContent='解封';
        unban.addEventListener('click',async()=>{ unban.disabled=true; if(!await setIpBan(item.ip,false)) unban.disabled=false; });
        row.append(label,unban); fragment.append(row);
      });
      root.replaceChildren(fragment);
    }
    async function loadBans() {
      if(!state.adminToken) return;
      const response=await fetch(apiBase+'/api/admin/bans',{headers:{'X-Admin-Token':state.adminToken}});
      if(response.ok) renderBans((await response.json()).bans||[]);
    }
    async function setIpBan(ip,banned) {
      const response=await fetch(apiBase+'/api/admin/ban',{method:'POST',headers:{'Content-Type':'application/json','X-Admin-Token':state.adminToken},body:JSON.stringify({ip,banned})});
      const data=await response.json().catch(()=>({}));
      if(!response.ok) { $('admin-ban-ip').value=''; $('admin-ban-ip').placeholder=data.error==='cannot ban local address'?'不能封禁服务器本机地址':'IP 地址无效或操作失败'; showToast(data.error==='cannot ban local address'?'不能封禁服务器本机地址':'IP 地址无效或操作失败','error'); return false; }
      renderBans(data.bans||[]); $('admin-ban-ip').value=''; $('admin-ban-ip').placeholder='输入 IP 地址'; showToast(banned?'IP 已封禁':'IP 已解除封禁','success'); return true;
    }
    function setAdminVerifiedUI() {
      document.body.classList.add('admin-mode');
      $('fab-admin').classList.add('verified');
      $('fab-admin').textContent='管理员工具';
      $('admin-status').hidden=false;
      $('admin-status').innerHTML='身份：<b>本机管理员</b><br>点击用户右侧齿轮可查看并封禁 IP。';
    }
    function openAdmin() {
      $('admin-modal').hidden=false;
      $('admin-password').value='';
      $('admin-password').placeholder='输入管理员密码';
      if(state.adminToken) {
        $('admin-login').hidden=true;
        $('admin-tools').hidden=false;
        $('admin-modal-title').textContent='管理员工具';
        renderAdminChannels();
        loadBans();
      } else {
        $('admin-login').hidden=false;
        $('admin-tools').hidden=true;
        $('admin-modal-title').textContent='验证管理员';
      }
    }
    function tick() {
      const now=Date.now();
      const active=state.messages.filter(m=>now-m.at<state.retentionMs);
      if(active.length!==state.messages.length) {
        state.messages=active;
        render();
      }
      vlist.nodeMap.forEach((row, id) => {
        const message = state.messages.find(item => item.id === id);
        if (message) {
          updateMessageCountdown(row, message.at);
          const recallButton=row.querySelector('.recall-action');
          if(recallButton) recallButton.hidden=message.recalled||message.senderId!==identity.id||now-message.at>state.recallWindowMs;
        }
      });
    }
    function updateBlocker(show, retryLeft, reason=state.blockedReason) {
      const blocker = $('blocker');
      blocker.hidden = !show;
      if (show) {
        const retry = Math.max(1, Math.ceil((retryLeft||state.blockRetry)/1000));
        if(reason==='ip connection limit') {
          $('blocker-title').textContent='IP CONNECTION LIMIT';
          $('blocker-message').textContent='当前 IP 已经有一个在线连接。关闭原来的页面并等待连接释放后即可重试。';
          $('blocker-meta-limit').textContent='IP LIMIT 1';
        } else if(reason==='ip banned') {
          $('blocker-title').textContent='ACCESS DENIED';
          $('blocker-message').textContent='当前 IP 已被管理员封禁，暂时无法进入聊天室。';
          $('blocker-meta-limit').textContent='IP BANNED';
        } else {
          $('blocker-title').textContent='ROOM IS FULL';
          $('blocker-message').textContent='当前聊天室同时在线已满，新的连接暂时无法进入。请稍后刷新再试，或等待现有连接超时释放。';
          $('blocker-meta-limit').textContent='LIMIT ' + (state.limit || 100);
        }
        $('blocker-retry').textContent = 'RETRY IN '+retry+'s';
      }
    }
    async function poll() {
      if (state.polling) return;
      state.polling=true;
      const requestedChannel=state.channel;
      const requestedMode=state.mode;
      const requestedPeer=state.peer?.id||'';
      const requestedCursor=state.cursor;
      let delay=state.pollInterval||1500;
      try {
        const peerQuery=requestedMode==='private'?'&peer='+encodeURIComponent(requestedPeer):'';
        const r=await fetch(apiBase+'/api/poll?since='+requestedCursor+'&client='+encodeURIComponent(identity.id)+'&channel='+encodeURIComponent(requestedChannel)+'&name='+encodeURIComponent(identity.name)+'&avatar='+encodeURIComponent(identity.avatar)+peerQuery);
        if(r.status===429) {
          const data = await r.json().catch(()=>({}));
          state.full=true;
          state.blockedReason=data.error||'room full';
          state.limit = data.limit || state.limit || 100;
          state.blockRetry = data.retryAfter || 5000;
          if (data.channels && data.channels.length) {
            state.channels = data.channels;
            state.onlineByChannel = data.onlineByChannel || {};
            state.online = data.online || state.limit;
            renderChannels();
          }
          delay = state.blockRetry;
          $('connection').textContent=state.blockedReason==='ip connection limit'?'IP 连接数已满':'聊天室已满';
          $('refresh').textContent=state.blockedReason==='ip connection limit'?'每个 IP 仅允许 1 个连接':'已达到 '+state.limit+' 人上限';
          $('send').disabled=true;
          updateComposerControls();
          updateBlocker(true, delay,state.blockedReason);
          return;
        }
        if(r.status===403) {
          const data=await r.json().catch(()=>({}));
          state.full=true; state.blockedReason=data.error||'access denied'; state.blockRetry=5000; delay=state.blockRetry;
          $('connection').textContent=state.blockedReason==='ip banned'?'IP 已被封禁':'连接已失效';
          $('refresh').textContent='等待重新连接'; $('send').disabled=true;
          updateComposerControls();
          updateBlocker(true,delay,state.blockedReason);
          return;
        }
        if(!r.ok) throw Error();
        const data=await r.json();
        if(requestedChannel!==state.channel||requestedMode!==state.mode||requestedPeer!==(state.peer?.id||'')) return;
        state.full=false;
        state.blockedReason='';
        updateBlocker(false);
        $('send').disabled=Date.now()<state.sendCooldownUntil;
        if(!state.nameEdited && data.assignedName) {
          identity.name=data.assignedName;
          $('my-name').value=data.assignedName;
        }
        if(typeof data.renderBatch === 'number') state.renderBatch = data.renderBatch;
        if(typeof data.pollInterval === 'number') state.pollInterval = data.pollInterval;
        if(typeof data.recallWindowMs === 'number') state.recallWindowMs = data.recallWindowMs;
        if(typeof data.maxFileBytes === 'number') state.maxFileBytes = data.maxFileBytes;
        state.limit = data.limit;
        state.cursor=data.cursor;
        state.online=data.online;
        state.channels=data.channels;
        state.onlineByChannel=data.onlineByChannel;
        state.users=data.users||[];
        state.privateUnread=data.privateUnread||{};
        state.privateActivity=data.privateActivity||{};
        if(state.mode==='private'&&data.peer) state.peer=data.peer;
        state.retentionMs=data.retentionMs;
        const root=$('messages');
        const wasLocked = state.scrollLocked;
        const atBottom = wasLocked || Math.abs((root.scrollTop + root.clientHeight) - root.scrollHeight) < 6;
        const indexById = new Map(state.messages.map((message,index)=>[message.id,index]));
        const newIds = [];
        const merged = state.messages.slice();
        let hasUpdates=false;
        data.messages.forEach(m=>{
          if(Date.now()-m.at>=data.retentionMs) return;
          const existingIndex=indexById.get(m.id);
          if(existingIndex===undefined) { indexById.set(m.id,merged.length); merged.push(m); newIds.push(m.id); return; }
          if((m.cursor||0)>(merged[existingIndex].cursor||0)) {
            merged[existingIndex]=m; hasUpdates=true;
            const oldNode=vlist.nodeMap.get(m.id); if(oldNode) oldNode.remove(); vlist.nodeMap.delete(m.id);
          }
        });
        state.messages = merged.length > state.renderBatch * 2 ? merged.slice(-state.renderBatch * 2) : merged;
        state.scrollLocked = atBottom || newIds.length > 0;
        $('connection').textContent='已连接';
        $('refresh').textContent='刚刚同步';
        renderChannels();
        renderUsers();
        render({ newIds, force:hasUpdates, scrollToBottom: newIds.length > 0 });
      } catch(e) {
        $('connection').textContent='等待服务';
        $('refresh').textContent='请启动局域网服务';
      } finally {
        state.polling=false;
        setTimeout(poll,delay);
      }
    }
    $('messages').addEventListener('scroll', () => {
      const root = $('messages');
      const atBottom = Math.abs((root.scrollTop + root.clientHeight) - root.scrollHeight) < 8;
      state.scrollLocked = atBottom;
      render();
    });
    $('my-name').addEventListener('input', e => { state.nameEdited=true; identity.name=Array.from(e.target.value).slice(0,5).join(''); e.target.value=identity.name; });
    $('mobile-users-toggle').addEventListener('click',()=>setMobileUsersOpen(true));
    $('mobile-users-close').addEventListener('click',()=>setMobileUsersOpen(false));
    document.addEventListener('keydown',e=>{ if(e.key==='Escape'&&document.body.classList.contains('mobile-users-open')) setMobileUsersOpen(false); });
    window.addEventListener('resize',()=>{ if(window.innerWidth>700) setMobileUsersOpen(false); });
    $('emoji-toggle').addEventListener('click', () => { $('emoji-panel').hidden=!$('emoji-panel').hidden; });
    document.addEventListener('click', e => { if(!e.target.closest('.emoji-wrap')) $('emoji-panel').hidden=true; });
    $('file-toggle').addEventListener('click',()=>{
      if(state.mode!=='private'||!state.peer) { $('connection').textContent='公共频道不允许发送文件'; showToast('公共频道不允许发送文件','warning'); return; }
      if(state.peer.online===false) { $('connection').textContent='对方已离线'; showToast('对方已离线，暂时不能发送文件','warning'); return; }
      $('file-input').click();
    });
    $('file-input').addEventListener('change',async e=>{
      const file=e.target.files?.[0];
      if(!file) return;
      const peerId=state.peer?.id||'';
      if(state.mode!=='private'||!peerId) { e.target.value=''; $('connection').textContent='公共频道不允许发送文件'; showToast('公共频道不允许发送文件','warning'); return; }
      if(file.size<=0||file.size>state.maxFileBytes) { e.target.value=''; const tip=file.size<=0?'不能发送空文件':'文件不能超过 1 MB'; $('connection').textContent=tip; showToast(tip,'warning'); return; }
      state.uploading=true; updateComposerControls(); $('connection').textContent='正在发送 '+file.name; showToast('正在发送 '+file.name,'info');
      let cooldown=0;
      try {
        const response=await fetch(apiBase+'/api/file?client='+encodeURIComponent(identity.id)+'&peer='+encodeURIComponent(peerId),{method:'POST',headers:{'Content-Type':file.type||'application/octet-stream','X-File-Name':encodeURIComponent(file.name)},body:file});
        const data=await response.json().catch(()=>({}));
        if(response.status===429&&data.error==='rate limit') {
          cooldown=data.retryAfter||5000; state.sendCooldownUntil=Date.now()+cooldown;
          $('connection').textContent='发送太快，请稍候'; $('refresh').textContent='文字和文件合计每 5 秒最多发送 2 条';
          showToast('发送太快，每 5 秒只能发送 2 条消息','warning');
          setTimeout(()=>{ if(Date.now()>=state.sendCooldownUntil) { updateComposerControls(); $('connection').textContent='已连接'; } },cooldown);
          throw Error('rate limit');
        }
        if(!response.ok) throw Error(data.error||'upload failed');
        if(state.mode==='private'&&state.peer?.id===peerId&&!state.messages.some(message=>message.id===data.message?.id)) {
          state.messages.push(data.message); state.scrollLocked=true; render({newIds:[data.message.id],scrollToBottom:true});
        }
        $('connection').textContent='文件已发送';
        showToast('文件发送成功','success');
      } catch(error) {
        if(error.message==='peer offline') { if(state.peer?.id===peerId) state.peer.online=false; $('connection').textContent='对方已离线，文件未发送'; showToast('对方已离线，文件未发送','warning'); renderChannels(); }
        else if(error.message==='file too large') { $('connection').textContent='文件不能超过 1 MB'; showToast('文件不能超过 1 MB','warning'); }
        else if(error.message!=='rate limit') { $('connection').textContent='文件发送失败，请重试'; showToast('文件发送失败，请重试','error'); }
      } finally {
        state.uploading=false; e.target.value=''; updateComposerControls();
      }
    });
    $('composer').addEventListener('submit', async e => {
      e.preventDefault();
      const input=$('message');
      const text=input.value.trim();
      if(!text || state.full) return;
      identity.name=Array.from($('my-name').value.trim()).slice(0,5).join('')||'匿名访客';
      $('my-name').value=identity.name;
      $('send').disabled=true;
      let cooldown=0;
      try {
        const response=await fetch(apiBase+'/api/message',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({...identity,mode:state.mode,peer:state.peer?.id||'',channel:state.channel,text})});
        const data=await response.json().catch(()=>({}));
        if(response.status===429 && data.error==='rate limit') {
          cooldown=data.retryAfter||5000;
          state.sendCooldownUntil=Date.now()+cooldown;
          $('connection').textContent='发送太快，请稍候';
          $('refresh').textContent='每 5 秒最多发送 2 条消息';
          showToast('发送太快，每 5 秒只能发送 2 条消息','warning');
          updateComposerControls();
          setTimeout(()=>{ if(!state.full&&Date.now()>=state.sendCooldownUntil) { updateComposerControls(); $('connection').textContent='已连接'; } },cooldown);
          throw Error('rate limit');
        }
        if(response.status === 429) { state.full = true; state.blockedReason=data.error||'room full'; updateBlocker(true, state.blockRetry,state.blockedReason); throw Error('full'); }
        if(!response.ok) throw Error(data.error||'send failed');
        if(data.name && data.name!==identity.name) { identity.name=data.name; $('my-name').value=data.name; }
        input.value='';
        state.scrollLocked = true;
      } catch(err) {
        if(err.message==='peer offline') {
          if(state.peer) state.peer.online=false;
          renderChannels();
          $('connection').textContent='对方已离线';
          showToast('对方已离线，消息未发送','warning');
        } else if(err.message!=='full'&&err.message!=='rate limit') { $('connection').textContent='发送失败，请重试'; showToast('发送失败，请重试','error'); }
      } finally {
        updateComposerControls();
        input.focus();
      }
    });
    fetch(apiBase+'/api/status').then(response=>response.json()).then(data=>{
      state.canAdmin = !!data.canAdmin;
      state.limit = data.limit || state.limit;
      if(typeof data.maxFileBytes==='number') state.maxFileBytes=data.maxFileBytes;
      if(state.canAdmin) {
        $('fab-admin').hidden=false;
      }
    }).catch(()=>{});
    $('fab-admin').addEventListener('click',openAdmin);
    $('admin-login-button').addEventListener('click',async()=>{
      const btn = $('admin-login-button');
      btn.disabled = true;
      const response=await fetch(apiBase+'/api/admin/login',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({password:$('admin-password').value})});
      btn.disabled = false;
      if(!response.ok) {
        $('admin-password').value='';
        $('admin-password').placeholder='密码错误，请重试';
        showToast('管理员密码错误','error');
        return;
      }
      const data=await response.json();
      state.adminToken=data.token;
      setAdminVerifiedUI();
      renderUsers();
      $('admin-modal').hidden=true;
      showToast('管理员验证成功','success');
    });
    document.querySelectorAll('[data-close]').forEach(button=>button.addEventListener('click',()=>$(button.dataset.close).hidden=true));
    $('mobile-channel-select').addEventListener('change',e=>switchChannel(e.target.value));
    $('user-search').addEventListener('input',renderUsers);
    $('admin-ban-button').addEventListener('click',()=>setIpBan($('admin-ban-ip').value.trim(),true));
    setInterval(tick,1000);
    tick();
    poll();
  </script>
</body>
</html>

PAGE_END */
