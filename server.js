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
const avatarIcons = new Set(['orbit','radio','circle-dot-dashed','triangle','hexagon','asterisk','scan-line','waves','box']);
function safeAvatar(raw) { const value=String(raw||''); return avatarIcons.has(value)?value:'orbit'; }
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
function onlineUsers(now=Date.now()) { return [...clients.entries()].filter(([,client])=>now-client.lastSeen<=ACTIVE_WINDOW_MS).map(([id,client])=>({id,name:reservedNames.get(id)||client.name||'匿名用户',avatar:safeAvatar(client.avatar),channel:client.channel})).sort((a,b)=>a.name.localeCompare(b.name,'zh-CN')); }
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
  for(const channelMessages of messages.values()) { const message=channelMessages.find(item=>item.file?.id===fileId); if(message) return message; }
  for(const thread of privateMessages.values()) { const message=thread.find(item=>item.file?.id===fileId); if(message) return message; }
  return null;
}
async function receiveFile(req,res,url) {
  const clientId=String(url.searchParams.get('client')||'');
  const peerId=String(url.searchParams.get('peer')||'');
  const channelId=getChannel(String(url.searchParams.get('channel')||''));
  const now=Date.now(); const ip=requestIp(req);
  pruneClients(now); pruneMessages(now);
  if(isIpBanned(ip)) { req.resume(); return json(res,403,{error:'ip banned'}); }
  if(!clientId||clientId.length>128||peerId.length>128||peerId===clientId||(!peerId&&!channelId)) { req.resume(); return json(res,400,{error:'invalid file session'}); }
  const sender=clients.get(clientId); const peer=peerId?clients.get(peerId):null;
  if(!sender||sender.ip!==ip) { req.resume(); return json(res,403,{error:'not connected'}); }
  if(peerId&&!peer) { req.resume(); return json(res,404,{error:'peer offline'}); }
  if(!peerId&&sender.channel!==channelId) { req.resume(); return json(res,409,{error:'channel changed'}); }
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
  if(peerId&&!clients.has(peerId)) { await forgetFile(fileId); return json(res,404,{error:'peer offline'}); }
  const currentSender=clients.get(clientId);
  if(!currentSender||currentSender.ip!==ip) { await forgetFile(fileId); return json(res,403,{error:'not connected'}); }
  const type=String(req.headers['content-type']||'application/octet-stream').replace(/[\r\n]/g,'').slice(0,100)||'application/octet-stream';
  const mode=peerId?'private':'channel';
  const message={id:crypto.randomUUID(),cursor:++cursor,at:completedAt,mode,channel:mode==='private'?'private':channelId,senderId:clientId,recipientId:peerId||'',name:reservedNames.get(clientId)||currentSender.name||'匿名用户',avatar:safeAvatar(currentSender.avatar),text:'',file:{id:fileId,name,size,type,token:downloadToken},recalled:false};
  const targetMessages=mode==='private'?getPrivateMessages(clientId,peerId,true):messages.get(channelId);
  targetMessages.push(message);
  if(targetMessages.length>MAX_MESSAGES) targetMessages.splice(0,targetMessages.length-MAX_MESSAGES).forEach(deleteMessageFile);
  json(res,201,{ok:true,message});
}
async function sendFile(req,res,url) {
  const match=url.pathname.match(/^\/api\/file\/([0-9a-f-]{36})$/i);
  if(!match) { json(res,404,{error:'not found'}); return true; }
  const fileId=match[1]; const clientId=String(url.searchParams.get('client')||''); const token=String(url.searchParams.get('token')||'');
  const now=Date.now(); const ip=requestIp(req); pruneClients(now); pruneMessages(now);
  const connected=clients.get(clientId); const message=findFileMessage(fileId);
  if(!connected||connected.ip!==ip||!message||message.recalled||now-message.at>=RETENTION_MS) { json(res,404,{error:'file unavailable'}); return true; }
  const canDownload=message.mode==='private'?(clientId===message.senderId||clientId===message.recipientId):connected.channel===message.channel;
  if(!canDownload) { json(res,403,{error:'file access denied'}); return true; }
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
  if (req.method==='POST' && url.pathname==='/api/file') return receiveFile(req,res,url).catch(()=>{ if(!res.headersSent) json(res,500,{error:'upload failed'}); });
  if (req.method==='GET' && url.pathname.startsWith('/api/file/')) return sendFile(req,res,url).catch(()=>{ if(!res.headersSent) json(res,500,{error:'download failed'}); });
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
    const avatar=safeAvatar(url.searchParams.get('avatar')||existing?.avatar);
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
      peerInfo={id:peer,name:reservedNames.get(peer)||peerRecord?.name||'已离线用户',avatar:safeAvatar(peerRecord?.avatar),online:!!peerRecord};
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
    const avatar=safeAvatar(data.avatar);
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
    .file-toggle { width:48px; height:48px; min-width:48px; flex:0 0 48px; padding:0; background:var(--white); font-size:18px; }
    .file-toggle[hidden] { display:none; }
    .file-input { display:none; }
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
    @media (max-width:700px) { body { overflow:hidden; } .shell { height:100vh; height:100dvh; min-height:0; grid-template-rows:56px minmax(0,1fr); } header { padding:0 16px; } main { height:100%; min-height:0; overflow:hidden; display:grid; grid-template-columns:1fr; grid-template-rows:auto minmax(0,1fr); } .profile-panel { overflow:hidden; padding:12px 16px; border-right:0; border-bottom:1px solid var(--line); display:grid; grid-template-columns:minmax(0,1fr) auto; gap:12px; align-items:center; } .profile-panel > div:first-child, .user-directory, .rules { display:none; } .identity { width:min(100%,280px); padding:8px 10px; grid-template-columns:42px minmax(0,1fr); box-shadow:3px 3px 0 var(--lime); } .avatar { width:42px; height:42px; font-size:22px; } .chat { height:100%; min-height:0; grid-template-rows:60px minmax(0,1fr) 70px; } .chat-top, .messages-window { padding-left:16px; padding-right:16px; } .composer { padding:12px 16px; } button { min-width:70px; padding:0 12px; } .file-toggle { width:48px; min-width:48px; flex-basis:48px; padding:0; } .mobile-channel-select { max-width:120px; } .chat-meta { gap:9px; } .chat-meta span:first-child { display:none; } .message-bubble { width:100%; } .message-file { min-width:0; width:100%; } .toast-host { top:12px; } .toast-message { min-width:0; width:100%; } .fab-admin { right:14px; bottom:14px; min-width:108px; height:40px; } }
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
  <style id="void-experience">
    :root {
      --void:#090a09; --void-2:#101210; --surface:#151815; --surface-2:#1b1f1b;
      --bone:#edeadd; --acid:#c8ff36; --signal:#ff5a3d; --cyan:#8be9df;
      --mist:#899087; --hair:rgba(237,234,221,.13); --hair-hot:rgba(200,255,54,.32);
      --ink:var(--bone); --muted:var(--mist); --line:var(--hair); --paper:var(--void);
      --lime:var(--acid); --coral:var(--signal); --white:var(--bone); --dark:var(--void);
      --amber:#ffb84a; --font:'Segoe UI Variable','PingFang SC','Microsoft YaHei',sans-serif;
      --display:'Arial Narrow','Segoe UI Variable Display','PingFang SC',sans-serif;
      --mx:72%; --my:22%;
    }
    * { border-radius:0; }
    html { background:var(--void); }
    body { color:var(--bone); background:var(--void); cursor:default; }
    body::before { content:''; position:fixed; inset:0; z-index:0; pointer-events:none; background:radial-gradient(560px circle at var(--mx) var(--my),rgba(200,255,54,.09),transparent 62%),radial-gradient(480px circle at 18% 82%,rgba(255,90,61,.07),transparent 65%); transition:background .12s linear; }
    body::after { content:''; position:fixed; inset:0; z-index:99; pointer-events:none; opacity:.045; background-image:url("data:image/svg+xml,%3Csvg viewBox='0 0 180 180' xmlns='http://www.w3.org/2000/svg'%3E%3Cfilter id='n'%3E%3CfeTurbulence type='fractalNoise' baseFrequency='.9' numOctaves='3' stitchTiles='stitch'/%3E%3C/filter%3E%3Crect width='100%25' height='100%25' filter='url(%23n)' opacity='.85'/%3E%3C/svg%3E"); mix-blend-mode:soft-light; }
    ::selection { color:var(--void); background:var(--acid); }
    .lucide { width:18px; height:18px; flex:0 0 auto; fill:none; stroke:currentColor; stroke-width:1.7; stroke-linecap:round; stroke-linejoin:round; }
    .shell { isolation:isolate; z-index:1; grid-template-rows:76px minmax(0,1fr); background:linear-gradient(90deg,transparent 0 33.333%,rgba(255,255,255,.015) 33.333% 66.666%,transparent 66.666%); }
    header { position:relative; padding:0 26px; border-color:var(--hair); background:rgba(9,10,9,.78); backdrop-filter:blur(18px); }
    header::after { content:''; position:absolute; right:0; bottom:-1px; width:38%; height:1px; background:linear-gradient(90deg,transparent,var(--acid)); }
    .brand { gap:14px; color:var(--bone); font:650 13px var(--font); letter-spacing:.28em; }
    .brand-lockup { display:flex; align-items:center; gap:14px; }
    .brand-icon { width:34px; height:34px; display:grid; place-items:center; color:var(--void); background:var(--acid); transform:rotate(-7deg); transition:transform .5s cubic-bezier(.2,.8,.2,1); }
    .brand-icon .lucide { width:18px; height:18px; stroke-width:2; }
    .brand:hover .brand-icon { transform:rotate(8deg) scale(1.08); }
    .brand-index { margin-left:4px; color:#5d635d; font-size:9px; letter-spacing:.1em; }
    .status { gap:11px; color:#7f867e; font-size:10px; letter-spacing:.15em; text-transform:uppercase; }
    .pulse { position:relative; width:7px; height:7px; background:var(--acid); box-shadow:none; }
    .pulse::after { content:''; position:absolute; inset:-5px; border:1px solid var(--acid); border-radius:50%; animation:signal-pulse 2.3s ease-out infinite; }
    main { position:relative; grid-template-columns:minmax(250px,20vw) minmax(460px,1fr) minmax(220px,17vw); background:linear-gradient(rgba(237,234,221,.025) 1px,transparent 1px),linear-gradient(90deg,rgba(237,234,221,.025) 1px,transparent 1px); background-size:44px 44px; }
    .profile-panel { position:relative; padding:30px 24px 22px; gap:22px; border-color:var(--hair); background:rgba(12,14,12,.9); scrollbar-color:#3b413b transparent; }
    .profile-panel::after { content:'01'; position:absolute; right:-2px; top:8px; color:rgba(237,234,221,.045); font:800 clamp(90px,9vw,150px)/1 var(--display); letter-spacing:-.08em; writing-mode:vertical-rl; pointer-events:none; }
    .kicker { display:flex; align-items:center; gap:9px; color:var(--acid); font-size:9px; letter-spacing:.28em; }
    .kicker::before { content:''; width:26px; height:1px; background:currentColor; }
    h1 { position:relative; z-index:1; max-width:240px; margin:20px 0 16px; color:var(--bone); font:650 clamp(38px,3.4vw,62px)/.86 var(--display); letter-spacing:-.075em; }
    .intro { max-width:220px; color:#797f78; font-size:11px; line-height:1.8; letter-spacing:.05em; }
    .identity { position:relative; z-index:2; padding:10px; grid-template-columns:46px minmax(0,1fr); gap:10px; border-color:var(--hair); background:rgba(237,234,221,.035); box-shadow:none; overflow:hidden; transition:border-color .25s,background .25s,transform .25s; }
    .identity::before { content:''; position:absolute; inset:auto 0 0; height:2px; background:linear-gradient(90deg,var(--acid),transparent 72%); transform:scaleX(.18); transform-origin:left; transition:transform .35s ease; }
    .identity:hover { border-color:var(--hair-hot); background:rgba(200,255,54,.045); transform:translateY(-2px); }
    .identity:hover::before { transform:scaleX(1); }
    .avatar { width:46px; height:46px; color:var(--void); border:0; background:var(--acid); }
    .avatar .lucide { width:22px; height:22px; stroke-width:1.8; }
    .identity small { margin-bottom:3px; color:#6c736b; font-size:8px; letter-spacing:.18em; text-transform:uppercase; }
    .identity input { height:auto; color:var(--bone); font-size:13px; font-weight:600; letter-spacing:.04em; }
    .identity input:focus { border-color:var(--acid); box-shadow:none; }
    .user-directory { position:relative; z-index:2; gap:10px; }
    .user-directory-head { color:#a1a79f; font-size:9px; letter-spacing:.2em; }
    .user-directory-head span:last-child { color:var(--acid); }
    .search-shell { position:relative; }
    .search-shell .lucide { position:absolute; left:11px; top:50%; width:14px; height:14px; color:#687068; transform:translateY(-50%); pointer-events:none; }
    .user-search { height:38px; padding:8px 10px 8px 34px; }
    .user-list { gap:3px; }
    .user-entry { gap:3px; }
    .user-row { height:41px; padding:0 10px; grid-template-columns:20px minmax(0,1fr) auto auto; gap:9px; border-color:transparent; background:transparent; color:#aeb4ac; }
    .user-row:hover { border-color:var(--hair); background:rgba(237,234,221,.04); color:var(--bone); }
    .user-row.active { border-color:var(--acid); color:var(--void); background:var(--acid); }
    .user-row-avatar { width:20px; height:20px; display:grid; place-items:center; }
    .user-row-avatar .lucide { width:15px; height:15px; }
    .user-row-name { font-size:11px; }
    .user-row-channel { color:#626962; font-size:8px; letter-spacing:.08em; }
    .user-row.active .user-row-channel { color:rgba(9,10,9,.55); }
    .unread-dot { border-radius:0; background:var(--signal); box-shadow:none; }
    .user-admin-button { width:38px; min-width:38px; height:41px; color:var(--void); border:0; background:var(--amber); }
    .user-admin-button .lucide { width:14px; height:14px; }
    .chat { position:relative; grid-template-rows:94px minmax(0,1fr) 88px; border-right:1px solid var(--hair); background:rgba(12,13,12,.76); backdrop-filter:blur(6px); }
    .chat::before { content:'VOID'; position:absolute; z-index:0; right:-1.8vw; top:13%; color:rgba(237,234,221,.023); font:900 clamp(100px,16vw,260px)/.7 var(--display); letter-spacing:-.09em; writing-mode:vertical-rl; pointer-events:none; }
    .chat-top { position:relative; z-index:2; padding:0 28px; border-color:var(--hair); background:rgba(9,10,9,.46); }
    .chat-title { color:var(--bone); font:650 clamp(26px,2.4vw,38px)/1 var(--display); letter-spacing:-.055em; }
    .chat-title::after { content:'.'; color:var(--acid); }
    .chat-meta { gap:0; color:#6f766e; font-size:8px; letter-spacing:.13em; }
    .chat-meta > span { height:28px; padding:0 11px; display:flex; align-items:center; gap:5px; border:1px solid var(--hair); border-right:0; }
    .chat-meta > span:last-child { border-right:1px solid var(--hair); }
    .chat-meta b { color:var(--bone); font-size:10px; }
    .messages { z-index:1; background:transparent; scrollbar-color:#3b423b transparent; }
    .messages-window { padding:28px 30px 34px; gap:20px; }
    .empty { position:relative; color:#6f766e; font-size:12px; line-height:1.9; letter-spacing:.08em; }
    .empty::before { content:''; display:block; width:42px; height:1px; margin:0 auto 16px; background:var(--acid); box-shadow:0 6px 20px var(--acid); }
    .message { grid-template-columns:34px minmax(0,1fr); column-gap:11px; max-width:980px; }
    .message-avatar { width:34px; height:34px; color:var(--bone); border-color:var(--hair); border-radius:0; background:var(--surface); }
    .message-avatar .lucide { width:16px; height:16px; }
    .message-meta { gap:9px; }
    .message-name { color:var(--signal); font-size:9px; letter-spacing:.16em; text-transform:uppercase; }
    .message-tag { padding:1px 5px; color:var(--acid); border-color:var(--hair-hot); border-radius:0; font-size:8px; }
    .message-bubble { min-width:160px; max-width:min(64%,620px); padding:12px 15px 35px; color:#d6d5cb; border-color:var(--hair); border-radius:0; background:rgba(237,234,221,.045); box-shadow:none; font-size:14px; line-height:1.7; backdrop-filter:blur(8px); }
    .message-bubble::before { content:''; position:absolute; left:-1px; top:-1px; width:18px; height:1px; background:var(--signal); }
    .message.self .message-bubble { color:var(--void); border-color:var(--acid); background:var(--acid); box-shadow:8px 8px 0 rgba(200,255,54,.1); }
    .message.self .message-bubble::before { left:auto; right:-1px; width:32px; background:var(--void); }
    .message.self .message-avatar { color:var(--void); border-color:var(--cyan); background:var(--cyan); }
    .message.self .message-name { color:var(--cyan); }
    .message.self { grid-template-columns:minmax(0,1fr) 34px; }
    .message-footer { bottom:6px; }
    .message-action { height:22px; color:#737a72; }
    .message-action .lucide { width:13px; height:13px; margin:auto; }
    .message.self .message-action,.message.self .message-time { color:rgba(9,10,9,.55); }
    .message-action:hover { color:var(--bone); background:rgba(237,234,221,.08); }
    .message.self .message-action:hover { color:var(--void); background:rgba(9,10,9,.1); }
    .message-time { color:#666d66; font-size:9px; letter-spacing:.08em; }
    .message.recalled .message-bubble { color:#6e756e; border-style:solid; background:transparent; }
    .message-file { min-width:250px; }
    .file-download { gap:6px; color:var(--bone); border-color:var(--hair); border-radius:0; background:transparent; }
    .file-download:hover { color:var(--void); background:var(--acid); }
    .composer { z-index:6; gap:8px; padding:18px 28px 20px; border-color:var(--hair); background:rgba(9,10,9,.84); backdrop-filter:blur(18px); }
    input,.mobile-channel-select { color:var(--bone); border-color:var(--hair); background:rgba(237,234,221,.035); caret-color:var(--acid); }
    input::placeholder { color:#555c55; }
    input:focus { border-color:var(--acid); box-shadow:0 0 0 1px rgba(200,255,54,.15),0 0 32px rgba(200,255,54,.05); }
    #message { height:50px; padding:13px 16px; }
    button { height:50px; color:var(--void); border-color:var(--acid); background:var(--acid); letter-spacing:.08em; transition:transform .25s cubic-bezier(.2,.8,.2,1),box-shadow .25s,background .25s,color .25s; }
    button:hover { transform:translateY(-2px); box-shadow:0 8px 22px rgba(200,255,54,.12); }
    #send { min-width:112px; display:inline-flex; align-items:center; justify-content:center; gap:10px; }
    #send .lucide { width:15px; height:15px; transition:transform .25s ease; }
    #send:hover .lucide { transform:translate(3px,-3px); }
    .file-toggle { width:50px; min-width:50px; height:50px; padding:0; display:grid; place-items:center; color:var(--bone); border-color:var(--hair); background:transparent; }
    .file-toggle:hover { color:var(--void); border-color:var(--acid); background:var(--acid); }
    .file-toggle .lucide { width:17px; height:17px; }
    .room-panel { position:relative; padding:30px 20px 22px; gap:24px; border:0; background:rgba(9,10,9,.9); scrollbar-color:#3b413b transparent; }
    .room-panel h2 { display:flex; align-items:center; gap:9px; color:#a8aea6; font-size:9px; letter-spacing:.24em; }
    .room-panel h2 .lucide { width:13px; height:13px; color:var(--acid); }
    .channel-list { gap:4px; }
    .channel-button { position:relative; height:47px; padding:0 11px; color:#8b928a; border-color:transparent; background:transparent; font-size:11px; overflow:hidden; }
    .channel-button::before { content:''; position:absolute; left:0; top:0; bottom:0; width:2px; background:var(--acid); transform:scaleY(0); transition:transform .25s; }
    .channel-button:hover { color:var(--bone); border-color:var(--hair); background:rgba(237,234,221,.03); }
    .channel-button.active { color:var(--bone); border-color:var(--hair); background:rgba(237,234,221,.055); }
    .channel-button.active::before { transform:scaleY(1); }
    .channel-count { color:#5e655e; }
    .channel-button.active .channel-count { color:var(--acid); }
    .metric { padding:20px 0; border-color:var(--hair); }
    .metric-label { color:#666d66; font-size:8px; letter-spacing:.16em; }
    .metric-value { color:var(--bone); font:650 32px/1 var(--display); letter-spacing:-.04em; }
    .online-value::before { background:var(--acid); box-shadow:0 0 16px var(--acid); }
    .rules { color:#666d66; border-color:var(--hair); font-size:9px; line-height:1.9; letter-spacing:.05em; }
    .rules b { color:#aeb4ac; }
    .sync { color:#686f68; font-size:8px; letter-spacing:.1em; }
    .sync::before { color:var(--acid); }
    .fab-admin { right:18px; bottom:18px; min-width:142px; color:var(--void); border:0; border-radius:0; background:var(--amber); box-shadow:7px 7px 0 rgba(255,184,74,.12); }
    .fab-admin .lucide { width:15px; height:15px; }
    .fab-admin::before { display:none; }
    .modal-backdrop { background:rgba(4,5,4,.82); backdrop-filter:blur(14px); }
    .modal { border-color:var(--hair-hot); background:#101310; box-shadow:12px 12px 0 rgba(200,255,54,.12); }
    .modal h2 { color:var(--bone); font:650 27px var(--display); letter-spacing:-.04em; }
    .modal-actions button { color:var(--void); }
    .modal-actions button:first-child { color:var(--bone); border-color:var(--hair); background:transparent; }
    .admin-ban-tools,.metric { border-color:var(--hair); }
    .admin-status,.user-detail { color:#7d847c; }
    .admin-status b,.user-detail b { color:var(--bone); }
    .banned-row button,.admin-channel-row button { color:var(--void); background:var(--acid); }
    .blocker { background:rgba(5,6,5,.94); }
    .blocker-card { border-color:var(--acid); background:var(--void-2); box-shadow:14px 14px 0 rgba(200,255,54,.09); }
    .blocker-card h2 { color:var(--acid); font:700 34px var(--display); }
    .toast-message { border-color:var(--hair); border-radius:0; color:var(--bone); background:#151815; box-shadow:0 18px 50px rgba(0,0,0,.38); }
    .toast-message.success,.toast-message.warning,.toast-message.error { color:var(--bone); background:#151815; }
    .toast-icon { border:0; border-radius:0; }
    .toast-icon .lucide { width:17px; height:17px; }
    .mobile-users-toggle,.mobile-users-close { gap:7px; }
    @keyframes signal-pulse { 0% { opacity:.8; transform:scale(.4); } 80%,100% { opacity:0; transform:scale(1.35); } }
    @keyframes rise { from { opacity:0; transform:translateY(12px) scale(.985); } to { opacity:1; transform:none; } }
    @media (max-width:1000px) {
      main { grid-template-columns:230px minmax(0,1fr); }
      .room-panel { display:none; }
      .mobile-channel-select { display:block; min-width:130px; }
      .chat-title { display:none; }
    }
    @media (max-width:700px) {
      .shell { grid-template-rows:60px minmax(0,1fr); }
      header { padding:0 15px; }
      .brand-index { display:none; }
      main { display:grid; grid-template-columns:1fr; grid-template-rows:auto minmax(0,1fr); }
      .profile-panel { padding:10px 14px; border-color:var(--hair); background:#0e100e; }
      .identity { padding:7px; grid-template-columns:38px minmax(0,1fr); }
      .avatar { width:38px; height:38px; }
      .chat { grid-template-rows:62px minmax(0,1fr) 76px; border:0; }
      .chat-top { padding:0 14px; }
      .chat-meta > span { padding:0 8px; }
      .messages-window { padding:20px 14px 26px; }
      .message-bubble { width:auto; max-width:82%; min-width:120px; font-size:13px; }
      .composer { gap:7px; padding:12px 14px 14px; }
      #message { height:48px; }
      #send { min-width:48px; width:48px; height:48px; padding:0; }
      #send .send-label { display:none; }
      .file-toggle { width:48px; min-width:48px; height:48px; }
      .mobile-channel-select { height:38px; font-size:11px; }
      .mobile-users-toggle { height:38px; color:var(--bone); border-color:var(--hair); background:transparent; }
      .chat-meta { display:none; }
      body.mobile-users-open .profile-panel { inset:60px 0 0; padding:16px; background:#0d0f0d; }
      body.mobile-users-open .profile-panel .mobile-users-close { color:var(--void); background:var(--acid); }
      body.mobile-users-open .fab-admin { display:none!important; }
      .fab-admin { right:12px; bottom:88px; width:46px; min-width:46px; height:46px; padding:0; box-shadow:5px 5px 0 rgba(255,184,74,.12); }
      .fab-admin span { display:none; }
    }
    @media (prefers-reduced-motion:reduce) { *,*::before,*::after { animation-duration:.01ms!important; animation-iteration-count:1!important; scroll-behavior:auto!important; transition-duration:.01ms!important; } }
  </style>
  <style id="liquid-experience">
    :root {
      --sky:#7f9fc4; --sky-deep:#678bb6; --sky-light:#a9c0d9; --glass:rgba(255,255,255,.12);
      --glass-strong:rgba(255,255,255,.22); --glass-line:rgba(255,255,255,.28);
      --glass-soft:rgba(255,255,255,.08); --cloud:#fff; --cloud-70:rgba(255,255,255,.7);
      --cloud-45:rgba(255,255,255,.45); --blue-ink:#52779f;
      --ink:#fff; --bone:#fff; --acid:#fff; --signal:#fff; --cyan:#fff; --void:#6f93bc;
      --hair:rgba(255,255,255,.22); --hair-hot:rgba(255,255,255,.5);
      --font:'Barlow','Segoe UI','PingFang SC','Microsoft YaHei',sans-serif;
      --display:'Instrument Serif','Times New Roman','Songti SC',serif;
    }
    body { color:#fff; background:linear-gradient(135deg,#6f92bb 0%,#87a5c8 48%,#7196bf 100%); font-family:var(--font); font-weight:300; }
    body::before { inset:-20%; background:radial-gradient(600px circle at var(--mx) var(--my),rgba(255,255,255,.22),transparent 62%),radial-gradient(42% 36% at 11% 18%,rgba(220,235,250,.32),transparent 72%),radial-gradient(36% 42% at 91% 82%,rgba(86,124,169,.3),transparent 74%); filter:blur(16px); animation:liquid-breathe 12s ease-in-out infinite alternate; }
    body::after { opacity:.035; mix-blend-mode:overlay; }
    .shell { grid-template-rows:86px minmax(0,1fr); padding:0 16px 16px; background:transparent; }
    header { height:62px; margin:14px 2px 10px; padding:0 20px; border:1px solid var(--glass-line); border-radius:999px; background:rgba(255,255,255,.1); box-shadow:0 16px 40px rgba(47,77,112,.1),inset 0 1px 1px rgba(255,255,255,.28); backdrop-filter:blur(24px) saturate(130%); -webkit-backdrop-filter:blur(24px) saturate(130%); }
    header::after { display:none; }
    .brand { color:#fff; font-size:12px; font-weight:500; letter-spacing:.26em; }
    .brand-icon { width:38px; height:38px; color:#fff; border:1px solid rgba(255,255,255,.5); border-radius:50%; background:rgba(255,255,255,.13); box-shadow:inset 0 1px 1px rgba(255,255,255,.32); transform:none; }
    .brand:hover .brand-icon { transform:rotate(10deg) scale(1.04); }
    .brand-index { color:rgba(255,255,255,.5); font-size:8px; font-weight:400; }
    .status { color:rgba(255,255,255,.72); font-size:9px; font-weight:400; }
    .pulse { background:#fff; box-shadow:0 0 14px rgba(255,255,255,.9); }
    .pulse::after { border-color:#fff; }
    main { gap:12px; grid-template-columns:minmax(248px,19vw) minmax(480px,1fr) minmax(220px,17vw); background:transparent; }
    .profile-panel,.chat,.room-panel { border:1px solid var(--glass-line); border-radius:28px; background:var(--glass); box-shadow:0 22px 55px rgba(40,72,109,.12),inset 0 1px 1px rgba(255,255,255,.3); backdrop-filter:blur(30px) saturate(125%); -webkit-backdrop-filter:blur(30px) saturate(125%); }
    .profile-panel { padding:30px 24px 22px; }
    .profile-panel::after { content:'01'; right:6px; top:18px; color:rgba(255,255,255,.07); font-family:var(--display); font-style:italic; }
    .profile-panel > div:first-child { animation:glass-reveal .9s cubic-bezier(.2,.8,.2,1) both; }
    .kicker { color:rgba(255,255,255,.72); font-size:9px; font-weight:500; letter-spacing:.22em; }
    .kicker::before { width:30px; background:rgba(255,255,255,.72); }
    h1 { max-width:250px; margin:24px 0 18px; color:#fff; font:italic 400 clamp(45px,4vw,66px)/.82 var(--display); letter-spacing:-.055em; text-wrap:balance; }
    .intro { max-width:230px; color:rgba(255,255,255,.64); font-size:11px; font-weight:300; line-height:1.75; }
    .identity { padding:8px; grid-template-columns:46px minmax(0,1fr); border:1px solid var(--glass-line); border-radius:22px; background:rgba(255,255,255,.1); box-shadow:inset 0 1px 1px rgba(255,255,255,.25); overflow:hidden; }
    .identity::before { inset:0; height:auto; border-radius:inherit; background:linear-gradient(120deg,rgba(255,255,255,.28),transparent 32%,transparent 68%,rgba(255,255,255,.14)); opacity:.4; transform:none; pointer-events:none; }
    .identity:hover { border-color:rgba(255,255,255,.48); background:rgba(255,255,255,.16); transform:translateY(-2px); }
    .avatar { width:46px; height:46px; color:var(--blue-ink); border:0; border-radius:50%; background:rgba(255,255,255,.9); box-shadow:0 8px 20px rgba(47,80,116,.12); }
    .identity small { color:rgba(255,255,255,.5); font-weight:500; }
    .identity input { color:#fff; font-weight:500; }
    .identity input:focus { border-color:rgba(255,255,255,.65); }
    .user-directory-head { color:rgba(255,255,255,.68); font-weight:500; }
    .user-directory-head span:last-child { color:#fff; }
    .search-shell .lucide { color:rgba(255,255,255,.55); }
    input,.mobile-channel-select { color:#fff; border:1px solid rgba(255,255,255,.22); border-radius:999px; background:rgba(255,255,255,.08); box-shadow:inset 0 1px 1px rgba(255,255,255,.16); font-family:var(--font); font-weight:300; }
    input::placeholder { color:rgba(255,255,255,.45); }
    input:focus { border-color:rgba(255,255,255,.58); box-shadow:0 0 0 4px rgba(255,255,255,.08),inset 0 1px 1px rgba(255,255,255,.22); }
    .user-row { color:rgba(255,255,255,.73); border:1px solid transparent; border-radius:15px; }
    .user-row:hover { color:#fff; border-color:rgba(255,255,255,.22); background:rgba(255,255,255,.1); }
    .user-row.active { color:var(--blue-ink); border-color:rgba(255,255,255,.65); background:rgba(255,255,255,.88); }
    .user-row-channel { color:rgba(255,255,255,.44); }
    .user-row.active .user-row-channel { color:rgba(82,119,159,.65); }
    .unread-dot { border-radius:999px; background:#fff; color:var(--blue-ink); }
    .user-admin-button { color:var(--blue-ink); border:0; border-radius:15px; background:rgba(255,255,255,.84); }
    .chat { grid-template-rows:92px minmax(0,1fr) 88px; border-right:1px solid var(--glass-line); overflow:hidden; }
    .chat::before { content:'CHAT'; right:-1vw; top:18%; color:rgba(255,255,255,.045); font-family:var(--display); font-style:italic; }
    .chat-top { padding:0 28px; border-color:rgba(255,255,255,.16); background:rgba(255,255,255,.025); }
    .chat-title { color:#fff; font:italic 400 clamp(34px,3vw,46px)/1 var(--display); letter-spacing:-.035em; animation:glass-reveal .7s .12s both; }
    .chat-title::after { color:rgba(255,255,255,.5); }
    .chat-meta { color:rgba(255,255,255,.58); font-weight:400; }
    .chat-meta > span { border-color:rgba(255,255,255,.2); background:rgba(255,255,255,.06); }
    .chat-meta > span:first-child { border-radius:999px 0 0 999px; }
    .chat-meta > span:last-child { border-color:rgba(255,255,255,.2); border-radius:0 999px 999px 0; }
    .chat-meta b { color:#fff; }
    .messages { background:radial-gradient(circle at 50% 48%,rgba(255,255,255,.07),transparent 48%); }
    .empty { color:rgba(255,255,255,.58); font-weight:300; }
    .empty::before { background:#fff; box-shadow:0 4px 20px rgba(255,255,255,.7); }
    .message-avatar { color:#fff; border-color:rgba(255,255,255,.28); border-radius:50%; background:rgba(255,255,255,.1); }
    .message-name { color:rgba(255,255,255,.82); font-weight:500; }
    .message-tag { color:#fff; border-color:rgba(255,255,255,.35); border-radius:999px; }
    .message-bubble { color:#fff; border:1px solid rgba(255,255,255,.24); border-radius:22px 22px 22px 7px; background:rgba(255,255,255,.11); box-shadow:0 12px 32px rgba(48,79,115,.1),inset 0 1px 1px rgba(255,255,255,.2); backdrop-filter:blur(22px); }
    .message-bubble::before { display:none; }
    .message.self .message-bubble { color:var(--blue-ink); border-color:rgba(255,255,255,.72); border-radius:22px 22px 7px 22px; background:rgba(255,255,255,.9); box-shadow:0 16px 38px rgba(48,79,115,.14),inset 0 1px 1px #fff; }
    .message.self .message-avatar { color:var(--blue-ink); border-color:rgba(255,255,255,.72); background:rgba(255,255,255,.82); }
    .message.self .message-name { color:#fff; }
    .message-action,.message-time { color:rgba(255,255,255,.58); }
    .message.self .message-action,.message.self .message-time { color:rgba(82,119,159,.62); }
    .message-action:hover { color:#fff; border-radius:999px; background:rgba(255,255,255,.13); }
    .message.self .message-action:hover { color:var(--blue-ink); background:rgba(82,119,159,.09); }
    .message.recalled .message-bubble { color:rgba(255,255,255,.65); border-style:dashed; background:rgba(255,255,255,.05); }
    .file-download { color:#fff; border-color:rgba(255,255,255,.3); border-radius:999px; background:rgba(255,255,255,.08); }
    .file-download:hover { color:var(--blue-ink); background:#fff; }
    .composer { padding:17px 24px 20px; border-color:rgba(255,255,255,.16); background:linear-gradient(180deg,transparent,rgba(255,255,255,.035)); backdrop-filter:none; }
    #message { padding-left:19px; background:rgba(255,255,255,.1); }
    button { color:var(--blue-ink); border:1px solid rgba(255,255,255,.64); border-radius:999px; background:rgba(255,255,255,.9); box-shadow:0 8px 24px rgba(47,80,116,.1),inset 0 1px 1px #fff; font-family:var(--font); font-weight:500; }
    button:hover { transform:translateY(-2px); box-shadow:0 12px 28px rgba(47,80,116,.16),inset 0 1px 1px #fff; }
    .file-toggle { color:#fff; border-color:rgba(255,255,255,.3); background:rgba(255,255,255,.1); }
    .file-toggle:hover { color:var(--blue-ink); border-color:#fff; background:#fff; }
    .room-panel { padding:30px 20px 22px; }
    .room-panel h2 { color:rgba(255,255,255,.72); font-weight:500; }
    .room-panel h2 .lucide { color:#fff; }
    .channel-button { color:rgba(255,255,255,.7); border:1px solid transparent; border-radius:16px; background:transparent; box-shadow:none; }
    .channel-button::before { left:9px; top:50%; bottom:auto; width:6px; height:6px; border-radius:50%; background:#fff; transform:translateY(-50%) scale(0); }
    .channel-button:hover { color:#fff; border-color:rgba(255,255,255,.24); background:rgba(255,255,255,.08); box-shadow:none; }
    .channel-button.active { padding-left:24px; color:var(--blue-ink); border-color:rgba(255,255,255,.72); background:rgba(255,255,255,.88); box-shadow:0 12px 28px rgba(47,80,116,.1); }
    .channel-button.active::before { transform:translateY(-50%) scale(1); background:var(--blue-ink); }
    .channel-count,.channel-button.active .channel-count { color:inherit; opacity:.68; }
    .metric,.rules { border-color:rgba(255,255,255,.18); }
    .metric-label,.rules,.sync { color:rgba(255,255,255,.54); }
    .metric-value { color:#fff; font:italic 400 36px/1 var(--display); }
    .online-value::before { background:#fff; box-shadow:0 0 18px rgba(255,255,255,.9); }
    .rules b,.sync::before { color:rgba(255,255,255,.86); }
    .fab-admin { color:var(--blue-ink); border-color:rgba(255,255,255,.72); border-radius:999px; background:rgba(255,255,255,.9); box-shadow:0 16px 38px rgba(47,80,116,.18); }
    .modal-backdrop { background:rgba(55,82,114,.42); backdrop-filter:blur(20px); }
    .modal { color:#fff; border:1px solid rgba(255,255,255,.36); border-radius:28px; background:rgba(105,143,185,.76); box-shadow:0 28px 70px rgba(38,66,98,.22),inset 0 1px 1px rgba(255,255,255,.3); backdrop-filter:blur(36px); }
    .modal h2 { color:#fff; font:italic 400 36px var(--display); }
    .modal-actions button:first-child { color:#fff; border-color:rgba(255,255,255,.3); background:rgba(255,255,255,.08); }
    .admin-status,.user-detail { color:rgba(255,255,255,.7); }
    .admin-status b,.user-detail b { color:#fff; }
    .blocker { background:rgba(76,109,148,.78); backdrop-filter:blur(26px); }
    .blocker-card { border:1px solid rgba(255,255,255,.35); border-radius:28px; background:rgba(255,255,255,.12); box-shadow:0 28px 70px rgba(38,66,98,.22); }
    .blocker-card h2 { color:#fff; font:italic 400 42px var(--display); }
    .toast-message,.toast-message.success,.toast-message.warning,.toast-message.error { color:#fff; border:1px solid rgba(255,255,255,.3); border-radius:999px; background:rgba(103,140,183,.72); box-shadow:0 18px 50px rgba(40,70,104,.18); backdrop-filter:blur(28px); }
    .toast-icon { color:#fff; }
    @keyframes glass-reveal { from { opacity:0; filter:blur(12px); transform:translateY(24px); } 55% { opacity:.65; filter:blur(4px); transform:translateY(-3px); } to { opacity:1; filter:blur(0); transform:none; } }
    @keyframes liquid-breathe { from { transform:scale(1) translate3d(-1%,0,0); } to { transform:scale(1.05) translate3d(1%,1%,0); } }
    @media (max-width:1000px) {
      main { grid-template-columns:220px minmax(0,1fr); }
      .room-panel { display:none; }
      .mobile-channel-select { display:block; }
    }
    @media (max-width:700px) {
      body { background:linear-gradient(160deg,#7699c0,#88a8ca 52%,#6f94bd); }
      .shell { grid-template-rows:74px minmax(0,1fr); padding:0 8px 8px; }
      header { height:54px; margin:10px 0; padding:0 13px; }
      .brand-icon { width:34px; height:34px; }
      main { gap:8px; }
      .profile-panel { padding:8px 10px; border-radius:22px; background:rgba(255,255,255,.11); }
      .identity { border-radius:17px; }
      .chat { grid-template-rows:58px minmax(0,1fr) 72px; border-radius:22px; }
      .chat-top { padding:0 10px; }
      .mobile-channel-select { height:38px; border-radius:999px; background:rgba(255,255,255,.1); }
      .mobile-users-toggle { color:#fff; border-color:rgba(255,255,255,.25); background:rgba(255,255,255,.1); box-shadow:none; }
      .messages-window { padding:18px 12px 24px; }
      .message-bubble { max-width:84%; }
      .composer { padding:10px 10px 12px; }
      #message { height:48px; }
      #send { color:var(--blue-ink); background:rgba(255,255,255,.92); }
      body.mobile-users-open .profile-panel { inset:74px 8px 8px; padding:14px; border:1px solid rgba(255,255,255,.3); border-radius:24px; background:rgba(117,154,195,.72); backdrop-filter:blur(32px); }
      body.mobile-users-open .profile-panel .mobile-users-close { color:var(--blue-ink); border-radius:999px; background:rgba(255,255,255,.9); }
      .fab-admin { bottom:84px; }
    }
  </style>
  <style id="light-contrast">
    :root { --navy:#183a5b; --navy-2:#315979; --navy-muted:#456682; --ice:#c3d6e7; --ice-2:#adc7df; }
    body { color:var(--navy); background:linear-gradient(145deg,#cbdbea 0%,#acc6df 48%,#c2d6e8 100%); }
    body::before { background:radial-gradient(620px circle at var(--mx) var(--my),rgba(255,255,255,.55),transparent 65%),radial-gradient(42% 40% at 8% 12%,rgba(255,255,255,.42),transparent 70%),radial-gradient(38% 40% at 92% 86%,rgba(93,139,181,.2),transparent 72%); }
    header { color:var(--navy); border-color:rgba(255,255,255,.58); background:rgba(255,255,255,.28); box-shadow:0 16px 42px rgba(46,81,114,.12),inset 0 1px 1px rgba(255,255,255,.72); }
    .brand,.status { color:var(--navy); }
    .brand-index { color:rgba(24,58,91,.58); }
    .brand-icon { color:var(--navy); border-color:rgba(255,255,255,.76); background:rgba(255,255,255,.5); }
    .pulse { background:#fff; box-shadow:0 0 0 3px rgba(255,255,255,.34),0 0 14px rgba(255,255,255,.9); }
    .profile-panel,.chat,.room-panel { color:var(--navy); border-color:rgba(255,255,255,.54); background:rgba(255,255,255,.22); box-shadow:0 22px 55px rgba(48,82,116,.12),inset 0 1px 1px rgba(255,255,255,.72); }
    .profile-panel { overflow-x:hidden; overscroll-behavior-x:none; }
    .profile-panel::after,.chat::before { color:rgba(255,255,255,.18); }
    .kicker { color:var(--navy-2); }
    .kicker::before { background:var(--navy-2); }
    h1,.chat-title { color:var(--navy); }
    .chat-title::after { color:rgba(24,58,91,.45); }
    .intro { color:var(--navy-muted); font-weight:400; }
    .identity { border-color:rgba(255,255,255,.66); background:rgba(255,255,255,.3); box-shadow:inset 0 1px 1px rgba(255,255,255,.78); }
    .identity:hover { border-color:rgba(255,255,255,.9); background:rgba(255,255,255,.4); }
    .avatar { color:#fff; background:var(--navy); }
    .identity small { color:rgba(24,58,91,.58); }
    .identity input,.mobile-channel-select,input { color:var(--navy); border-color:rgba(255,255,255,.6); background:rgba(255,255,255,.3); }
    input::placeholder { color:rgba(24,58,91,.52); }
    input:focus { border-color:rgba(24,58,91,.45); box-shadow:0 0 0 4px rgba(255,255,255,.18),inset 0 1px 1px rgba(255,255,255,.75); }
    select option { color:var(--navy); background:#e3edf5; }
    .user-directory-head { color:var(--navy-2); }
    .user-directory-head span:last-child { color:var(--navy); }
    .search-shell .lucide { color:var(--navy-muted); }
    .user-row { color:var(--navy-2); font-weight:400; }
    .user-row:hover { color:var(--navy); border-color:rgba(255,255,255,.65); background:rgba(255,255,255,.28); }
    .user-row.active { color:#fff; border-color:var(--navy); background:var(--navy); }
    .user-row-channel { color:rgba(24,58,91,.58); }
    .user-row.active .user-row-channel { color:rgba(255,255,255,.64); }
    .unread-dot { color:#fff; background:var(--navy); }
    .chat-top { border-color:rgba(255,255,255,.42); background:rgba(255,255,255,.08); }
    .chat-meta { color:var(--navy-muted); }
    .chat-meta > span { border-color:rgba(255,255,255,.62); background:rgba(255,255,255,.22); }
    .chat-meta > span:last-child { border-color:rgba(255,255,255,.62); }
    .chat-meta b { color:var(--navy); }
    .messages { background:radial-gradient(circle at 50% 45%,rgba(255,255,255,.22),transparent 48%); }
    .empty { color:var(--navy-muted); font-weight:400; }
    .empty::before { background:var(--navy); box-shadow:0 5px 18px rgba(24,58,91,.25); }
    .message-avatar { color:var(--navy); border-color:rgba(255,255,255,.7); background:rgba(255,255,255,.42); }
    .message-name { color:var(--navy); }
    .message-tag { color:var(--navy-2); border-color:rgba(24,58,91,.25); }
    .message-bubble { color:var(--navy); border-color:rgba(255,255,255,.7); background:rgba(255,255,255,.38); box-shadow:0 12px 32px rgba(48,79,115,.1),inset 0 1px 1px rgba(255,255,255,.82); }
    .message.self .message-bubble { color:#fff; border-color:rgba(24,58,91,.72); background:linear-gradient(145deg,#244d72,#183a5b); box-shadow:0 16px 38px rgba(35,72,106,.22),inset 0 1px 1px rgba(255,255,255,.16); }
    .message.self .message-avatar { color:#fff; border-color:var(--navy); background:var(--navy); }
    .message.self .message-name { color:var(--navy); }
    .message-action,.message-time { color:rgba(24,58,91,.62); }
    .message.self .message-action,.message.self .message-time { color:rgba(255,255,255,.68); }
    .message-action:hover { color:var(--navy); background:rgba(255,255,255,.46); }
    .message.self .message-action:hover { color:#fff; background:rgba(255,255,255,.12); }
    .message.recalled .message-bubble { color:var(--navy-muted); border-color:rgba(24,58,91,.2); background:rgba(255,255,255,.14); }
    .composer { overflow:visible; border-color:rgba(255,255,255,.42); background:linear-gradient(180deg,rgba(255,255,255,.02),rgba(255,255,255,.14)); }
    #message { background:rgba(255,255,255,.34); }
    button { color:#fff; border-color:rgba(24,58,91,.78); background:var(--navy); box-shadow:0 9px 24px rgba(36,72,107,.18),inset 0 1px 1px rgba(255,255,255,.16); }
    button:hover { box-shadow:0 13px 28px rgba(36,72,107,.24),inset 0 1px 1px rgba(255,255,255,.18); }
    .file-toggle,.emoji-toggle { color:var(--navy); border-color:rgba(255,255,255,.65); background:rgba(255,255,255,.34); box-shadow:inset 0 1px 1px rgba(255,255,255,.7); }
    .file-toggle:hover,.emoji-toggle:hover,.emoji-toggle[aria-expanded="true"] { color:#fff; border-color:var(--navy); background:var(--navy); }
    .emoji-wrap { position:relative; z-index:12; flex:0 0 50px; }
    .emoji-toggle { width:50px; min-width:50px; height:50px; padding:0; display:grid; place-items:center; }
    .emoji-panel { position:absolute; left:0; bottom:62px; z-index:20; width:300px; height:270px; padding:14px; display:grid; grid-template-rows:minmax(0,1fr) 32px; gap:10px; border:1px solid rgba(255,255,255,.82); border-radius:26px; background:rgba(225,237,247,.78); box-shadow:0 24px 60px rgba(34,70,104,.22),inset 0 1px 1px #fff; backdrop-filter:blur(32px) saturate(135%); -webkit-backdrop-filter:blur(32px) saturate(135%); overflow:hidden; transform-origin:left bottom; animation:emoji-pop .22s cubic-bezier(.2,.8,.2,1); }
    .emoji-panel[hidden] { display:none; }
    .emoji-grid { min-height:0; display:grid; grid-template-columns:repeat(6,1fr); grid-template-rows:repeat(4,1fr); gap:5px; }
    .emoji-option { width:100%; min-width:0; height:100%; min-height:0; padding:0; display:grid; place-items:center; color:initial; border:0; border-radius:13px; background:transparent; box-shadow:none; font-family:'Segoe UI Emoji','Apple Color Emoji',sans-serif; font-size:21px; line-height:1; }
    .emoji-option:hover { transform:translateY(-2px) scale(1.08); color:initial; background:rgba(255,255,255,.6); box-shadow:0 8px 18px rgba(36,72,107,.1); }
    .emoji-pagination { display:flex; align-items:center; justify-content:center; gap:10px; }
    .emoji-page-button { width:32px; min-width:32px; height:32px; padding:0; display:grid; place-items:center; color:var(--navy); border:1px solid rgba(255,255,255,.7); background:rgba(255,255,255,.48); box-shadow:none; }
    .emoji-page-button:hover { color:#fff; background:var(--navy); }
    .emoji-page-button:disabled { opacity:.35; }
    .emoji-page-label { min-width:48px; color:var(--navy-muted); text-align:center; font-size:10px; font-weight:500; letter-spacing:.12em; }
    .room-panel h2,.room-panel h2 .lucide { color:var(--navy); }
    .channel-button { color:var(--navy-2); font-weight:400; }
    .channel-button:hover { color:var(--navy); border-color:rgba(255,255,255,.65); background:rgba(255,255,255,.28); }
    .channel-button.active { color:#fff; border-color:var(--navy); background:var(--navy); }
    .channel-button.active::before { background:#fff; }
    .metric,.rules { border-color:rgba(255,255,255,.5); }
    .metric-label,.rules,.sync { color:var(--navy-muted); font-weight:400; }
    .metric-value,.rules b,.sync::before { color:var(--navy); }
    .online-value::before { background:var(--navy); box-shadow:0 0 0 4px rgba(24,58,91,.12); }
    .fab-admin { color:#fff; border-color:var(--navy); background:var(--navy); }
    .modal-backdrop { background:rgba(55,83,112,.28); }
    .modal { color:var(--navy); border-color:rgba(255,255,255,.8); background:rgba(223,235,245,.88); box-shadow:0 30px 74px rgba(36,70,103,.25),inset 0 1px 1px #fff; }
    .modal h2 { color:var(--navy); }
    .modal-actions button:first-child { color:var(--navy); border-color:rgba(24,58,91,.22); background:rgba(255,255,255,.38); }
    .admin-status,.user-detail { color:var(--navy-muted); }
    .admin-status b,.user-detail b { color:var(--navy); }
    .toast-message,.toast-message.success,.toast-message.warning,.toast-message.error { color:#fff; border-color:rgba(24,58,91,.72); background:rgba(24,58,91,.88); }
    @keyframes emoji-pop { from { opacity:0; filter:blur(8px); transform:translateY(10px) scale(.96); } to { opacity:1; filter:blur(0); transform:none; } }
    @media (max-width:700px) {
      body { background:linear-gradient(160deg,#c8dbea,#abc6df 52%,#bed3e6); }
      main { grid-template-columns:1fr; grid-template-rows:auto minmax(0,1fr); }
      .mobile-channel-select { color:var(--navy); background:rgba(255,255,255,.34); }
      .mobile-users-toggle { color:var(--navy); border-color:rgba(255,255,255,.62); background:rgba(255,255,255,.3); }
      #send { color:#fff; background:var(--navy); }
      .emoji-wrap { flex-basis:48px; }
      .emoji-toggle { width:48px; min-width:48px; height:48px; }
      .emoji-panel { left:-2px; bottom:58px; width:min(292px,calc(100vw - 28px)); height:260px; padding:12px; border-radius:22px; }
      body.mobile-users-open .profile-panel { width:auto; color:var(--navy); background:rgba(215,231,243,.9); }
      body.mobile-users-open .profile-panel .mobile-users-close { color:#fff; background:var(--navy); }
    }
  </style>
  <style id="ios26-experience">
    :root {
      --ios-blue:#0a84ff; --ios-blue-deep:#0066d6; --ios-ink:#1d1d1f; --ios-secondary:#5e6470;
      --ios-tertiary:#7a8290; --ios-glass:rgba(250,252,255,.5); --ios-glass-strong:rgba(255,255,255,.7);
      --ios-stroke:rgba(255,255,255,.72); --ios-stroke-soft:rgba(255,255,255,.42);
      --ios-shadow:0 18px 44px rgba(43,63,89,.15); --ios-radius:30px; --ios-inner:20px;
      --font:-apple-system,BlinkMacSystemFont,'SF Pro Text','SF Pro Display','Segoe UI','PingFang SC','Microsoft YaHei',sans-serif;
      --display:-apple-system,BlinkMacSystemFont,'SF Pro Display','Segoe UI','PingFang SC','Microsoft YaHei',sans-serif;
    }
    html { background:#b8cbe2; }
    body { color:var(--ios-ink); background:radial-gradient(circle at 8% 0%,rgba(255,255,255,.92),transparent 30%),radial-gradient(circle at 90% 14%,rgba(214,196,255,.62),transparent 31%),radial-gradient(circle at 75% 92%,rgba(255,205,190,.42),transparent 32%),linear-gradient(145deg,#b8d2ea 0%,#dbe8f4 47%,#a9c6e3 100%); font-family:var(--font); font-weight:400; }
    body::before { inset:0; background:radial-gradient(ellipse 28% 42% at 23% 64%,rgba(80,155,255,.22),transparent 72%),radial-gradient(ellipse 36% 30% at 72% 36%,rgba(255,255,255,.34),transparent 74%); filter:none; animation:none; }
    body::after { opacity:.018; mix-blend-mode:multiply; }
    .shell { grid-template-rows:76px minmax(0,1fr); padding:0 12px 12px; }
    header { height:56px; margin:10px 2px; padding:0 16px; color:var(--ios-ink); border:1px solid var(--ios-stroke); border-radius:28px; background:linear-gradient(140deg,rgba(255,255,255,.67),rgba(255,255,255,.34)); box-shadow:0 12px 30px rgba(46,70,98,.12),inset 0 1px 1px rgba(255,255,255,.95),inset 0 -1px 0 rgba(255,255,255,.25); backdrop-filter:blur(22px) saturate(145%); -webkit-backdrop-filter:blur(22px) saturate(145%); contain:paint; }
    .brand,.status { color:var(--ios-ink); }
    .brand { font-size:12px; font-weight:650; letter-spacing:.16em; }
    .brand-index { color:var(--ios-secondary); font-size:8px; font-weight:500; }
    .brand-icon { width:38px; height:38px; color:var(--ios-blue); border:1px solid rgba(255,255,255,.85); border-radius:14px; background:linear-gradient(145deg,rgba(255,255,255,.9),rgba(255,255,255,.48)); box-shadow:0 5px 16px rgba(36,73,110,.12),inset 0 1px 1px #fff; }
    .status { color:var(--ios-secondary); font-weight:500; letter-spacing:.04em; text-transform:none; }
    .pulse { background:#34c759; box-shadow:0 0 0 3px rgba(52,199,89,.16); }
    .pulse::after { display:none; }
    main { gap:10px; grid-template-columns:minmax(250px,19vw) minmax(480px,1fr) minmax(220px,17vw); background:transparent; }
    .profile-panel,.chat,.room-panel { color:var(--ios-ink); border:1px solid var(--ios-stroke); border-radius:var(--ios-radius); background:linear-gradient(145deg,rgba(255,255,255,.58),rgba(242,248,255,.33)); box-shadow:var(--ios-shadow),inset 0 1px 1px rgba(255,255,255,.94),inset 0 -1px 0 rgba(255,255,255,.22); backdrop-filter:blur(22px) saturate(135%); -webkit-backdrop-filter:blur(22px) saturate(135%); contain:paint; }
    .profile-panel { padding:24px 20px 18px; overflow-x:hidden; }
    .profile-panel::after,.chat::before { display:none; }
    .profile-panel > div:first-child,.chat-title { animation:none; filter:none; }
    .kicker { color:var(--ios-blue); font-size:9px; font-weight:650; letter-spacing:.14em; }
    .kicker::before { width:22px; height:2px; border-radius:2px; background:var(--ios-blue); }
    h1 { max-width:230px; margin:18px 0 13px; color:var(--ios-ink); font:700 clamp(36px,3vw,50px)/.96 var(--display); letter-spacing:-.055em; }
    .intro { color:var(--ios-secondary); font-size:11px; font-weight:450; line-height:1.65; }
    .identity { padding:7px; grid-template-columns:46px minmax(0,1fr); border:1px solid rgba(255,255,255,.78); border-radius:22px; background:linear-gradient(145deg,rgba(255,255,255,.62),rgba(255,255,255,.3)); box-shadow:0 8px 20px rgba(52,76,103,.08),inset 0 1px 1px #fff; backdrop-filter:none; }
    .identity::before { display:none; }
    .identity:hover { border-color:#fff; background:rgba(255,255,255,.68); transform:scale(1.01); }
    .avatar { width:46px; height:46px; color:#fff; border-radius:15px; background:linear-gradient(145deg,#3b9cff,#087cff); box-shadow:0 7px 18px rgba(10,132,255,.25),inset 0 1px 1px rgba(255,255,255,.35); }
    .identity small { color:var(--ios-tertiary); font-weight:600; }
    .identity input { color:var(--ios-ink); font-size:13px; font-weight:600; }
    .user-directory-head { color:var(--ios-secondary); font-weight:650; }
    .user-directory-head span:last-child { color:var(--ios-blue); }
    input,.mobile-channel-select { color:var(--ios-ink); border:1px solid rgba(255,255,255,.76); border-radius:16px; background:rgba(255,255,255,.43); box-shadow:inset 0 1px 1px rgba(255,255,255,.92); backdrop-filter:none; }
    input::placeholder { color:var(--ios-tertiary); }
    input:focus { border-color:rgba(10,132,255,.5); box-shadow:0 0 0 4px rgba(10,132,255,.12),inset 0 1px 1px #fff; }
    .search-shell .lucide { color:var(--ios-tertiary); }
    .user-row { color:var(--ios-secondary); border:1px solid transparent; border-radius:15px; font-weight:500; box-shadow:none; }
    .user-row:hover { color:var(--ios-ink); border-color:rgba(255,255,255,.65); background:rgba(255,255,255,.42); }
    .user-row.active { color:#fff; border-color:rgba(10,132,255,.78); background:linear-gradient(145deg,#3099ff,#0a84ff); box-shadow:0 7px 18px rgba(10,132,255,.2); }
    .user-row-channel { color:var(--ios-tertiary); }
    .user-row.active .user-row-channel { color:rgba(255,255,255,.7); }
    .unread-dot { color:#fff; background:#ff3b30; }
    .user-admin-button { color:var(--ios-blue); border-color:rgba(255,255,255,.8); border-radius:15px; background:rgba(255,255,255,.62); box-shadow:inset 0 1px 1px #fff; }
    .chat { grid-template-rows:78px minmax(0,1fr) 84px; background:linear-gradient(150deg,rgba(250,252,255,.68),rgba(238,246,254,.4)); overflow:hidden; }
    .chat-top { padding:0 24px; border:0; background:linear-gradient(180deg,rgba(255,255,255,.18),transparent); }
    .chat-title { color:var(--ios-ink); font:700 clamp(24px,2.3vw,34px)/1 var(--display); letter-spacing:-.04em; }
    .chat-title::after { color:var(--ios-blue); }
    .chat-meta { color:var(--ios-secondary); font-weight:550; letter-spacing:.04em; }
    .chat-meta > span { height:30px; padding:0 10px; border-color:rgba(255,255,255,.82); background:rgba(255,255,255,.44); box-shadow:inset 0 1px 1px #fff; }
    .chat-meta > span:last-child { border-color:rgba(255,255,255,.82); }
    .chat-meta b { color:var(--ios-ink); }
    .messages { background:linear-gradient(180deg,rgba(255,255,255,.08),rgba(255,255,255,.18)); contain:strict; }
    .messages-window { contain:layout style; }
    .empty { color:var(--ios-tertiary); font-weight:500; }
    .empty::before { width:32px; height:3px; border-radius:3px; background:var(--ios-blue); box-shadow:none; }
    .message-avatar { color:var(--ios-blue); border-color:rgba(255,255,255,.78); border-radius:14px; background:rgba(255,255,255,.66); box-shadow:0 5px 12px rgba(48,70,96,.08); }
    .message-name { color:var(--ios-secondary); font-weight:650; letter-spacing:.06em; }
    .message-tag { color:var(--ios-blue); border-color:rgba(10,132,255,.2); border-radius:999px; }
    .message-bubble { color:var(--ios-ink); border:1px solid rgba(255,255,255,.78); border-radius:21px 21px 21px 7px; background:rgba(255,255,255,.68); box-shadow:0 8px 22px rgba(43,66,92,.09),inset 0 1px 1px #fff; backdrop-filter:none; }
    .message.self .message-bubble { color:#fff; border-color:rgba(10,132,255,.75); border-radius:21px 21px 7px 21px; background:linear-gradient(145deg,#339cff,#0a84ff); box-shadow:0 10px 24px rgba(10,132,255,.22),inset 0 1px 1px rgba(255,255,255,.3); }
    .message.self .message-avatar { color:#fff; border-color:rgba(10,132,255,.75); background:var(--ios-blue); }
    .message.self .message-name { color:var(--ios-blue); }
    .message-action,.message-time { color:var(--ios-tertiary); }
    .message.self .message-action,.message.self .message-time { color:rgba(255,255,255,.72); }
    .message-action:hover { color:var(--ios-blue); background:rgba(10,132,255,.09); }
    .message.self .message-action:hover { color:#fff; background:rgba(255,255,255,.13); }
    .message.recalled .message-bubble { color:var(--ios-secondary); border-color:rgba(118,118,128,.16); background:rgba(255,255,255,.35); }
    .composer { margin:8px 12px 12px; padding:8px; gap:7px; border:1px solid rgba(255,255,255,.8); border-radius:27px; background:linear-gradient(145deg,rgba(255,255,255,.72),rgba(255,255,255,.4)); box-shadow:0 12px 30px rgba(39,62,88,.13),inset 0 1px 1px #fff; backdrop-filter:none; overflow:visible; contain:layout style; }
    #message { height:48px; padding:0 16px; border:0; border-radius:19px; background:rgba(255,255,255,.42); box-shadow:none; }
    #message:focus { box-shadow:inset 0 0 0 2px rgba(10,132,255,.2); }
    button { color:var(--ios-ink); border:1px solid rgba(255,255,255,.8); border-radius:17px; background:linear-gradient(145deg,rgba(255,255,255,.82),rgba(255,255,255,.48)); box-shadow:0 5px 14px rgba(44,69,95,.1),inset 0 1px 1px #fff; font-weight:600; transition:transform .16s ease,background .16s ease,box-shadow .16s ease; }
    button:hover { transform:scale(1.025); box-shadow:0 7px 18px rgba(44,69,95,.14),inset 0 1px 1px #fff; }
    button:active { transform:scale(.97); }
    #send { color:#fff; border-color:rgba(10,132,255,.72); border-radius:19px; background:linear-gradient(145deg,#3b9fff,#0a84ff); box-shadow:0 7px 18px rgba(10,132,255,.25),inset 0 1px 1px rgba(255,255,255,.3); }
    .file-toggle,.emoji-toggle { color:var(--ios-blue); border-color:rgba(255,255,255,.84); border-radius:19px; background:rgba(255,255,255,.62); box-shadow:inset 0 1px 1px #fff; }
    .file-toggle:hover,.emoji-toggle:hover,.emoji-toggle[aria-expanded="true"] { color:#fff; border-color:var(--ios-blue); background:var(--ios-blue); }
    .emoji-panel { border-color:rgba(255,255,255,.86); border-radius:28px; background:linear-gradient(145deg,rgba(250,253,255,.88),rgba(235,244,253,.7)); box-shadow:0 22px 58px rgba(38,61,88,.2),inset 0 1px 1px #fff; backdrop-filter:blur(20px) saturate(140%); -webkit-backdrop-filter:blur(20px) saturate(140%); }
    .emoji-option { border-radius:14px; }
    .emoji-option:hover { background:rgba(255,255,255,.74); }
    .emoji-page-button { color:var(--ios-blue); border-color:rgba(255,255,255,.85); background:rgba(255,255,255,.7); }
    .emoji-page-button:hover { color:#fff; background:var(--ios-blue); }
    .emoji-page-label { color:var(--ios-secondary); }
    .room-panel { padding:24px 18px 18px; }
    .room-panel h2,.room-panel h2 .lucide { color:var(--ios-secondary); }
    .channel-button { color:var(--ios-secondary); border-radius:17px; font-weight:550; }
    .channel-button:hover { color:var(--ios-ink); border-color:rgba(255,255,255,.72); background:rgba(255,255,255,.4); }
    .channel-button.active { color:#fff; border-color:rgba(10,132,255,.72); background:linear-gradient(145deg,#329aff,#0a84ff); box-shadow:0 7px 18px rgba(10,132,255,.2); }
    .channel-button.active::before { background:#fff; }
    .metric,.rules { border-color:rgba(255,255,255,.6); }
    .metric-label,.rules,.sync { color:var(--ios-secondary); font-weight:500; }
    .metric-value,.rules b,.sync::before { color:var(--ios-ink); }
    .metric-value { font:700 30px/1 var(--display); }
    .online-value::before { background:#34c759; box-shadow:0 0 0 4px rgba(52,199,89,.13); }
    .fab-admin { color:#fff; border-color:rgba(10,132,255,.72); border-radius:19px; background:linear-gradient(145deg,#319aff,#0a84ff); box-shadow:0 12px 28px rgba(10,132,255,.22),inset 0 1px 1px rgba(255,255,255,.3); }
    .modal-backdrop { background:rgba(58,75,96,.22); backdrop-filter:blur(12px); }
    .modal { color:var(--ios-ink); border-color:rgba(255,255,255,.85); border-radius:32px; background:linear-gradient(145deg,rgba(250,253,255,.9),rgba(231,241,251,.8)); box-shadow:0 28px 70px rgba(39,60,84,.22),inset 0 1px 1px #fff; backdrop-filter:blur(22px) saturate(130%); }
    .modal h2 { color:var(--ios-ink); font:700 28px var(--display); letter-spacing:-.04em; }
    .modal input { background:rgba(255,255,255,.62); }
    .modal-actions button:first-child { color:var(--ios-blue); border-color:rgba(255,255,255,.85); background:rgba(255,255,255,.62); }
    .admin-status,.user-detail { color:var(--ios-secondary); }
    .admin-status b,.user-detail b { color:var(--ios-ink); }
    .toast-message,.toast-message.success,.toast-message.warning,.toast-message.error { color:var(--ios-ink); border-color:rgba(255,255,255,.86); border-radius:20px; background:rgba(248,251,255,.88); box-shadow:0 16px 42px rgba(37,59,84,.18),inset 0 1px 1px #fff; backdrop-filter:blur(18px); }
    .toast-icon { color:var(--ios-blue); }
    @supports not ((backdrop-filter:blur(1px)) or (-webkit-backdrop-filter:blur(1px))) {
      header,.profile-panel,.chat,.room-panel,.emoji-panel,.modal { background:rgba(241,247,253,.94); }
    }
    @media (max-width:1000px) {
      main { grid-template-columns:220px minmax(0,1fr); }
    }
    @media (max-width:700px) {
      body { background:radial-gradient(circle at 18% 0%,rgba(255,255,255,.9),transparent 32%),radial-gradient(circle at 86% 80%,rgba(204,188,255,.44),transparent 34%),linear-gradient(160deg,#b7d1ea,#dce8f4 54%,#abc8e4); }
      .shell { grid-template-rows:70px minmax(0,1fr); padding:0 7px 7px; }
      header { height:52px; margin:9px 0; padding:0 12px; border-radius:24px; }
      .brand-icon { width:34px; height:34px; border-radius:13px; }
      main { grid-template-columns:1fr; grid-template-rows:auto minmax(0,1fr); gap:7px; }
      .profile-panel { padding:7px 9px; border-radius:26px; }
      .identity { border-radius:19px; }
      .avatar { border-radius:14px; }
      .chat { grid-template-rows:58px minmax(0,1fr) 72px; border-radius:28px; }
      .chat-top { padding:0 9px; }
      .mobile-channel-select { height:40px; border-radius:17px; }
      .mobile-users-toggle { height:40px; color:var(--ios-blue); border-color:rgba(255,255,255,.82); border-radius:17px; background:rgba(255,255,255,.6); box-shadow:inset 0 1px 1px #fff; }
      .messages-window { padding:16px 11px 22px; }
      .composer { margin:6px 7px 8px; padding:6px; border-radius:24px; }
      #message { height:46px; border-radius:17px; }
      #send,.file-toggle,.emoji-toggle { width:46px; min-width:46px; height:46px; border-radius:17px; }
      .emoji-wrap { flex-basis:46px; }
      .emoji-panel { left:-1px; bottom:56px; width:min(292px,calc(100vw - 24px)); border-radius:26px; }
      body.mobile-users-open .profile-panel { width:auto; inset:70px 7px 7px; border-radius:28px; background:rgba(239,247,253,.86); }
      body.mobile-users-open .profile-panel .mobile-users-close { color:#fff; border-radius:18px; background:var(--ios-blue); }
      .fab-admin { bottom:80px; border-radius:18px; }
    }
    html.performance-lite body::after { display:none; }
    html.performance-lite header,
    html.performance-lite .profile-panel,
    html.performance-lite .chat,
    html.performance-lite .room-panel {
      -webkit-backdrop-filter:blur(12px) saturate(115%);
      backdrop-filter:blur(12px) saturate(115%);
      box-shadow:0 12px 30px rgba(46,75,105,.11),inset 0 1px 0 rgba(255,255,255,.9);
    }
    html.performance-lite .emoji-panel,
    html.performance-lite .modal,
    html.performance-lite .toast-message {
      -webkit-backdrop-filter:blur(10px) saturate(110%);
      backdrop-filter:blur(10px) saturate(110%);
    }
    @media (max-width:700px),(hover:none) {
      body::after { display:none; }
      button:hover { transform:none; }
    }
    @media (prefers-reduced-motion:reduce) { button,.message,.emoji-panel,.toast-message { transition:none!important; animation:none!important; } }
  </style>
  <style id="small-type-adjustment">
    .brand { font-size:13px; }
    .brand-index { font-size:10px; }
    .status { font-size:11px; }
    .kicker { font-size:11px; }
    .intro { font-size:13px; }
    .identity small { font-size:10px; }
    .identity input { font-size:14px; }
    .user-directory-head { font-size:11px; }
    .user-search { font-size:14px; }
    .user-row-name { font-size:13px; }
    .user-row-channel { font-size:10px; }
    .user-empty { font-size:12px; }
    .unread-dot { font-size:11px; }
    .chat-meta { font-size:10px; }
    .chat-meta b { font-size:12px; }
    .message-name { font-size:11px; }
    .message-tag { font-size:10px; }
    .message-time { font-size:11px; }
    .file-meta { font-size:12px; }
    .file-download { font-size:12px; }
    .emoji-page-label { font-size:12px; }
    .room-panel h2 { font-size:11px; }
    .channel-button { font-size:12px; }
    .metric-label { font-size:10px; }
    .rules { font-size:11px; }
    .sync { font-size:10px; }
    .admin-status,.banned-empty { font-size:13px; }
    .admin-channel-row,.banned-row,.blocker-meta { font-size:13px; }
    .admin-ban-tools h3 { font-size:12px; }
    .toast-message { font-size:14px; }
    .mobile-channel-select { font-size:12px; }
  </style>
  <style id="editable-name-cue">
    .identity input {
      height:28px;
      padding:2px 1px 3px;
      cursor:text!important;
      caret-color:var(--ios-blue);
      user-select:text;
      pointer-events:auto;
      border:0;
      border-bottom:1px solid rgba(29,29,31,.3);
      border-radius:0;
      background:transparent;
      box-shadow:none;
      transition:border-color .16s ease,box-shadow .16s ease,color .16s ease;
    }
    .identity input:hover { border-bottom-color:rgba(10,132,255,.62); }
    .identity input:focus {
      border-bottom-color:var(--ios-blue);
      box-shadow:0 3px 0 -2px rgba(10,132,255,.28);
    }
    .identity:focus-within {
      border-color:rgba(10,132,255,.42);
      box-shadow:0 8px 22px rgba(10,132,255,.1),inset 0 1px 1px #fff;
    }
  </style>
  <style id="sidebar-heading-width-fix">
    .profile-panel h1 {
      width:100%;
      max-width:none;
      white-space:nowrap;
    }
  </style>
  <style id="glass-bubbles-and-controls">
    .message-bubble,
    .message.self .message-bubble {
      color:var(--ios-ink);
      border:1px solid rgba(255,255,255,.88);
      background:
        radial-gradient(circle at 14% 0%,rgba(255,255,255,.72),transparent 38%),
        linear-gradient(145deg,rgba(255,255,255,.58),rgba(232,243,253,.34));
      box-shadow:
        0 10px 26px rgba(43,66,92,.1),
        inset 0 1px 1px rgba(255,255,255,.98),
        inset 0 -1px 0 rgba(255,255,255,.28);
      backdrop-filter:none;
    }
    .message.self .message-bubble {
      border-color:rgba(194,224,255,.9);
      background:
        radial-gradient(circle at 82% 0%,rgba(255,255,255,.86),transparent 38%),
        linear-gradient(145deg,rgba(223,240,255,.72),rgba(191,220,248,.48));
      box-shadow:
        0 11px 28px rgba(31,91,145,.13),
        inset 0 1px 1px #fff,
        inset 0 -1px 0 rgba(120,177,227,.16);
    }
    .message.self .message-avatar {
      color:var(--ios-blue);
      border-color:rgba(255,255,255,.9);
      background:linear-gradient(145deg,rgba(255,255,255,.88),rgba(218,237,253,.62));
      box-shadow:0 6px 16px rgba(48,88,124,.11),inset 0 1px 1px #fff;
    }
    .message.self .message-action,
    .message.self .message-time { color:var(--ios-secondary); }
    .message.self .message-action:hover { color:var(--ios-blue); background:rgba(255,255,255,.46); }
    button,
    #send,
    .file-toggle,
    .emoji-toggle,
    .fab-admin,
    .user-admin-button {
      color:var(--ios-ink);
      border-color:rgba(255,255,255,.9);
      background:
        radial-gradient(circle at 22% 0%,rgba(255,255,255,.95),transparent 46%),
        linear-gradient(145deg,rgba(255,255,255,.72),rgba(226,239,251,.48));
      box-shadow:
        0 7px 18px rgba(42,68,94,.11),
        inset 0 1px 1px #fff,
        inset 0 -1px 0 rgba(255,255,255,.3);
    }
    button:hover,
    #send:hover,
    .file-toggle:hover,
    .emoji-toggle:hover,
    .fab-admin:hover {
      color:var(--ios-blue);
      border-color:rgba(255,255,255,1);
      background:
        radial-gradient(circle at 25% 0%,#fff,transparent 48%),
        linear-gradient(145deg,rgba(255,255,255,.86),rgba(222,239,254,.62));
      box-shadow:0 9px 22px rgba(41,76,108,.14),inset 0 1px 1px #fff;
    }
    #send .lucide,
    .fab-admin .lucide { color:var(--ios-blue); }
    .emoji-toggle[aria-expanded="true"] {
      color:var(--ios-blue);
      border-color:rgba(10,132,255,.28);
      background:linear-gradient(145deg,rgba(255,255,255,.9),rgba(211,234,253,.68));
    }
    .channel-button.active,
    .user-row.active {
      color:var(--ios-blue);
      border-color:rgba(255,255,255,.92);
      background:
        radial-gradient(circle at 20% 0%,rgba(255,255,255,.98),transparent 45%),
        linear-gradient(145deg,rgba(255,255,255,.76),rgba(221,238,252,.54));
      box-shadow:0 8px 20px rgba(42,78,111,.12),inset 0 1px 1px #fff;
    }
    .channel-button.active::before { background:var(--ios-blue); }
    .channel-button.active .channel-count,
    .user-row.active .user-row-channel { color:var(--ios-secondary); }
    .admin-channel-row button,
    .admin-ban-entry button,
    .banned-row button,
    .modal-actions button,
    body.mobile-users-open .profile-panel .mobile-users-close {
      color:var(--ios-ink);
      border-color:rgba(255,255,255,.9);
      background:linear-gradient(145deg,rgba(255,255,255,.82),rgba(223,238,251,.56));
      box-shadow:0 6px 16px rgba(42,68,94,.1),inset 0 1px 1px #fff;
    }
    @media (max-width:700px) {
      #send { color:var(--ios-ink); }
      #send .lucide { color:var(--ios-blue); }
    }
  </style>
  <style id="mobile-overflow-fix">
    html,body,.shell { width:100%; max-width:100%; overflow-x:hidden; }
    @supports (overflow:clip) {
      html,body { overflow-x:clip; }
    }
    @media (max-width:700px) {
      .shell,main,.profile-panel,.chat,.chat-top,.messages,.composer {
        min-width:0;
        max-width:100%;
      }
      main { width:100%; grid-template-columns:minmax(0,1fr); }
      .profile-panel,.chat { width:100%; }
      .identity { width:min(100%,280px); max-width:100%; min-width:0; }
      .chat-top {
        width:100%;
        display:grid;
        grid-template-columns:minmax(0,1fr) 64px;
        gap:7px;
      }
      .mobile-channel-select { width:100%; min-width:0; max-width:100%; }
      .mobile-users-toggle {
        width:64px;
        min-width:0;
        max-width:64px;
        padding:0 7px;
        gap:3px;
        overflow:hidden;
      }
      .mobile-unread-count { position:absolute; top:3px; right:3px; }
      .chat-meta { display:none; }
      .composer {
        width:auto;
        max-width:calc(100% - 14px);
      }
      .composer > * { min-width:0; }
      .emoji-wrap,#send,.file-toggle {
        width:46px;
        min-width:46px;
        max-width:46px;
        flex:0 0 46px;
      }
      #message {
        width:0;
        min-width:0;
        max-width:none;
        flex:1 1 0;
      }
      .message,.message-file,.message-bubble { min-width:0; max-width:100%; }
    }
  </style>
  <style id="visible-user-scrollbar">
    .room-panel {
      scrollbar-width:thin;
      scrollbar-color:rgba(54,91,126,.62) transparent;
      scrollbar-gutter:stable;
    }
    .user-list {
      padding-right:5px;
      scrollbar-width:auto;
      scrollbar-color:rgba(54,91,126,.72) rgba(255,255,255,.3);
      scrollbar-gutter:stable;
    }
    .room-panel::-webkit-scrollbar { width:8px; }
    .room-panel::-webkit-scrollbar-track { background:transparent; }
    .room-panel::-webkit-scrollbar-thumb {
      min-height:46px;
      border:2px solid transparent;
      border-radius:999px;
      background:rgba(54,91,126,.62) padding-box;
    }
    .room-panel::-webkit-scrollbar-thumb:hover {
      background:rgba(24,70,113,.86) padding-box;
    }
    .user-list::-webkit-scrollbar-button,
    .profile-panel::-webkit-scrollbar-button,
    .room-panel::-webkit-scrollbar-button,
    .messages::-webkit-scrollbar-button {
      display:none;
      width:0;
      height:0;
    }
    .user-list::-webkit-scrollbar { width:11px; }
    .user-list::-webkit-scrollbar-track {
      border:1px solid rgba(255,255,255,.62);
      border-radius:999px;
      background:rgba(255,255,255,.28);
      box-shadow:inset 0 1px 3px rgba(50,76,103,.1);
    }
    .user-list::-webkit-scrollbar-thumb {
      min-height:42px;
      border:2px solid transparent;
      border-radius:999px;
      background:linear-gradient(180deg,rgba(80,129,174,.86),rgba(42,83,121,.78)) padding-box;
      box-shadow:inset 0 1px 1px rgba(255,255,255,.55),0 2px 6px rgba(35,66,95,.16);
    }
    .user-list::-webkit-scrollbar-thumb:hover {
      background:linear-gradient(180deg,rgba(55,118,178,.96),rgba(24,70,113,.9)) padding-box;
    }
    .user-list::-webkit-scrollbar-thumb:active {
      background:var(--ios-blue);
    }
    @media (max-width:700px) {
      .user-list { scrollbar-width:thin; }
      .user-list::-webkit-scrollbar { width:8px; }
    }
  </style>
  <style id="desktop-hidden-sidebars">
    @media (min-width:701px) {
      .profile-panel,
      .user-list,
      .room-panel {
        -ms-overflow-style:none;
        scrollbar-width:none;
        scrollbar-gutter:auto;
      }
      .profile-panel::-webkit-scrollbar,
      .user-list::-webkit-scrollbar,
      .room-panel::-webkit-scrollbar {
        display:none;
        width:0;
        height:0;
      }
    }
  </style>
  <style id="message-caret-cue">
    #message {
      position:relative;
      z-index:1;
      cursor:text!important;
      caret-color:var(--ios-blue)!important;
      user-select:text;
      -webkit-user-select:text;
      pointer-events:auto;
    }
    #message:focus {
      outline:none;
      box-shadow:inset 0 0 0 2px rgba(10,132,255,.22),0 0 0 1px rgba(255,255,255,.5);
    }
    .composer:focus-within {
      border-color:rgba(10,132,255,.4);
      box-shadow:0 12px 30px rgba(39,62,88,.13),0 0 0 3px rgba(10,132,255,.08),inset 0 1px 1px #fff;
    }
  </style>
  <style id="nickname-avatar-system">
    .avatar-initial {
      --avatar-from:#4ca4ff;
      --avatar-to:#0a74e8;
      color:#fff!important;
      border-color:rgba(255,255,255,.88)!important;
      background:linear-gradient(145deg,var(--avatar-from),var(--avatar-to))!important;
      box-shadow:0 6px 16px rgba(40,78,116,.18),inset 0 1px 1px rgba(255,255,255,.42)!important;
      font-family:var(--font);
      font-weight:750;
      line-height:1;
      text-transform:uppercase;
      user-select:none;
    }
    .avatar-initial[data-avatar-tone="1"] { --avatar-from:#a287ff; --avatar-to:#7251db; }
    .avatar-initial[data-avatar-tone="2"] { --avatar-from:#3bcdb7; --avatar-to:#078c7e; }
    .avatar-initial[data-avatar-tone="3"] { --avatar-from:#ffb364; --avatar-to:#df7428; }
    .avatar-initial[data-avatar-tone="4"] { --avatar-from:#ff819f; --avatar-to:#d94b70; }
    .avatar-initial[data-avatar-tone="5"] { --avatar-from:#7894ff; --avatar-to:#4059c9; }
    .avatar.avatar-initial { font-size:18px; }
    .user-row-avatar.avatar-initial {
      width:24px;
      height:24px;
      border:1px solid rgba(255,255,255,.88);
      border-radius:9px;
      display:grid;
      place-items:center;
      font-size:11px;
    }
    .message-avatar.avatar-initial { font-size:13px; }
  </style>
</head>
<body>
  <svg width="0" height="0" aria-hidden="true" style="position:absolute;overflow:hidden">
    <defs>
      <symbol id="lucide-radio" viewBox="0 0 24 24"><path d="M4.9 19.1a10 10 0 0 1 0-14.2M7.8 16.2a6 6 0 0 1 0-8.5M12 13a1 1 0 1 0 0-2 1 1 0 0 0 0 2Z"/><path d="M16.2 7.8a6 6 0 0 1 0 8.5M19.1 4.9a10 10 0 0 1 0 14.2"/></symbol>
      <symbol id="lucide-orbit" viewBox="0 0 24 24"><circle cx="12" cy="12" r="3"/><circle cx="19" cy="5" r="2"/><circle cx="5" cy="19" r="2"/><path d="M10.4 2.1a10 10 0 0 1 11.5 11.5M13.6 21.9A10 10 0 0 1 2.1 10.4"/></symbol>
      <symbol id="lucide-circle-dot-dashed" viewBox="0 0 24 24"><path d="M10.1 2.2a10 10 0 0 1 3.8 0M17.6 3.8a10 10 0 0 1 2.6 2.7M21.8 10.1a10 10 0 0 1 0 3.8M20.2 17.6a10 10 0 0 1-2.7 2.6M13.9 21.8a10 10 0 0 1-3.8 0M6.4 20.2a10 10 0 0 1-2.6-2.7M2.2 13.9a10 10 0 0 1 0-3.8M3.8 6.4a10 10 0 0 1 2.7-2.6"/><circle cx="12" cy="12" r="1"/></symbol>
      <symbol id="lucide-triangle" viewBox="0 0 24 24"><path d="M13.73 4a2 2 0 0 0-3.46 0l-8 14A2 2 0 0 0 4 21h16a2 2 0 0 0 1.73-3Z"/></symbol>
      <symbol id="lucide-hexagon" viewBox="0 0 24 24"><path d="M21 16V8a2 2 0 0 0-1-1.73l-7-4a2 2 0 0 0-2 0l-7 4A2 2 0 0 0 3 8v8a2 2 0 0 0 1 1.73l7 4a2 2 0 0 0 2 0l7-4A2 2 0 0 0 21 16Z"/></symbol>
      <symbol id="lucide-asterisk" viewBox="0 0 24 24"><path d="M12 6v12M17.2 9 6.8 15M6.8 9l10.4 6"/></symbol>
      <symbol id="lucide-scan-line" viewBox="0 0 24 24"><path d="M3 7V5a2 2 0 0 1 2-2h2M17 3h2a2 2 0 0 1 2 2v2M21 17v2a2 2 0 0 1-2 2h-2M7 21H5a2 2 0 0 1-2-2v-2M7 12h10"/></symbol>
      <symbol id="lucide-waves" viewBox="0 0 24 24"><path d="M2 6c.6.5 1.2 1 2.5 1C7 7 7 5 9.5 5S12 7 14.5 7 17 5 19.5 5c1.3 0 1.9.5 2.5 1M2 12c.6.5 1.2 1 2.5 1C7 13 7 11 9.5 11s2.5 2 5 2 2.5-2 5-2c1.3 0 1.9.5 2.5 1M2 18c.6.5 1.2 1 2.5 1C7 19 7 17 9.5 17s2.5 2 5 2 2.5-2 5-2c1.3 0 1.9.5 2.5 1"/></symbol>
      <symbol id="lucide-box" viewBox="0 0 24 24"><path d="M21 8a2 2 0 0 0-1-1.73l-7-4a2 2 0 0 0-2 0l-7 4A2 2 0 0 0 3 8v8a2 2 0 0 0 1 1.73l7 4a2 2 0 0 0 2 0l7-4A2 2 0 0 0 21 16Z"/><path d="m3.3 7 8.7 5 8.7-5M12 22V12"/></symbol>
      <symbol id="lucide-users" viewBox="0 0 24 24"><path d="M16 21v-2a4 4 0 0 0-4-4H6a4 4 0 0 0-4 4v2M9 11a4 4 0 1 0 0-8 4 4 0 0 0 0 8ZM22 21v-2a4 4 0 0 0-3-3.87M16 3.13a4 4 0 0 1 0 7.75"/></symbol>
      <symbol id="lucide-smile" viewBox="0 0 24 24"><circle cx="12" cy="12" r="10"/><path d="M8 14s1.5 2 4 2 4-2 4-2M9 9h.01M15 9h.01"/></symbol>
      <symbol id="lucide-chevron-left" viewBox="0 0 24 24"><path d="m15 18-6-6 6-6"/></symbol>
      <symbol id="lucide-chevron-right" viewBox="0 0 24 24"><path d="m9 18 6-6-6-6"/></symbol>
      <symbol id="lucide-x" viewBox="0 0 24 24"><path d="M18 6 6 18M6 6l12 12"/></symbol>
      <symbol id="lucide-paperclip" viewBox="0 0 24 24"><path d="m21.4 11.6-8.9 8.9a6 6 0 0 1-8.5-8.5l9.6-9.6a4 4 0 0 1 5.7 5.7l-9.6 9.6a2 2 0 0 1-2.8-2.8l8.9-8.9"/></symbol>
      <symbol id="lucide-send" viewBox="0 0 24 24"><path d="m22 2-7 20-4-9-9-4Z"/><path d="M22 2 11 13"/></symbol>
      <symbol id="lucide-copy" viewBox="0 0 24 24"><rect width="14" height="14" x="8" y="8" rx="2" ry="2"/><path d="M4 16c-1.1 0-2-.9-2-2V4c0-1.1.9-2 2-2h10c1.1 0 2 .9 2 2"/></symbol>
      <symbol id="lucide-rotate-ccw" viewBox="0 0 24 24"><path d="M3 12a9 9 0 1 0 3-6.7L3 8"/><path d="M3 3v5h5"/></symbol>
      <symbol id="lucide-download" viewBox="0 0 24 24"><path d="M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4M7 10l5 5 5-5M12 15V3"/></symbol>
      <symbol id="lucide-settings-2" viewBox="0 0 24 24"><path d="M20 7h-9M14 17H5M17 17h2M5 7h2"/><circle cx="9" cy="7" r="2"/><circle cx="16" cy="17" r="2"/></symbol>
      <symbol id="lucide-shield-check" viewBox="0 0 24 24"><path d="M20 13c0 5-3.5 7.5-8 9-4.5-1.5-8-4-8-9V5l8-3 8 3Z"/><path d="m9 12 2 2 4-4"/></symbol>
      <symbol id="lucide-check" viewBox="0 0 24 24"><path d="m20 6-11 11-5-5"/></symbol>
      <symbol id="lucide-info" viewBox="0 0 24 24"><circle cx="12" cy="12" r="10"/><path d="M12 16v-4M12 8h.01"/></symbol>
      <symbol id="lucide-triangle-alert" viewBox="0 0 24 24"><path d="m21.7 18-8-14a2 2 0 0 0-3.4 0l-8 14A2 2 0 0 0 4 21h16a2 2 0 0 0 1.7-3Z"/><path d="M12 9v4M12 17h.01"/></symbol>
      <symbol id="lucide-circle-x" viewBox="0 0 24 24"><circle cx="12" cy="12" r="10"/><path d="m15 9-6 6M9 9l6 6"/></symbol>
      <symbol id="lucide-search" viewBox="0 0 24 24"><circle cx="11" cy="11" r="8"/><path d="m21 21-4.3-4.3"/></symbol>
      <symbol id="lucide-hash" viewBox="0 0 24 24"><path d="M4 9h16M4 15h16M10 3 8 21M16 3l-2 18"/></symbol>
      <symbol id="lucide-lock-keyhole" viewBox="0 0 24 24"><rect width="18" height="11" x="3" y="11" rx="2" ry="2"/><path d="M7 11V7a5 5 0 0 1 10 0v4M12 15v3"/></symbol>
    </defs>
  </svg>
  <div class="shell">
    <header><div class="brand"><div class="brand-lockup"><span class="brand-icon"><svg class="lucide"><use href="#lucide-radio"></use></svg></span><span>VOID / CHAT</span><span class="brand-index">LIQUID LOCAL MESSENGER</span></div></div><div class="status"><i class="pulse"></i><span id="connection">正在连接</span></div></header>
    <main>
      <aside class="profile-panel">
        <div><div class="kicker" id="kicker">LOCAL / 001</div><h1>轻声落下，<br>即刻消散。</h1><div class="intro">同一网络中的短暂信号。没有账号，没有档案，只留下此刻的回声。</div></div>
        <button class="mobile-users-close" id="mobile-users-close" type="button"><svg class="lucide"><use href="#lucide-x"></use></svg><span>返回聊天</span></button>
        <div class="identity"><div class="avatar" id="my-avatar"></div><div><small>YOUR SIGNAL</small><input id="my-name" maxlength="5" value="匿名访客" aria-label="编辑用户名"></div></div>
        <div class="user-directory"><div class="user-directory-head"><span>ONLINE SIGNALS</span><span id="user-count">0</span></div><div class="search-shell"><svg class="lucide"><use href="#lucide-search"></use></svg><input class="user-search" id="user-search" type="search" placeholder="检索在线用户" aria-label="搜索在线用户"></div><div class="user-list" id="user-list"></div></div>
      </aside>
      <section class="chat"><div class="chat-top"><div class="chat-title" id="channel-title">唠嗑</div><select class="mobile-channel-select" id="mobile-channel-select" aria-label="切换频道"></select><button class="mobile-users-toggle" id="mobile-users-toggle" type="button" aria-label="查看在线用户" aria-expanded="false"><svg class="lucide"><use href="#lucide-users"></use></svg><span>用户</span><span class="mobile-unread-count" id="mobile-unread-count" hidden></span></button><div class="chat-meta"><span id="channel-code">CHANNEL / 01</span><span><span id="scope-label">本频道</span> <b id="online">0</b></span><span>全站 <b id="total-online-inline">0</b>/100</span></div></div><div class="messages" id="messages"><div class="messages-spacer" id="messages-spacer"><div class="messages-window" id="messages-window"></div></div></div><form class="composer" id="composer"><div class="emoji-wrap"><button class="emoji-toggle" id="emoji-toggle" type="button" aria-label="打开表情面板" aria-expanded="false"><svg class="lucide"><use href="#lucide-smile"></use></svg></button><div class="emoji-panel" id="emoji-panel" hidden></div></div><button class="file-toggle" id="file-toggle" type="button" title="发送文件（最大 1 MB，5 分钟后销毁）" aria-label="选择文件"><svg class="lucide"><use href="#lucide-paperclip"></use></svg></button><input class="file-input" id="file-input" type="file" tabindex="-1"><input id="message" maxlength="500" autocomplete="off" placeholder="说点什么……"><button id="send" type="submit"><span class="send-label">发送</span><svg class="lucide"><use href="#lucide-send"></use></svg></button></form></section>
      <aside class="room-panel"><h2><svg class="lucide"><use href="#lucide-hash"></use></svg><span>CHANNELS</span></h2><div class="channel-list" id="channel-list"></div><div class="metric"><span class="metric-label">全站在线 / CAPACITY</span><div class="metric-value online-value"><span id="total-online">0</span> / 100</div></div><div class="rules"><b>温馨提示</b><br><b>消息与文件仅保留 5 分钟</b><br>发送后 3 分钟内可以撤回<br>公共频道与私聊均可发送文件<br>单个文件最大 1 MB<br>每 5 秒最多发送 2 条内容</div><div class="room-admin-entry"><div class="admin-status" id="admin-status" hidden></div><div class="sync" id="refresh">等待同步</div></div></aside>
    </main>
  </div>
  <div class="toast-host" id="toast-host" aria-live="polite" aria-atomic="true"></div>
  <button class="fab-admin" id="fab-admin" type="button" hidden><svg class="lucide"><use href="#lucide-shield-check"></use></svg><span>验证管理员</span></button>
  <div class="modal-backdrop" id="admin-modal" hidden><div class="modal"><h2 id="admin-modal-title">验证管理员</h2><div id="admin-login"><input id="admin-password" type="password" inputmode="numeric" placeholder="输入管理员密码"><div class="modal-actions"><button type="button" data-close="admin-modal">取消</button><button type="button" id="admin-login-button">验证</button></div></div><div id="admin-tools" hidden><div class="admin-channels" id="admin-channels"></div><div class="admin-ban-tools"><h3>IP 封禁管理</h3><div class="admin-ban-entry"><input id="admin-ban-ip" placeholder="输入 IP 地址" aria-label="要封禁的 IP 地址"><button type="button" id="admin-ban-button">封禁</button></div><div class="banned-list" id="banned-list"></div></div><div class="modal-actions"><button type="button" data-close="admin-modal">完成</button></div></div></div></div>
  <div class="modal-backdrop" id="user-modal" hidden><div class="modal"><h2>用户信息</h2><div class="user-detail" id="user-detail">正在读取</div><div class="modal-actions"><button type="button" data-close="user-modal">关闭</button></div></div></div>
  <div class="blocker" id="blocker" hidden><div class="blocker-card"><h2 id="blocker-title">ROOM IS FULL</h2><p id="blocker-message">当前聊天室同时在线已满，新的连接暂时无法进入。请稍后刷新再试，或等待现有连接超时释放。</p><div class="blocker-meta"><span id="blocker-meta-limit">LIMIT 100</span><span id="blocker-retry">RETRY IN 5s</span></div></div></div>
  <script>
    const names = ['雾中信号','午夜电台','路过的人','蓝色回声','未读消息','七号窗口','风的背面','纸上月光','无名之声','半格电量','雨后电台','凌晨三点','玻璃海岸','远方来客','静默频道','白噪音','南墙以北','小行星带','旧磁带','临时月亮','低空飞行','纸船渡口','橘色回声','没有署名','第九街角','慢速星球','失眠旅人','空白信笺','北纬三十','候车室里','微光入口','借过一下','晴天留声机','倒带之前','未完句号','晚风收件箱','路灯下面','隐身模式','落日存档','匿名观测员','月面漫步者','雨伞借我','发呆俱乐部','半夜醒来','蓝调星期五','海边的字','轻声路过','没有目的地','风筝线外','借来的名字'];
    const avatarIcons = ['orbit','radio','circle-dot-dashed','triangle','hexagon','asterisk','scan-line','waves','box'];
    const identity = { name:names[Math.floor(Math.random()*names.length)], avatar:avatarIcons[Math.floor(Math.random()*avatarIcons.length)], id:crypto.randomUUID ? crypto.randomUUID() : Math.random().toString(36).slice(2) };
    const state = { messages:[], users:[], privateUnread:{}, privateActivity:{}, online:0, cursor:0, polling:false, uploading:false, nameEdited:false, mode:'channel', peer:null, channel:'channel1', channels:[], onlineByChannel:{}, adminToken:'', full:false, blockedReason:'', sendCooldownUntil:0, retentionMs:300000, recallWindowMs:180000, maxFileBytes:1048576, renderBatch:100, pollInterval:1500, blockRetry:5000, canAdmin:false, scrollLocked:true };
    const $ = id => document.getElementById(id);
    const renderCache = { channels:'', users:'' };
    const prefersLessMotion=matchMedia('(prefers-reduced-motion: reduce)').matches;
    const limitedCpu=Number(navigator.hardwareConcurrency||8)<=4;
    const limitedMemory=Number(navigator.deviceMemory||8)<=4;
    document.documentElement.classList.toggle('performance-lite',prefersLessMotion||limitedCpu||limitedMemory);
    const availableIcons = new Set(['radio','orbit','circle-dot-dashed','triangle','hexagon','asterisk','scan-line','waves','box','users','smile','chevron-left','chevron-right','x','paperclip','send','copy','rotate-ccw','download','settings-2','shield-check','check','info','triangle-alert','circle-x','search','hash','lock-keyhole']);
    function iconNode(name, className='lucide') {
      const safe=availableIcons.has(name)?name:'orbit';
      const svg=document.createElementNS('http://www.w3.org/2000/svg','svg');
      svg.setAttribute('class',className); svg.setAttribute('aria-hidden','true');
      const use=document.createElementNS('http://www.w3.org/2000/svg','use');
      use.setAttribute('href','#lucide-'+safe); svg.append(use); return svg;
    }
    function setIcon(target,name) {
      const safe=availableIcons.has(name)?name:'orbit';
      if(target.dataset.icon===safe&&target.childElementCount===1) return;
      target.replaceChildren(iconNode(safe));
      target.dataset.icon=safe;
    }
    const avatarSegmenter=typeof Intl.Segmenter==='function'?new Intl.Segmenter('zh-CN',{granularity:'grapheme'}):null;
    function avatarInitial(name) {
      const value=String(name||'').trim();
      if(!value) return '匿';
      if(avatarSegmenter) return avatarSegmenter.segment(value)[Symbol.iterator]().next().value?.segment||'匿';
      return Array.from(value)[0]||'匿';
    }
    function avatarTone(name) {
      let hash=2166136261;
      for(const character of String(name||'')) {
        hash^=character.codePointAt(0);
        hash=Math.imul(hash,16777619)>>>0;
      }
      return hash%6;
    }
    function setAvatarInitial(target,name) {
      const value=String(name||'').trim()||'匿名';
      const initial=avatarInitial(value).toLocaleUpperCase('zh-CN');
      const tone=String(avatarTone(value));
      if(target.dataset.avatarInitial!==initial) target.textContent=initial;
      target.classList.add('avatar-initial');
      target.dataset.avatarInitial=initial;
      target.dataset.avatarTone=tone;
      delete target.dataset.icon;
      target.setAttribute('aria-hidden','true');
    }
    function setText(target,value) {
      const text=String(value);
      if(target.textContent!==text) target.textContent=text;
    }
    let toastTimer=0;
    function showToast(message,type='info') {
      const host=$('toast-host');
      clearTimeout(toastTimer); host.replaceChildren();
      const toast=document.createElement('div'); toast.className='toast-message '+type; toast.setAttribute('role',type==='error'?'alert':'status');
      const icon=document.createElement('span'); icon.className='toast-icon'; icon.append(iconNode(({success:'check',warning:'triangle-alert',error:'circle-x',info:'info'})[type]||'info'));
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
      '😇','🥰','😍','🤩','😘','😎','🤔','😌','🤗','🥳','😴','🤤',
      '😮','😱','😢','😭','😠','😡','🤯','😳','🥺','😶','🙄','😏',
      '🤪','😜','🤡','💀','👻','👽','🤖','🙌','👏','👍','👎','👌',
      '✌️','🤞','🤟','🤘','👊','✊','🤝','🙏','💪','👋','🤚','💖',
      '👀','🧠','❤️','🧡','💛','💚','💙','💜','🖤','🤍','💔','💕',
      '✨','⭐','🔥','🎉','⚡','💡','🎈','🎁','🍎','🍕','🍰','☕',
      '🌞','🌙','☁️','🌈','🌸','🌊','❄️','🌍','🐶','🐱','🐼','🦊',
      '🐸','🦄','🦋','🐧','🚀','✈️','🚗','🚲','⏰','📌','📚','🎵'
    ];
    const emojiGrid=document.createElement('div'); emojiGrid.className='emoji-grid';
    const emojiPagination=document.createElement('div'); emojiPagination.className='emoji-pagination';
    const previousEmojiPage=document.createElement('button'); previousEmojiPage.className='emoji-page-button'; previousEmojiPage.type='button'; previousEmojiPage.setAttribute('aria-label','上一页表情'); setIcon(previousEmojiPage,'chevron-left');
    const emojiPageLabel=document.createElement('span'); emojiPageLabel.className='emoji-page-label';
    const nextEmojiPage=document.createElement('button'); nextEmojiPage.className='emoji-page-button'; nextEmojiPage.type='button'; nextEmojiPage.setAttribute('aria-label','下一页表情'); setIcon(nextEmojiPage,'chevron-right');
    emojiPagination.append(previousEmojiPage,emojiPageLabel,nextEmojiPage); $('emoji-panel').append(emojiGrid,emojiPagination);
    const emojiPageSize=24; let emojiPage=0;
    function renderEmojiPage() {
      emojiGrid.replaceChildren();
      emojis.slice(emojiPage*emojiPageSize,(emojiPage+1)*emojiPageSize).forEach(emoji=>{
        const button=document.createElement('button'); button.className='emoji-option'; button.type='button'; button.textContent=emoji; button.setAttribute('aria-label','插入表情 '+emoji);
        button.addEventListener('click',()=>{ const input=$('message'); const start=input.selectionStart; input.value=input.value.slice(0,start)+emoji+input.value.slice(input.selectionEnd); input.focus(); input.selectionStart=input.selectionEnd=start+emoji.length; $('emoji-panel').hidden=true; $('emoji-toggle').setAttribute('aria-expanded','false'); });
        emojiGrid.append(button);
      });
      const pageCount=Math.ceil(emojis.length/emojiPageSize); emojiPageLabel.textContent=(emojiPage+1)+' / '+pageCount; previousEmojiPage.disabled=emojiPage===0; nextEmojiPage.disabled=emojiPage===pageCount-1;
    }
    previousEmojiPage.addEventListener('click',()=>{ if(emojiPage>0){ emojiPage--; renderEmojiPage(); } });
    nextEmojiPage.addEventListener('click',()=>{ if(emojiPage<Math.ceil(emojis.length/emojiPageSize)-1){ emojiPage++; renderEmojiPage(); } });
    renderEmojiPage();
    $('my-name').value = identity.name; setAvatarInitial($('my-avatar'),identity.name);
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
        setIcon(button,'check'); setTimeout(()=>setIcon(button,'copy'),900);
        showToast('消息内容已复制','success');
      } catch { setIcon(button,'circle-x'); setTimeout(()=>setIcon(button,'copy'),900); showToast('复制失败，请重试','error'); }
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
        setIcon(button,'triangle-alert');
        setTimeout(()=>setIcon(button,'rotate-ccw'),1000);
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
      row.innerHTML = '<div class="message-avatar"></div><div class="message-meta"><div class="message-name"></div><div class="message-tag" hidden></div></div><div class="message-bubble"><span class="message-text"></span><div class="message-file" hidden><div class="file-name"></div><div class="file-meta"></div><a class="file-download"></a></div><div class="message-footer"><button class="message-action copy-action" type="button" title="复制消息" aria-label="复制消息"></button><time class="message-time"></time><button class="message-action recall-action" type="button" title="撤回消息" aria-label="撤回消息"></button></div></div>';
      setAvatarInitial(row.querySelector('.message-avatar'),m.name);
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
        download.download=m.file.name; download.title='下载 '+m.file.name; download.append(iconNode('download'),document.createTextNode('下载'));
      }
      const tag = row.querySelector('.message-tag');
      if (self) { tag.hidden = false; tag.textContent = '我'; }
      const copyButton=row.querySelector('.copy-action');
      const recallButton=row.querySelector('.recall-action');
      setIcon(copyButton,'copy'); setIcon(recallButton,'rotate-ccw');
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
      $('send').disabled=state.full||state.uploading||cooling||peerOffline;
      $('file-toggle').hidden=false;
      $('file-toggle').disabled=state.full||state.uploading||cooling||peerOffline;
      $('file-toggle').title=peerOffline?'对方已离线':state.uploading?'正在上传文件':state.mode==='private'?'发送私聊文件（最大 1 MB，5 分钟后销毁）':'发送频道文件（最大 1 MB，5 分钟后销毁）';
      $('file-toggle').classList.toggle('is-uploading',state.uploading);
      setIcon($('file-toggle'),state.uploading?'radio':'paperclip');
    }
    function renderChannels() {
      const root=$('channel-list');
      const listSignature=JSON.stringify([
        state.mode,
        state.channel,
        state.peer?.id||'',
        state.peer?.name||'',
        state.channels.map(channel=>[channel.id,channel.name,state.onlineByChannel[channel.id]||0])
      ]);
      if(renderCache.channels!==listSignature) {
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
        renderCache.channels=listSignature;
      }
      const current=state.channels.find(channel=>channel.id===state.channel);
      if(state.mode==='private'&&state.peer) {
        setText($('kicker'),'PRIVATE / 1:1');
        setText($('channel-title'),'与 '+state.peer.name+' 私聊');
        setText($('channel-code'),'PRIVATE / 1:1');
        setText($('scope-label'),'对方');
        setText($('online'),state.peer.online===false?'离线':'在线');
        $('message').placeholder=state.peer.online===false?'对方已离线':'私下说点什么……';
        if(state.peer.online===false) $('send').disabled=true;
        else if(!state.full&&Date.now()>=state.sendCooldownUntil) $('send').disabled=false;
      } else if(current) {
        const idx = state.channels.indexOf(current)+1;
        setText($('kicker'),'LOCAL / ' + String(idx).padStart(3,'0'));
        setText($('channel-title'),current.name);
        setText($('channel-code'),'CHANNEL / '+String(idx).padStart(2,'0'));
        setText($('scope-label'),'本频道');
        setText($('online'),state.onlineByChannel[state.channel]||0);
        $('message').placeholder='说点什么……';
        if(!state.full&&Date.now()>=state.sendCooldownUntil) $('send').disabled=false;
      }
      setText($('total-online'),state.online);
      setText($('total-online-inline'),state.online);
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
      setText($('user-count'),query?filtered.length+'/'+state.users.length:state.users.length);
      const userSignature=JSON.stringify([
        query,
        state.mode,
        state.peer?.id||'',
        Boolean(state.adminToken),
        state.channels.map(channel=>[channel.id,channel.name]),
        filtered.map(user=>[user.id,user.name,user.avatar,user.channel,state.privateUnread[user.id]||0,state.privateActivity[user.id]||0])
      ]);
      if(renderCache.users===userSignature) return;
      renderCache.users=userSignature;
      if(!filtered.length) {
        const empty=document.createElement('div'); empty.className='user-empty'; empty.textContent=query?'没有匹配的在线用户':'暂无在线用户';
        root.replaceChildren(empty); return;
      }
      const fragment=document.createDocumentFragment();
      filtered.forEach(user=>{
        const entry=document.createElement('div'); entry.className='user-entry';
        const button=document.createElement('button'); button.type='button'; button.className='user-row'+(user.id===identity.id?' self':'')+(state.mode==='private'&&state.peer?.id===user.id?' active':'');
        const avatar=document.createElement('span'); avatar.className='user-row-avatar'; setAvatarInitial(avatar,user.name);
        const name=document.createElement('span'); name.className='user-row-name'; name.textContent=user.name+(user.id===identity.id?'（我）':'');
        const channel=document.createElement('span'); channel.className='user-row-channel';
        const channelInfo=state.channels.find(item=>item.id===user.channel); channel.textContent=channelInfo?channelInfo.name:user.channel;
        button.append(avatar,name,channel);
        const unread=state.privateUnread[user.id]||0;
        if(unread) { const dot=document.createElement('span'); dot.className='unread-dot'; dot.textContent=unread>99?'99+':String(unread); button.append(dot); }
        if(user.id!==identity.id) button.addEventListener('click',()=>switchPrivate(user));
        entry.append(button);
        if(state.adminToken) {
          const admin=document.createElement('button'); admin.type='button'; admin.className='user-admin-button'; setIcon(admin,'settings-2'); admin.title='查看用户信息'; admin.setAttribute('aria-label','管理 '+user.name);
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
      $('fab-admin').replaceChildren(iconNode('settings-2'),document.createTextNode('管理员工具'));
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
        render({force:true});
      }
      if(!vlist.nodeMap.size) return;
      const messageById=new Map(state.messages.map(message=>[message.id,message]));
      vlist.nodeMap.forEach((row, id) => {
        const message=messageById.get(id);
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
          setAvatarInitial($('my-avatar'),identity.name);
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
        const wasTrimmed=merged.length>state.renderBatch*2;
        state.messages = wasTrimmed ? merged.slice(-state.renderBatch * 2) : merged;
        state.scrollLocked = atBottom || newIds.length > 0;
        $('connection').textContent='已连接';
        $('refresh').textContent='刚刚同步';
        renderChannels();
        renderUsers();
        if(newIds.length||hasUpdates||wasTrimmed||(vlist.lastStart===-1&&state.messages.length>0)) {
          render({ newIds, force:hasUpdates, scrollToBottom: newIds.length > 0 });
        }
      } catch(e) {
        $('connection').textContent='等待服务';
        $('refresh').textContent='请启动局域网服务';
      } finally {
        state.polling=false;
        setTimeout(poll,delay);
      }
    }
    let scrollRenderFrame=0;
    $('messages').addEventListener('scroll', () => {
      const root = $('messages');
      const atBottom = Math.abs((root.scrollTop + root.clientHeight) - root.scrollHeight) < 8;
      state.scrollLocked = atBottom;
      if(scrollRenderFrame) return;
      scrollRenderFrame=requestAnimationFrame(()=>{
        scrollRenderFrame=0;
        render();
      });
    },{passive:true});
    $('my-name').addEventListener('input', e => {
      state.nameEdited=true;
      identity.name=Array.from(e.target.value).slice(0,5).join('');
      e.target.value=identity.name;
      setAvatarInitial($('my-avatar'),identity.name);
    });
    $('mobile-users-toggle').addEventListener('click',()=>setMobileUsersOpen(true));
    $('mobile-users-close').addEventListener('click',()=>setMobileUsersOpen(false));
    document.addEventListener('keydown',e=>{ if(e.key==='Escape'&&document.body.classList.contains('mobile-users-open')) setMobileUsersOpen(false); });
    window.addEventListener('resize',()=>{ if(window.innerWidth>700) setMobileUsersOpen(false); });
    $('emoji-toggle').addEventListener('click',()=>{ const panel=$('emoji-panel'); panel.hidden=!panel.hidden; $('emoji-toggle').setAttribute('aria-expanded',panel.hidden?'false':'true'); });
    document.addEventListener('click',event=>{ if(!event.target.closest('.emoji-wrap')) { $('emoji-panel').hidden=true; $('emoji-toggle').setAttribute('aria-expanded','false'); } });
    document.addEventListener('keydown',event=>{ if(event.key==='Escape') { $('emoji-panel').hidden=true; $('emoji-toggle').setAttribute('aria-expanded','false'); } });
    $('file-toggle').addEventListener('click',()=>{
      if(state.mode==='private'&&!state.peer) { showToast('当前私聊会话不可用','warning'); return; }
      if(state.mode==='private'&&state.peer.online===false) { $('connection').textContent='对方已离线'; showToast('对方已离线，暂时不能发送文件','warning'); return; }
      $('file-input').click();
    });
    $('file-input').addEventListener('change',async e=>{
      const file=e.target.files?.[0];
      if(!file) return;
      const requestedMode=state.mode;
      const peerId=requestedMode==='private'?(state.peer?.id||''):'';
      const channelId=state.channel;
      if(requestedMode==='private'&&!peerId) { e.target.value=''; showToast('当前私聊会话不可用','warning'); return; }
      if(file.size<=0||file.size>state.maxFileBytes) { e.target.value=''; const tip=file.size<=0?'不能发送空文件':'文件不能超过 1 MB'; $('connection').textContent=tip; showToast(tip,'warning'); return; }
      state.uploading=true; updateComposerControls(); $('connection').textContent='正在发送 '+file.name; showToast('正在发送 '+file.name,'info');
      let cooldown=0;
      try {
        const targetQuery=requestedMode==='private'?'&peer='+encodeURIComponent(peerId):'&channel='+encodeURIComponent(channelId);
        const response=await fetch(apiBase+'/api/file?client='+encodeURIComponent(identity.id)+targetQuery,{method:'POST',headers:{'Content-Type':file.type||'application/octet-stream','X-File-Name':encodeURIComponent(file.name)},body:file});
        const data=await response.json().catch(()=>({}));
        if(response.status===429&&data.error==='rate limit') {
          cooldown=data.retryAfter||5000; state.sendCooldownUntil=Date.now()+cooldown;
          $('connection').textContent='发送太快，请稍候'; $('refresh').textContent='文字和文件合计每 5 秒最多发送 2 条';
          showToast('发送太快，每 5 秒只能发送 2 条消息','warning');
          setTimeout(()=>{ if(Date.now()>=state.sendCooldownUntil) { updateComposerControls(); $('connection').textContent='已连接'; } },cooldown);
          throw Error('rate limit');
        }
        if(!response.ok) throw Error(data.error||'upload failed');
        const stillViewingTarget=requestedMode==='private'?(state.mode==='private'&&state.peer?.id===peerId):(state.mode==='channel'&&state.channel===channelId);
        if(stillViewingTarget&&!state.messages.some(message=>message.id===data.message?.id)) {
          state.messages.push(data.message); state.scrollLocked=true; render({newIds:[data.message.id],scrollToBottom:true});
        }
        $('connection').textContent='文件已发送';
        showToast('文件发送成功','success');
      } catch(error) {
        if(error.message==='peer offline') { if(state.peer?.id===peerId) state.peer.online=false; $('connection').textContent='对方已离线，文件未发送'; showToast('对方已离线，文件未发送','warning'); renderChannels(); }
        else if(error.message==='channel changed') { $('connection').textContent='频道已切换，文件未发送'; showToast('频道已经切换，请重新选择文件','warning'); }
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
        if(data.name && data.name!==identity.name) {
          identity.name=data.name;
          $('my-name').value=data.name;
          setAvatarInitial($('my-avatar'),identity.name);
        }
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
