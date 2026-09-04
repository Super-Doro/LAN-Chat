const http = require('http');
const fs = require('fs');
const path = require('path');
const os = require('os');
const crypto = require('crypto');
const net = require('net');
const zlib = require('zlib');
const { spawn } = require('child_process');

const configuredPort = Number(process.env.LAN_CHAT_PORT);
const PORT = Number.isInteger(configuredPort) && configuredPort > 0 && configuredPort < 65536 ? configuredPort : 9000;
const browserOpenDisabled = /^(1|true|yes|on)$/i.test(String(process.env.LAN_CHAT_NO_OPEN||'').trim());
const PAGE = (() => {
  try {
    const sea = require('node:sea');
    if (sea.isSea()) return sea.getAsset('page.html', 'utf8');
  } catch {}
  const source=fs.readFileSync(__filename,'utf8');
  const start=source.lastIndexOf('/* PAGE_START');
  const end=source.lastIndexOf('PAGE_END */');
  return start<0||end<=start?'<!doctype html><html lang="zh-CN"><body><h1>页面加载失败</h1></body></html>':source.slice(start+'/* PAGE_START'.length,end).trimStart();
})();
const PAGE_GZIP=zlib.gzipSync(PAGE,{level:9});
const DEFAULT_RETENTION_MS = 10 * 60 * 1000;
const MIN_RETENTION_MINUTES = 1;
const MAX_RETENTION_MINUTES = 24 * 60;
const MAX_MESSAGES = 1000;
const MAX_CONNECTIONS = 100;
const ACTIVE_WINDOW_MS = 6000;
const MAX_BODY_BYTES = 16 * 1024;
const DEFAULT_MAX_FILE_BYTES = 1024 * 1024;
const MIN_FILE_MEGABYTES = 1;
const MAX_FILE_MEGABYTES = 20 * 1024;
const MAX_IMAGE_PREVIEW_BYTES = 25 * 1024 * 1024;
const MAX_UPLOAD_DURATION_MS = 12 * 60 * 60 * 1000;
const UPLOAD_CHUNK_BYTES = 1024 * 1024;
const UPLOAD_SESSION_MAX_AGE_MS = 24 * 60 * 60 * 1000;
const ADMIN_PASSWORD = process.env.ADMIN_PASSWORD || '666666';
const RENDER_BATCH = 100;
const POLL_HINT = 1500;
const BLOCK_HINT = 5000;
const MAX_CONNECTIONS_PER_IP = 1;
const SEND_WINDOW_MS = 5000;
const SEND_WINDOW_LIMIT = 2;
const RECALL_WINDOW_MS = 3 * 60 * 1000;
const FILE_DIR = path.join(os.tmpdir(), 'lan-chat-files');
fs.mkdirSync(FILE_DIR,{recursive:true});
const defaultChannels = [
  { id: 'channel1', name: '频道1' },
  { id: 'channel2', name: '频道2' },
  { id: 'channel3', name: '频道3' },
  { id: 'channel4', name: '频道4' },
  { id: 'channel5', name: '频道5' }
];
const channels = defaultChannels.map(channel=>({...channel}));
const messages = new Map(channels.map(channel => [channel.id, []]));
const privateMessages = new Map();
const clients = new Map();
const reservedNames = new Map();
const adminTokens = new Map();
const bannedIps = new Map();
const ownedFileIds = new Set();
const activeUploadIds = new Set();
const uploadSessions = new Map();
const rtcSignals = new Map();
let retentionMs = DEFAULT_RETENTION_MS;
let maxFileBytes = DEFAULT_MAX_FILE_BYTES;
const localAddresses = new Set(['127.0.0.1','::1',...Object.values(os.networkInterfaces()).flat().filter(Boolean).map(item=>item.address)]);
function persistConfig() {}
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
function onlineUsers(now=Date.now()) { return [...clients.entries()].filter(([,client])=>now-client.lastSeen<=ACTIVE_WINDOW_MS).map(([id,client])=>({id,name:reservedNames.get(id)||client.name||'匿名用户',channel:client.channel})).sort((a,b)=>a.name.localeCompare(b.name,'zh-CN')); }
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
function channelUnreadFor(clientId) {
  const client=clients.get(clientId); const read=client?.channelRead||new Map(); const counts={};
  for(const channel of channels) {
    let count=0;
    for(const message of messages.get(channel.id)||[]) if(!message.recalled&&message.senderId!==clientId&&(message.createdCursor||message.cursor)>(read.get(channel.id)||0)) count++;
    counts[channel.id]=count;
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
function deleteMessageFile(message) { if(message?.file?.id&&!message.file.direct) forgetFile(message.file.id); }
function cleanExpiredFilesOnDisk(now=Date.now()) {
  fs.readdir(FILE_DIR,{withFileTypes:true},(error,entries)=>{ if(error) return; entries.filter(entry=>entry.isFile()&&!activeUploadIds.has(entry.name)&&!uploadSessions.has(entry.name)).forEach(entry=>{ const target=path.join(FILE_DIR,entry.name); fs.stat(target,(statError,stat)=>{ if(!statError&&now-stat.mtimeMs>=retentionMs) fs.rm(target,{force:true},()=>{}); }); }); });
}
function keepFreshMessages(items,cutoff) { return items.filter(message=>{ if(message.at>cutoff) return true; deleteMessageFile(message); return false; }); }
function pruneMessages(now=Date.now()) {
  const cutoff=now-retentionMs;
  for(const [channelId,channelMessages] of messages) messages.set(channelId,keepFreshMessages(channelMessages,cutoff));
  for(const [key,thread] of privateMessages) { const active=keepFreshMessages(thread,cutoff); if(active.length) privateMessages.set(key,active); else privateMessages.delete(key); }
}
function cleanExpiredTokens(now=Date.now()) { for(const [token,record] of adminTokens) if(record.expiresAt<now) adminTokens.delete(token); }
function queueRtcSignal(target,signal) {
  const queue=rtcSignals.get(target)||[]; queue.push(signal); if(queue.length>100) queue.splice(0,queue.length-100); rtcSignals.set(target,queue);
}
function takeRtcSignals(target,now=Date.now()) {
  const queue=(rtcSignals.get(target)||[]).filter(item=>now-item.at<30000); rtcSignals.delete(target); return queue;
}
function cleanRtcSignals(now=Date.now()) { for(const [target,queue] of rtcSignals) { const active=queue.filter(item=>now-item.at<30000); if(active.length) rtcSignals.set(target,active); else rtcSignals.delete(target); } }
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
function previewImageType(file) {
  const declared=String(file?.type||'').toLowerCase().split(';')[0].trim();
  const allowed=new Set(['image/jpeg','image/png','image/gif','image/webp','image/avif','image/bmp']);
  if(allowed.has(declared)) return declared;
  const extension=path.extname(String(file?.name||'')).toLowerCase();
  return ({'.jpg':'image/jpeg','.jpeg':'image/jpeg','.png':'image/png','.gif':'image/gif','.webp':'image/webp','.avif':'image/avif','.bmp':'image/bmp'})[extension]||'';
}
function readBinary(req,maxBytes) {
  return new Promise((resolve,reject)=>{
    const chunks=[]; let size=0; let settled=false;
    req.on('data',chunk=>{
      if(settled) return;
      size+=chunk.length;
      if(size>maxBytes) { settled=true; reject(new Error('chunk too large')); req.resume(); return; }
      chunks.push(chunk);
    });
    req.on('end',()=>{ if(!settled) { settled=true; resolve(Buffer.concat(chunks,size)); } });
    req.on('error',error=>{ if(!settled) { settled=true; reject(error); } });
  });
}
function hashFile(target) {
  return new Promise((resolve,reject)=>{
    const hash=crypto.createHash('sha256'); const stream=fs.createReadStream(target);
    stream.on('data',chunk=>hash.update(chunk)); stream.on('error',reject); stream.on('end',()=>resolve(hash.digest('hex')));
  });
}
function discardUpload(session) {
  if(!session) return Promise.resolve();
  uploadSessions.delete(session.id); activeUploadIds.delete(session.id); return forgetFile(session.id);
}
function cleanUploadSessions(now=Date.now()) {
  for(const session of uploadSessions.values()) if(now-session.updatedAt>UPLOAD_SESSION_MAX_AGE_MS) discardUpload(session);
}
function uploadTarget(data) {
  const peerId=String(data.peer||'');
  const channelId=getChannel(String(data.channel||''));
  return {peerId,channelId,mode:peerId?'private':'channel'};
}
function replySnapshot(items,rawId) {
  const id=String(rawId||'');
  if(!id) return null;
  if(!/^[0-9a-f-]{36}$/i.test(id)) return undefined;
  const target=items.find(message=>message.id===id);
  if(!target||target.recalled) return undefined;
  const preview=target.file?'[文件] '+target.file.name:Array.from(String(target.text||'')).slice(0,120).join('');
  return {id:target.id,name:target.name||'匿名用户',preview};
}
async function initializeUpload(req,res) {
  let data;
  try { data=await body(req); } catch(error) { return json(res,error.message==='body too large'?413:400,{error:error.message==='body too large'?'body too large':'invalid'}); }
  const clientId=String(data.client||''); const {peerId,channelId,mode}=uploadTarget(data);
  const now=Date.now(); const ip=requestIp(req); const size=Number(data.size); const fingerprint=String(data.fingerprint||'').slice(0,300);
  pruneClients(now); pruneMessages(now); cleanUploadSessions(now);
  if(isIpBanned(ip)) return json(res,403,{error:'ip banned'});
  if(!clientId||clientId.length>128||peerId.length>128||peerId===clientId||(!peerId&&!channelId)) return json(res,400,{error:'invalid file session'});
  const sender=clients.get(clientId); const peer=peerId?clients.get(peerId):null;
  if(!sender||sender.ip!==ip) return json(res,403,{error:'not connected'});
  if(peerId&&!peer) return json(res,404,{error:'peer offline'});
  if(!peerId&&sender.channel!==channelId) return json(res,409,{error:'channel changed'});
  if(!Number.isInteger(size)||size<=0||size>maxFileBytes) return json(res,413,{error:'file too large',limit:maxFileBytes});
  const name=safeFileName(data.name); if(!name||!fingerprint) return json(res,400,{error:'invalid file'});
  const type=String(data.type||'application/octet-stream').replace(/[\r\n]/g,'').slice(0,100)||'application/octet-stream';
  const resumable=[...uploadSessions.values()].find(session=>session.clientId===clientId&&session.fingerprint===fingerprint&&session.peerId===peerId&&session.channelId===channelId&&session.name===name&&session.size===size);
  if(resumable) {
    resumable.updatedAt=now;
    return json(res,200,{uploadId:resumable.id,chunkBytes:UPLOAD_CHUNK_BYTES,received:resumable.received,size:resumable.size,resumed:resumable.received>0});
  }
  const targetMessages=mode==='private'?getPrivateMessages(clientId,peerId):messages.get(channelId);
  const reply=replySnapshot(targetMessages,String(data.replyTo||''));
  if(reply===undefined) return json(res,400,{error:'invalid reply'});
  const previous=[...uploadSessions.values()].filter(session=>session.clientId===clientId);
  await Promise.all(previous.map(discardUpload));
  const slot=reserveSendSlot(sender,now);
  if(slot.retryAfter) return json(res,429,{error:'rate limit',retryAfter:slot.retryAfter});
  clients.set(clientId,{...sender,lastSeen:now,sentAt:slot.sentAt});
  const id=crypto.randomUUID(); const session={id,clientId,peerId,channelId,mode,name,size,type,fingerprint,reply,received:0,createdAt:now,updatedAt:now,locked:false,cancelled:false};
  try { await fs.promises.writeFile(filePath(id),Buffer.alloc(0),{flag:'wx'}); }
  catch { return json(res,500,{error:'upload init failed'}); }
  ownedFileIds.add(id); uploadSessions.set(id,session);
  json(res,201,{uploadId:id,chunkBytes:UPLOAD_CHUNK_BYTES,received:0,size,resumed:false});
}
async function receiveUploadChunk(req,res,url,uploadId) {
  const clientId=String(url.searchParams.get('client')||''); const session=uploadSessions.get(uploadId);
  const ip=requestIp(req); const connected=clients.get(clientId); const offset=Number(req.headers['x-upload-offset']); const expectedHash=String(req.headers['x-chunk-sha256']||'').toLowerCase();
  if(isIpBanned(ip)) { req.resume(); return json(res,403,{error:'ip banned'}); }
  if(!session||session.clientId!==clientId) { req.resume(); return json(res,404,{error:'upload session expired'}); }
  if(!connected||connected.ip!==ip) { req.resume(); return json(res,403,{error:'not connected'}); }
  if(session.cancelled) { req.resume(); return json(res,409,{error:'upload cancelled',received:session.received}); }
  if(session.locked) { req.resume(); return json(res,409,{error:'upload busy',received:session.received}); }
  if(!Number.isInteger(offset)||offset!==session.received) { req.resume(); return json(res,409,{error:'offset mismatch',received:session.received}); }
  if(!/^[0-9a-f]{64}$/.test(expectedHash)) { req.resume(); return json(res,400,{error:'invalid chunk hash'}); }
  session.locked=true; activeUploadIds.add(uploadId);
  try {
    const chunk=await readBinary(req,UPLOAD_CHUNK_BYTES);
    if(session.cancelled) return json(res,409,{error:'upload cancelled',received:session.received});
    if(!chunk.length||session.received+chunk.length>session.size) return json(res,400,{error:'invalid chunk size',received:session.received});
    const actualHash=crypto.createHash('sha256').update(chunk).digest('hex');
    if(actualHash!==expectedHash) return json(res,422,{error:'chunk hash mismatch',received:session.received});
    const handle=await fs.promises.open(filePath(uploadId),'r+');
    try { await handle.write(chunk,0,chunk.length,session.received); } finally { await handle.close(); }
    if(session.cancelled) return json(res,409,{error:'upload cancelled',received:session.received});
    session.received+=chunk.length; session.updatedAt=Date.now();
    clients.set(clientId,{...connected,lastSeen:session.updatedAt});
    return json(res,200,{ok:true,received:session.received,size:session.size});
  } catch(error) {
    return json(res,error.message==='chunk too large'?413:500,{error:error.message==='chunk too large'?'chunk too large':'chunk upload failed',received:session.received});
  } finally { session.locked=false; activeUploadIds.delete(uploadId); if(session.cancelled) await discardUpload(session); }
}
async function completeUpload(req,res,uploadId) {
  let data;
  try { data=await body(req); } catch { return json(res,400,{error:'invalid'}); }
  const clientId=String(data.client||''); const session=uploadSessions.get(uploadId); const ip=requestIp(req); const now=Date.now();
  if(isIpBanned(ip)) return json(res,403,{error:'ip banned'});
  if(!session||session.clientId!==clientId) return json(res,404,{error:'upload session expired'});
  if(session.cancelled) { await discardUpload(session); return json(res,409,{error:'upload cancelled'}); }
  const sender=clients.get(clientId);
  if(!sender||sender.ip!==ip) return json(res,403,{error:'not connected'});
  if(session.locked) return json(res,409,{error:'upload busy',received:session.received});
  if(session.received!==session.size) return json(res,409,{error:'upload incomplete',received:session.received,size:session.size});
  if(session.peerId&&!clients.has(session.peerId)) return json(res,404,{error:'peer offline'});
  if(!session.peerId&&sender.channel!==session.channelId) return json(res,409,{error:'channel changed'});
  session.locked=true; activeUploadIds.add(uploadId);
  try {
    const sha256=await hashFile(filePath(uploadId));
    if(session.cancelled) return json(res,409,{error:'upload cancelled'});
    if(session.peerId&&!clients.has(session.peerId)) return json(res,404,{error:'peer offline'});
    const currentSender=clients.get(clientId); if(!currentSender||currentSender.ip!==ip) return json(res,403,{error:'not connected'});
    if(!session.peerId&&currentSender.channel!==session.channelId) return json(res,409,{error:'channel changed'});
    const completedAt=Date.now(); const downloadToken=crypto.randomBytes(24).toString('hex'); const messageCursor=++cursor;
    const message={id:crypto.randomUUID(),cursor:messageCursor,createdCursor:messageCursor,at:completedAt,mode:session.mode,channel:session.mode==='private'?'private':session.channelId,senderId:clientId,recipientId:session.peerId||'',name:reservedNames.get(clientId)||currentSender.name||'匿名用户',text:'',file:{id:uploadId,name:session.name,size:session.size,type:session.type,token:downloadToken,sha256},reply:session.reply||null,deliveredAt:null,readAt:null,recalled:false};
    const targetMessages=session.mode==='private'?getPrivateMessages(clientId,session.peerId,true):messages.get(session.channelId);
    targetMessages.push(message);
    if(targetMessages.length>MAX_MESSAGES) targetMessages.splice(0,targetMessages.length-MAX_MESSAGES).forEach(deleteMessageFile);
    uploadSessions.delete(uploadId); activeUploadIds.delete(uploadId);
    return json(res,201,{ok:true,message,sha256});
  } catch { return json(res,500,{error:'upload finalize failed'}); }
  finally { session.locked=false; activeUploadIds.delete(uploadId); if(session.cancelled) await discardUpload(session); }
}
async function cancelUpload(req,res,url,uploadId) {
  const clientId=String(url.searchParams.get('client')||''); const session=uploadSessions.get(uploadId); const connected=clients.get(clientId);
  if(!session||session.clientId!==clientId) return json(res,404,{error:'upload session expired'});
  if(!connected||connected.ip!==requestIp(req)) return json(res,403,{error:'not connected'});
  session.cancelled=true;
  if(session.locked) return json(res,202,{ok:true,pending:true});
  await discardUpload(session); return json(res,200,{ok:true});
}
function findFileMessage(fileId) {
  for(const channelMessages of messages.values()) { const message=channelMessages.find(item=>item.file?.id===fileId); if(message) return message; }
  for(const thread of privateMessages.values()) { const message=thread.find(item=>item.file?.id===fileId); if(message) return message; }
  return null;
}
function findMessageById(messageId) {
  for(const channelMessages of messages.values()) { const message=channelMessages.find(item=>item.id===messageId); if(message) return message; }
  for(const thread of privateMessages.values()) { const message=thread.find(item=>item.id===messageId); if(message) return message; }
  return null;
}
async function sendFile(req,res,url) {
  const match=url.pathname.match(/^\/api\/file\/([0-9a-f-]{36})$/i);
  if(!match) { json(res,404,{error:'not found'}); return true; }
  const fileId=match[1]; const clientId=String(url.searchParams.get('client')||''); const token=String(url.searchParams.get('token')||'');
  const now=Date.now(); const ip=requestIp(req); pruneClients(now); pruneMessages(now);
  const connected=clients.get(clientId); const message=findFileMessage(fileId);
  if(!connected||connected.ip!==ip||!message||message.recalled||now-message.at>=retentionMs) { json(res,404,{error:'file unavailable'}); return true; }
  const canDownload=message.mode==='private'?(clientId===message.senderId||clientId===message.recipientId):connected.channel===message.channel;
  if(!canDownload) { json(res,403,{error:'file access denied'}); return true; }
  if(!message.file||token!==message.file.token) { json(res,403,{error:'invalid file token'}); return true; }
  if(message.mode==='private'&&clientId===message.recipientId&&!message.file.receivedAt) { message.file.receivedAt=now; message.cursor=++cursor; }
  let stat;
  try { stat=await fs.promises.stat(filePath(fileId)); } catch { json(res,410,{error:'file expired'}); return true; }
  const encoded=encodeURIComponent(message.file.name).replace(/['()*]/g,char=>'%'+char.charCodeAt(0).toString(16).toUpperCase());
  const imageType=previewImageType(message.file); const inlinePreview=url.searchParams.get('preview')==='1'&&!!imageType&&stat.size<=MAX_IMAGE_PREVIEW_BYTES;
  res.writeHead(200,{'Content-Type':inlinePreview?imageType:'application/octet-stream','Content-Length':stat.size,'Content-Disposition':`${inlinePreview?'inline':'attachment'}; filename*=UTF-8''${encoded}`,'Cache-Control':'private, no-store','X-Content-Type-Options':'nosniff'});
  const stream=fs.createReadStream(filePath(fileId)); stream.on('error',()=>res.destroy()); stream.pipe(res); return true;
}
function serve(req,res) {
  const url = new URL(req.url, 'http://localhost');
  if (req.method==='GET' && url.pathname==='/api/status') return json(res,200,{canAdmin:isLocalRequest(req),limit:MAX_CONNECTIONS,retentionMs,maxFileBytes,maxImagePreviewBytes:MAX_IMAGE_PREVIEW_BYTES});
  if (req.method==='POST' && url.pathname==='/api/admin/login') return body(req).then(data => { if(!isLocalRequest(req)) return json(res,403,{error:'local only'}); if(String(data.password||'')!==ADMIN_PASSWORD) return json(res,401,{error:'wrong password'}); const token=crypto.randomBytes(24).toString('hex'); adminTokens.set(token,{ip:requestIp(req),expiresAt:Date.now()+60*60*1000}); json(res,200,{token}); }).catch(error=>json(res,error.message==='body too large'?413:400,{error:error.message==='body too large'?'body too large':'invalid'}));
  if (req.method==='POST' && url.pathname==='/api/admin/channel') return body(req).then(data => { if(!getAdmin(req)) return json(res,403,{error:'admin required'}); const channel=channels.find(item=>item.id===data.id); const name=Array.from(String(data.name||'').trim()).slice(0,10).join(''); if(!channel||!name) return json(res,400,{error:'invalid channel'}); channel.name=name; persistConfig(); json(res,200,{channels}); }).catch(()=>json(res,400,{error:'invalid'}));
  if (req.method==='POST' && url.pathname==='/api/admin/settings') return body(req).then(data => {
    if(!getAdmin(req)) return json(res,403,{error:'admin required'});
    const retentionValue=String(data.retentionMinutes??'');
    const fileSizeValue=String(data.fileMegabytes??'');
    const digitsOnly=/^[0-9]+$/;
    const retentionMinutes=Number(retentionValue);
    const fileMegabytes=Number(fileSizeValue);
    const validRetention=digitsOnly.test(retentionValue)&&Number.isInteger(retentionMinutes)&&retentionMinutes>=MIN_RETENTION_MINUTES&&retentionMinutes<=MAX_RETENTION_MINUTES;
    const validFileSize=digitsOnly.test(fileSizeValue)&&Number.isInteger(fileMegabytes)&&fileMegabytes>=MIN_FILE_MEGABYTES&&fileMegabytes<=MAX_FILE_MEGABYTES;
    if(!validRetention||!validFileSize) return json(res,400,{error:'invalid settings'});
    retentionMs=retentionMinutes*60*1000;
    maxFileBytes=fileMegabytes*1024*1024;
    pruneMessages();
    cleanExpiredFilesOnDisk();
    persistConfig();
    json(res,200,{ok:true,retentionMs,maxFileBytes});
  }).catch(error=>json(res,error.message==='body too large'?413:400,{error:error.message==='body too large'?'body too large':'invalid'}));
  if (req.method==='GET' && url.pathname==='/api/admin/user') { if(!getAdmin(req)) return json(res,403,{error:'admin required'}); const clientId=String(url.searchParams.get('client')||''); const client=clients.get(clientId); if(!client) return json(res,404,{error:'offline'}); return json(res,200,{id:clientId,name:reservedNames.get(clientId)||'匿名用户',ip:client.ip,channel:client.channel,lastSeen:client.lastSeen,banned:isIpBanned(client.ip)}); }
  if (req.method==='GET' && url.pathname==='/api/admin/bans') { if(!getAdmin(req)) return json(res,403,{error:'admin required'}); return json(res,200,{bans:banList()}); }
  if (req.method==='POST' && url.pathname==='/api/admin/ban') return body(req).then(data => {
    if(!getAdmin(req)) return json(res,403,{error:'admin required'});
    const ip=String(data.ip||'').trim();
    if(!net.isIP(ip)) return json(res,400,{error:'invalid ip'});
    if(localAddresses.has(ip)) return json(res,400,{error:'cannot ban local address'});
    if(data.banned===false) bannedIps.delete(ip);
    else { bannedIps.set(ip,{at:Date.now()}); disconnectIp(ip); }
    persistConfig();
    json(res,200,{ok:true,bans:banList()});
  }).catch(error=>json(res,error.message==='body too large'?413:400,{error:error.message==='body too large'?'body too large':'invalid'}));
  if (req.method==='POST' && url.pathname==='/api/upload/init') return initializeUpload(req,res).catch(()=>{ if(!res.headersSent) json(res,500,{error:'upload init failed'}); });
  const uploadMatch=url.pathname.match(/^\/api\/upload\/([0-9a-f-]{36})(?:\/chunk|\/complete)?$/i);
  if(uploadMatch&&req.method==='PUT'&&url.pathname.endsWith('/chunk')) return receiveUploadChunk(req,res,url,uploadMatch[1]).catch(()=>{ if(!res.headersSent) json(res,500,{error:'chunk upload failed'}); });
  if(uploadMatch&&req.method==='POST'&&url.pathname.endsWith('/complete')) return completeUpload(req,res,uploadMatch[1]).catch(()=>{ if(!res.headersSent) json(res,500,{error:'upload finalize failed'}); });
  if(uploadMatch&&req.method==='DELETE'&&url.pathname===`/api/upload/${uploadMatch[1]}`) return cancelUpload(req,res,url,uploadMatch[1]).catch(()=>{ if(!res.headersSent) json(res,500,{error:'upload cancel failed'}); });
  if (req.method==='POST' && url.pathname==='/api/rtc/signal') return body(req).then(data=>{
    const clientId=String(data.id||''); const target=String(data.target||''); const connected=clients.get(clientId); const peer=clients.get(target); const ip=requestIp(req);
    if(!connected||connected.ip!==ip||!peer||!target||target===clientId||target.length>128||!data.signal||typeof data.signal!=='object') return json(res,403,{error:'invalid rtc peer'});
    queueRtcSignal(target,{from:clientId,signal:data.signal,at:Date.now()}); json(res,200,{ok:true});
  }).catch(()=>json(res,400,{error:'invalid'}));
  if (req.method==='POST' && url.pathname==='/api/direct-file') return body(req).then(data=>{
    const clientId=String(data.id||''); const peerId=String(data.peer||''); const transferId=String(data.transferId||''); const size=Number(data.size); const sha256=String(data.sha256||'').toLowerCase(); const now=Date.now(); const ip=requestIp(req); const sender=clients.get(clientId);
    if(!sender||sender.ip!==ip||!clients.has(peerId)||peerId===clientId||!/^[a-z0-9-]{16,64}$/i.test(transferId)) return json(res,403,{error:'invalid direct transfer'});
    if(!Number.isInteger(size)||size<=0||size>maxFileBytes||!/^[0-9a-f]{64}$/.test(sha256)) return json(res,400,{error:'invalid direct file'});
    const name=safeFileName(data.name); if(!name) return json(res,400,{error:'invalid file name'});
    const thread=getPrivateMessages(clientId,peerId,true); const reply=replySnapshot(thread,String(data.replyTo||''));
    if(reply===undefined) return json(res,400,{error:'invalid reply'});
    const slot=reserveSendSlot(sender,now); if(slot.retryAfter) return json(res,429,{error:'rate limit',retryAfter:slot.retryAfter});
    clients.set(clientId,{...sender,lastSeen:now,sentAt:slot.sentAt});
    const type=String(data.type||'application/octet-stream').replace(/[\r\n]/g,'').slice(0,100)||'application/octet-stream';
    const messageCursor=++cursor;
    const message={id:crypto.randomUUID(),cursor:messageCursor,createdCursor:messageCursor,at:now,mode:'private',channel:'private',senderId:clientId,recipientId:peerId,name:reservedNames.get(clientId)||sender.name||'匿名用户',text:'',file:{id:transferId,transferId,name,size,type,direct:true,sha256,receivedAt:now},reply,deliveredAt:now,readAt:null,recalled:false};
    thread.push(message); if(thread.length>MAX_MESSAGES) thread.splice(0,thread.length-MAX_MESSAGES).forEach(deleteMessageFile);
    json(res,201,{ok:true,message});
  }).catch(error=>json(res,error.message==='body too large'?413:400,{error:'invalid'}));
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
    const privateRead=existing?.privateRead||new Map();
    const channelRead=existing?.channelRead||new Map(channels.map(item=>[item.id,cursor]));
    clients.set(client,{...existing,lastSeen:now,channel,ip,name:assignedName,sentAt:existing?.sentAt||[],privateRead,channelRead});
    const since=Number(url.searchParams.get('since')) || 0;
    pruneMessages(now);
    let activeMessages=messages.get(channel);
    if(!peer) {
      const newestChannelMessage=activeMessages.reduce((latest,message)=>Math.max(latest,message.createdCursor||message.cursor||0),0);
      if(newestChannelMessage) channelRead.set(channel,Math.max(channelRead.get(channel)||0,newestChannelMessage));
    }
    let peerInfo=null;
    if(peer) {
      activeMessages=getPrivateMessages(client,peer);
      for(const message of activeMessages) if(message.recipientId===client&&!message.recalled) {
        let changed=false;
        if(!message.deliveredAt) { message.deliveredAt=now; changed=true; }
        if(!message.readAt) { message.readAt=now; changed=true; }
        if(changed) message.cursor=++cursor;
      }
      const newestIncoming=activeMessages.filter(message=>message.recipientId===client).reduce((latest,message)=>Math.max(latest,message.cursor),0);
      if(newestIncoming) privateRead.set(peer,Math.max(privateRead.get(peer)||0,newestIncoming));
      const peerRecord=clients.get(peer);
      peerInfo={id:peer,name:reservedNames.get(peer)||peerRecord?.name||'已离线用户',online:!!peerRecord};
    }
    const typing=[...clients.entries()].filter(([id,item])=>id!==client&&item.typingUntil>now&&(peer?(id===peer&&item.typingMode==='private'&&item.typingPeer===client):(item.typingMode==='channel'&&item.typingChannel===channel))).map(([id,item])=>reservedNames.get(id)||item.name||'匿名用户');
    return json(res,200,{cursor,messages:activeMessages.filter(m=>m.cursor>since),mode:peer?'private':'channel',peer:peerInfo,typing,rtcSignals:takeRtcSignals(client,now),privateUnread:privateUnreadFor(client),channelUnread:channelUnreadFor(client),privateActivity:privateActivityFor(client),online:clients.size,onlineByChannel:onlineByChannel(now),users:onlineUsers(now),channels,retentionMs,recallWindowMs:RECALL_WINDOW_MS,maxFileBytes,maxImagePreviewBytes:MAX_IMAGE_PREVIEW_BYTES,assignedName,limit:MAX_CONNECTIONS,renderBatch:RENDER_BATCH,pollInterval:POLL_HINT});
  }
  if (req.method==='POST' && url.pathname==='/api/typing') return body(req).then(data=>{
    const clientId=String(data.id||''); const peer=String(data.peer||''); const channel=getChannel(data.channel); const mode=data.mode==='private'?'private':'channel'; const now=Date.now(); const ip=requestIp(req); const connected=clients.get(clientId);
    if(!connected||connected.ip!==ip||!channel||peer.length>128||peer===clientId) return json(res,403,{error:'not connected'});
    if(mode==='private'&&(!peer||!clients.has(peer))) return json(res,404,{error:'peer offline'});
    clients.set(clientId,{...connected,lastSeen:now,typingUntil:data.active===false?0:now+2500,typingMode:mode,typingPeer:mode==='private'?peer:'',typingChannel:mode==='channel'?channel:''});
    json(res,200,{ok:true});
  }).catch(()=>json(res,400,{error:'invalid'}));
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
    const targetMessages=isPrivate?getPrivateMessages(client,peer,true):messages.get(channel);
    const reply=replySnapshot(targetMessages,String(data.replyTo||''));
    if(reply===undefined) return json(res,400,{error:'invalid reply'});
    const slot=reserveSendSlot(existing,now);
    if(slot.retryAfter) return json(res,429,{error:'rate limit',retryAfter:slot.retryAfter});
    const name=allocateName(client,data.name);
    clients.set(client,{...existing,lastSeen:now,channel,name,sentAt:slot.sentAt});
    const messageCursor=++cursor;
    const message={id:crypto.randomUUID(),cursor:messageCursor,createdCursor:messageCursor,at:now,mode:isPrivate?'private':'channel',channel:isPrivate?'private':channel,senderId:client,recipientId:isPrivate?peer:null,name,text:Array.from(data.text.trim()).slice(0,500).join(''),reply,deliveredAt:null,readAt:null,recalled:false};
    targetMessages.push(message);
    if(targetMessages.length>MAX_MESSAGES) targetMessages.splice(0,targetMessages.length-MAX_MESSAGES);
    json(res,201,{ok:true,name,message});
  }).catch(error=>json(res,error.message==='body too large'?413:400,{error:error.message==='body too large'?'body too large':'invalid'}));
  if (req.method==='POST' && url.pathname==='/api/message/recall') return body(req).then(data => {
    const client=String(data.id||''); const messageId=String(data.messageId||''); const now=Date.now(); const ip=requestIp(req);
    if(isIpBanned(ip)) return json(res,403,{error:'ip banned'});
    const connected=clients.get(client);
    if(!connected||connected.ip!==ip) return json(res,403,{error:'not connected'});
    const target=findMessageById(messageId);
    if(!target) return json(res,404,{error:'message not found'});
    if(target.senderId!==client) return json(res,403,{error:'not owner'});
    if(target.recalled) return json(res,409,{error:'already recalled'});
    if(now-target.at>RECALL_WINDOW_MS) return json(res,410,{error:'recall expired'});
    deleteMessageFile(target);
    target.recalled=true; target.recalledAt=now; target.text=''; target.cursor=++cursor;
    json(res,200,{ok:true,message:target});
  }).catch(error=>json(res,error.message==='body too large'?413:400,{error:error.message==='body too large'?'body too large':'invalid'}));
  if (req.method==='GET' && (url.pathname==='/' || url.pathname==='/index.html')) { const gzip=/\bgzip\b/.test(String(req.headers['accept-encoding']||'')); const page=gzip?PAGE_GZIP:PAGE; res.writeHead(200,{'Content-Type':'text/html; charset=utf-8','Content-Length':Buffer.byteLength(page),'Cache-Control':'no-cache','Vary':'Accept-Encoding',...(gzip?{'Content-Encoding':'gzip'}:{})}); return res.end(page); }
  json(res,404,{error:'not found'});
}
setInterval(pruneClients,5000);
setInterval(pruneMessages,1000);
setInterval(cleanExpiredTokens,60*1000);
setInterval(cleanExpiredFilesOnDisk,60*1000);
setInterval(cleanUploadSessions,60*1000);
setInterval(cleanRtcSignals,10*1000);
cleanExpiredFilesOnDisk();
process.once('exit',()=>{ for(const fileId of ownedFileIds) { try { fs.rmSync(filePath(fileId),{force:true}); } catch {} } });
process.once('SIGINT',()=>process.exit(0));
process.once('SIGTERM',()=>process.exit(0));
const localIPv4Addresses = [...new Set(Object.values(os.networkInterfaces()).flat().filter(item => item && !item.internal && (item.family === 'IPv4' || item.family === 4)).map(item => item.address))];
function openLocalPage(url) {
  let command=''; let args=[];
  if(process.platform==='win32') { command=process.env.ComSpec||'cmd.exe'; args=['/d','/c','start','',url]; }
  else if(process.platform==='darwin') { command='open'; args=[url]; }
  else { command='xdg-open'; args=[url]; }
  try {
    const child=spawn(command,args,{detached:true,stdio:'ignore',windowsHide:true});
    child.once('error',()=>console.warn(`Unable to open browser automatically. Open ${url} manually.`));
    child.unref();
  } catch { console.warn(`Unable to open browser automatically. Open ${url} manually.`); }
}
const server=http.createServer(serve);
server.requestTimeout=MAX_UPLOAD_DURATION_MS;
server.listen(PORT,'0.0.0.0',()=>{
  const localUrl=`http://localhost:${PORT}`;
  console.log(`LAN chat running on ${localUrl}`);
  localIPv4Addresses.forEach(address => console.log(`LAN access: http://${address}:${PORT}`));
  if(!browserOpenDisabled) openLocalPage(localUrl);
});

/* PAGE_START
<!doctype html>
<html lang="zh-CN">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>LAN CHAT</title>
  <link rel="icon" type="image/svg+xml" href="data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 64 64'%3E%3Cdefs%3E%3ClinearGradient id='g' x1='0' y1='0' x2='1' y2='1'%3E%3Cstop stop-color='%23f8fcff'/%3E%3Cstop offset='1' stop-color='%23b9dcf6'/%3E%3C/linearGradient%3E%3C/defs%3E%3Crect width='64' height='64' rx='19' fill='url(%23g)'/%3E%3Ccircle cx='32' cy='32' r='5' fill='%230a84ff'/%3E%3Cpath d='M21 22a14 14 0 0 0 0 20M16 17a21 21 0 0 0 0 30M43 22a14 14 0 0 1 0 20M48 17a21 21 0 0 1 0 30' fill='none' stroke='%230a84ff' stroke-width='4' stroke-linecap='round'/%3E%3C/svg%3E">
  <style>
:root{--ink:#17211b;--muted:#718078;--line:#d9e0d9;--paper:#eef1eb;--lime:#d9ff55;--coral:#ff7059;--white:#fffef9;--dark:#1c251f;--amber:#ffb347;--font:'Microsoft YaHei','PingFang SC',sans-serif}
*{box-sizing:border-box}
html,body{height:100%;min-height:0}
body{margin:0;color:var(--ink);background:var(--paper);font-family:var(--font);font-variant-numeric:tabular-nums;overflow:hidden}
button,input{font:inherit}
.shell{width:100%;height:100vh;height:100dvh;min-height:0;overflow:hidden;display:grid;grid-template-rows:64px minmax(0,1fr);position:relative}
header{display:flex;justify-content:space-between;align-items:center;padding:0 24px;background:var(--dark);color:var(--white);border-bottom:1px solid #354239}
.brand{display:flex;align-items:center;gap:12px;font:700 17px var(--font);letter-spacing:2px}
.status{display:flex;gap:9px;align-items:center;color:#b7c2ba;font:12px var(--font)}
.pulse{width:8px;height:8px;background:#51ad72;border-radius:50%;box-shadow:0 0 0 5px #51ad7225}
main{min-height:0;overflow:hidden;display:grid;grid-template-columns:minmax(260px,22vw) minmax(480px,1fr) minmax(210px,16vw)}
.profile-panel{min-width:0;min-height:0;overflow-y:auto;padding:32px 26px;background:#f7f8f4;border-right:1px solid var(--line);display:flex;flex-direction:column;gap:20px}
.kicker{color:var(--coral);font:700 11px var(--font);letter-spacing:2px}
h1{margin:13px 0 14px;font-size:clamp(34px,3vw,48px);line-height:1.02;font-weight:400;letter-spacing:0}
.intro{max-width:260px;color:var(--muted);font-size:13px;line-height:1.75}
.identity{border:1px solid var(--ink);background:var(--white);padding:14px;display:grid;grid-template-columns:52px minmax(0,1fr);gap:12px;align-items:center;box-shadow:5px 5px 0 var(--lime)}
.avatar{width:52px;height:52px;border:1px solid var(--ink);display:grid;place-items:center;font-size:26px;background:var(--lime)}
.identity small{display:block;color:var(--muted);font:10px var(--font);margin-bottom:5px}
.identity input{width:100%;min-width:0;padding:2px 0;border:0;border-bottom:1px solid transparent;background:transparent;font-size:16px;color:var(--ink);outline:none}
.identity input:focus{border-bottom-color:var(--coral);box-shadow:none}
.user-directory{min-height:140px;flex:1 1 0;display:flex;flex-direction:column;gap:9px}
.user-search{width:100%;height:36px;flex:none;padding:8px 10px;font-size:12px}
.user-list{min-height:0;flex:1;overflow-x:hidden;overflow-y:auto;display:flex;flex-direction:column;gap:5px;padding-right:3px;scrollbar-width:thin}
.user-entry{display:grid;grid-template-columns:minmax(0,1fr) auto;gap:4px}
.user-row{width:100%;height:38px;min-width:0;padding:0 9px;display:grid;grid-template-columns:24px minmax(0,1fr) auto auto;gap:8px;align-items:center;border-color:var(--line);background:transparent;font-weight:400}
.user-row:hover{transform:none;box-shadow:none;border-color:var(--ink);background:var(--white)}
.user-row.active{border-color:var(--ink);background:var(--dark);color:var(--white)}
.user-row.self{cursor:default}
.user-row-avatar{font-size:16px}
.user-row-name{overflow:hidden;text-overflow:ellipsis;white-space:nowrap;text-align:left;font-size:12px}
.user-row-channel{color:var(--muted);font-size:9px}
.unread-dot{min-width:17px;height:17px;padding:0 4px;display:grid;place-items:center;border-radius:9px;background:#e53935;color:white;font:700 9px var(--font);box-shadow:0 0 0 2px #e5393520}
.user-admin-button{width:34px;min-width:34px;height:38px;padding:0;border-color:var(--line);background:var(--amber);font-size:13px}
.user-admin-button:hover{transform:none;box-shadow:none}
.user-empty{padding:16px 4px;color:var(--muted);text-align:center;font-size:11px}
.rules{border-top:1px solid var(--line);padding-top:16px;color:var(--muted);font:11px/1.8 var(--font)}
.rules b{color:var(--ink);font-weight:400}
.chat{min-width:0;min-height:0;height:100%;overflow:hidden;background:var(--white);display:grid;grid-template-rows:76px minmax(0,1fr) 76px}
.chat-top{display:flex;justify-content:space-between;align-items:center;padding:0 26px;border-bottom:1px solid var(--line)}
.chat-title{font-size:25px}
.mobile-channel-select{display:none;height:38px;max-width:150px;border:1px solid var(--ink);background:var(--white);padding:0 10px;color:var(--ink);font-family:var(--font)}
.mobile-users-toggle,.mobile-users-close{display:none}
.messages{position:relative;padding:0;overflow:auto;scrollbar-color:#bdc7bf transparent;scrollbar-width:thin;background:linear-gradient(180deg,#ffffff 0%,#fbfaf6 100%)}
.messages-spacer{position:relative;width:100%}
.messages-window{position:absolute;left:0;right:0;top:0;padding:24px 26px;display:flex;flex-direction:column;gap:16px;will-change:transform}
.empty{color:var(--muted);margin:auto;text-align:center;font-size:14px;line-height:1.8;padding:40px 20px}
.message{display:grid;grid-template-columns:38px minmax(0,1fr);grid-template-areas:'avatar meta' 'avatar bubble';column-gap:12px;row-gap:4px;align-items:start;max-width:940px;width:100%}
.message-avatar{grid-area:avatar;width:38px;height:38px;display:grid;place-items:center;border:1px solid var(--line);background:#e7eee1;font-size:18px;user-select:none;border-radius:10px}
.message-meta{grid-area:meta;display:flex;align-items:baseline;gap:10px}
.message-name{font:700 11px var(--font);color:var(--coral);letter-spacing:1px}
.message-bubble{position:relative;grid-area:bubble;padding:10px 14px 38px;border:1px solid var(--line);border-radius:14px;background:#f4f6f2;box-shadow:2px 3px 0 #dfe7de;font-size:16px;line-height:1.6;overflow-wrap:anywhere;white-space:pre-wrap;width:fit-content;max-width:50%;min-width:150px}
.message-text{display:block}
.message-file{min-width:230px;max-width:360px;display:grid;grid-template-columns:minmax(0,1fr) auto;grid-template-areas:'name download' 'meta download';gap:1px 12px;align-items:center;white-space:normal}
.message-file[hidden]{display:none}
.file-name{grid-area:name;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-size:14px;font-weight:700}
.file-meta{grid-area:meta;color:var(--muted);font-size:10px}
.file-download{grid-area:download;min-width:54px;height:32px;padding:0 10px;display:inline-flex;align-items:center;justify-content:center;border:1px solid var(--ink);border-radius:8px;background:var(--white);color:var(--ink);font:700 11px var(--font);text-decoration:none}
.file-download:hover{background:var(--dark);color:var(--white)}
.message-footer{position:absolute;left:8px;right:8px;bottom:6px;display:flex;align-items:center}
.message-action{flex:1 1 0;width:auto;min-width:0;height:24px;padding:0;border:0;border-radius:6px;background:transparent;color:var(--muted);box-shadow:none;font:14px/1 var(--font)}
.message-action:hover{transform:none;box-shadow:none;background:#dde4dc;color:var(--ink)}
.message-action:disabled{visibility:hidden}
.message-footer .message-action[hidden]{display:block;visibility:hidden}
.message.recalled .message-bubble{background:#ecefeb;border-style:dashed;box-shadow:none;color:var(--muted);font-style:italic}
.message-time{flex:1 1 0;color:#718078;font:700 11px var(--font);line-height:24px;font-variant-numeric:tabular-nums;white-space:nowrap;text-align:center}
.message.self{grid-template-columns:minmax(0,1fr) 38px;grid-template-areas:'meta avatar' 'bubble avatar';justify-items:end;margin-left:auto}
.message.self .message-meta{flex-direction:row-reverse}
.message.self .message-name{color:#2d6a4f}
.message.self .message-bubble{background:linear-gradient(180deg,var(--lime) 0%,#c9f23d 100%);border-color:#a8c93b;box-shadow:3px 4px 0 #1c251f}
.message.self .message-avatar{background:var(--amber)}
.message.is-new .message-bubble{animation:rise .28s ease-out}
.composer{position:relative;z-index:5;overflow:visible;display:flex;align-items:stretch;gap:10px;padding:14px 26px;border-top:1px solid var(--line);background:#f7f8f4}
.file-toggle{width:48px;height:48px;min-width:48px;flex:0 0 48px;padding:0;background:var(--white);font-size:18px}
.file-toggle[hidden]{display:none}
.file-input{display:none}
input{flex:1;min-width:0;height:48px;border:1px solid #aab5ad;background:var(--white);padding:13px 15px;color:var(--ink);outline:none}
input:focus{border-color:var(--ink);box-shadow:3px 3px 0 var(--lime)}
button{min-width:92px;height:48px;border:1px solid var(--ink);background:var(--lime);color:var(--ink);padding:0 18px;cursor:pointer;font:700 12px var(--font);transition:transform .15s,box-shadow .15s}
button:hover{transform:translate(-2px,-2px);box-shadow:4px 4px 0 var(--ink)}
button:disabled{opacity:.5;cursor:not-allowed;transform:none;box-shadow:none}
.room-panel{min-width:0;min-height:0;overflow-y:auto;padding:28px 20px;background:var(--paper);border-left:1px solid var(--line);display:flex;flex-direction:column;gap:22px}
.room-panel h2{margin:0;font:700 11px var(--font);letter-spacing:2px}
.channel-list{display:flex;flex-direction:column;gap:7px}
.channel-button{width:100%;height:44px;min-width:0;padding:0 10px;display:flex;align-items:center;justify-content:space-between;border-color:var(--line);background:transparent;font-family:var(--font);font-weight:400}
.channel-button:hover{transform:none;box-shadow:none;border-color:var(--ink)}
.channel-button.active{background:var(--dark);color:var(--white);border-color:var(--dark)}
.channel-count{min-width:24px;text-align:right;color:var(--muted)}
.channel-button.active .channel-count{color:var(--lime)}
.room-admin-entry{margin-top:auto;display:flex;flex-direction:column;gap:10px}
.admin-status{font:11px/1.6 var(--font);color:var(--muted)}
.admin-status b{color:#2d6a4f}
.fab-admin{position:fixed;right:20px;bottom:20px;z-index:9;min-width:120px;height:42px;background:var(--amber);box-shadow:5px 5px 0 var(--ink);border-radius:21px;display:none}
.fab-admin:not([hidden]){display:inline-flex;align-items:center;justify-content:center;gap:6px}
.fab-admin::before{content:'';display:inline-block;width:8px;height:8px;border-radius:50%;background:var(--coral)}
.fab-admin.verified::before{background:#2d6a4f}
.modal-backdrop{position:fixed;inset:0;z-index:20;display:grid;place-items:center;padding:20px;background:#17211bcc;backdrop-filter:blur(2px)}
.modal-backdrop[hidden]{display:none}
.modal{width:min(460px,100%);padding:22px;border:1px solid var(--ink);background:var(--white);box-shadow:7px 7px 0 var(--lime)}
.modal.admin-modal-wide{width:min(460px,100%);max-height:calc(100dvh - 40px);overflow:auto}
.modal.admin-modal-wide.tools-open{width:min(1080px,100%)}
.modal h2{margin:0 0 18px;font-size:22px;font-weight:400}
.modal input,.modal select{width:100%;margin-bottom:12px}
.modal-actions{display:flex;justify-content:flex-end;gap:8px}
.modal-actions button{height:40px}
.admin-tools-layout{display:grid;grid-template-columns:minmax(320px,1.15fr) minmax(230px,.85fr) minmax(280px,1fr);gap:14px;align-items:start;margin-bottom:18px}
.admin-tool-panel{min-width:0;padding:16px;border:1px solid var(--line);border-radius:18px;background:rgba(255,255,255,.3)}
.admin-tool-panel h3{margin:0 0 13px;font:700 12px var(--font);letter-spacing:1.4px}
.admin-channels{display:flex;flex-direction:column;gap:10px;margin:0}
.admin-channel-row{display:grid;grid-template-columns:75px 1fr 60px;gap:8px;align-items:center;font-size:13px}
.admin-channel-row input{height:38px;margin:0}
.admin-channel-row button{min-width:0;height:38px;padding:0 8px}
.admin-settings{display:flex;flex-direction:column;gap:14px}
.admin-setting-row{display:grid;gap:7px;color:var(--muted);font-size:12px}
.admin-setting-row input{height:40px;margin:0;padding:0 12px;border:1px solid var(--line);border-radius:12px;color:var(--ink);background:rgba(255,255,255,.72);outline:none;font:600 13px var(--font)}
.admin-setting-row input:focus{border-color:var(--ios-blue,#268ee6);box-shadow:0 0 0 3px rgba(10,132,255,.12)}
.admin-settings-save{width:100%;height:40px;margin-top:2px}
.admin-settings-note{margin:0;color:var(--muted);font:11px/1.6 var(--font)}
.admin-ban-tools{margin:0}
.admin-ban-entry{display:grid;grid-template-columns:minmax(0,1fr) 72px;gap:8px}
.admin-ban-entry input,.admin-ban-entry button{height:40px;margin:0}
.admin-ban-entry button{min-width:0;padding:0 8px}
.banned-list{max-height:126px;overflow:auto;margin-top:10px;display:flex;flex-direction:column;gap:5px}
.banned-row{display:grid;grid-template-columns:minmax(0,1fr) 60px;gap:8px;align-items:center;font:12px var(--font)}
.banned-row button{min-width:0;height:32px;padding:0 6px;background:var(--paper)}
.banned-empty{color:var(--muted);font-size:11px;padding:5px 0}
.user-detail{color:var(--muted);font:14px/1.8 var(--font)}
.user-modal-actions{align-items:center;justify-content:space-between;margin-top:14px}
.user-modal-actions button{min-width:92px}
@media (max-width:900px){.admin-tools-layout{grid-template-columns:repeat(2,minmax(0,1fr))}
.admin-ban-tools{grid-column:1/-1}
}
@media (max-width:620px){.modal.admin-modal-wide{max-height:calc(100dvh - 20px);padding:16px}
.admin-tools-layout{grid-template-columns:1fr}
.admin-ban-tools{grid-column:auto}
}
.user-detail b{color:var(--ink);font-weight:400}
.metric{padding:18px 0;border-top:1px solid #cbd3cc}
.metric-label{display:block;margin-bottom:8px;color:var(--muted);font:10px var(--font)}
.metric-value{font-size:29px;line-height:1}
.online-value::before{content:'';display:inline-block;width:8px;height:8px;margin-right:9px;border-radius:50%;background:#51ad72;vertical-align:4px}
.sync{color:var(--muted);font:10px/1.7 var(--font)}
.sync::before{content:'SYNC STATUS';display:block;color:var(--ink);margin-bottom:7px}
.blocker{position:fixed;inset:0;z-index:30;display:grid;place-items:center;background:#17211bf0;color:var(--white)}
.blocker[hidden]{display:none}
.blocker-card{width:min(520px,92vw);padding:28px;border:1px solid var(--lime);background:#111915;box-shadow:8px 8px 0 #000}
.blocker-card h2{margin:0 0 12px;font-size:26px;color:var(--lime);letter-spacing:1px}
.blocker-card p{margin:0 0 18px;color:#cfd7d1;line-height:1.75;font-family:var(--font);font-size:15px}
.blocker-meta{display:flex;justify-content:space-between;color:#8a9891;font:12px var(--font);margin-top:18px}
.toast-host{position:fixed;z-index:60;top:20px;left:50%;width:min(420px,calc(100vw - 32px));transform:translateX(-50%);display:flex;justify-content:center;pointer-events:none}
.toast-message{--toast-color:#4f718c;width:max-content;max-width:100%;min-width:280px;min-height:44px;padding:10px 16px;display:flex;align-items:center;justify-content:center;gap:10px;border:1px solid #d8dee4;border-radius:8px;background:#fff;color:#44515b;box-shadow:0 6px 22px #17211b24;font:13px/1.5 var(--font);opacity:0;transform:translateY(-14px);transition:opacity .18s ease,transform .18s ease}
.toast-message.visible{opacity:1;transform:translateY(0)}
.toast-message.success{--toast-color:#4d9b69;border-color:#c9e7d3;background:#f1faf4;color:#356d49}
.toast-message.warning{--toast-color:#d49632;border-color:#f0d7ad;background:#fff8eb;color:#94651f}
.toast-message.error{--toast-color:#d95b57;border-color:#efc5c3;background:#fff2f1;color:#a5423e}
.toast-icon{width:18px;height:18px;flex:0 0 18px;display:grid;place-items:center;border:1px solid currentColor;border-radius:50%;color:var(--toast-color);font:700 11px/1 var(--font)}
.toast-text{min-width:0;overflow-wrap:anywhere}
@keyframes rise{from{opacity:0;transform:translateY(6px)}
to{opacity:1;transform:none}
}
@media (max-width:1000px){main{grid-template-columns:220px minmax(0,1fr)}
.room-panel{display:none}
.mobile-channel-select{display:block}
.chat-title{display:none}
}
@media (max-width:700px){body{overflow:hidden}
.shell{height:100vh;height:100dvh;min-height:0;grid-template-rows:56px minmax(0,1fr)}
header{padding:0 16px}
main{height:100%;min-height:0;overflow:hidden;display:grid;grid-template-columns:1fr;grid-template-rows:auto minmax(0,1fr)}
.profile-panel{overflow:hidden;padding:12px 16px;border-right:0;border-bottom:1px solid var(--line);display:grid;grid-template-columns:minmax(0,1fr) auto;gap:12px;align-items:center}
.profile-panel>div:first-child,.user-directory,.rules{display:none}
.identity{width:min(100%,280px);padding:8px 10px;grid-template-columns:42px minmax(0,1fr);box-shadow:3px 3px 0 var(--lime)}
.avatar{width:42px;height:42px;font-size:22px}
.chat{height:100%;min-height:0;grid-template-rows:60px minmax(0,1fr) 70px}
.chat-top,.messages-window{padding-left:16px;padding-right:16px}
.composer{padding:12px 16px}
button{min-width:70px;padding:0 12px}
.file-toggle{width:48px;min-width:48px;flex-basis:48px;padding:0}
.mobile-channel-select{max-width:120px}
.message-bubble{width:100%}
.message-file{min-width:0;width:100%}
.toast-host{top:12px}
.toast-message{min-width:0;width:100%}
.fab-admin{right:14px;bottom:14px;min-width:108px;height:40px}
}
@media (max-width:700px){.chat-top{gap:8px}
.mobile-channel-select{flex:1 1 auto;min-width:0;max-width:none}
.mobile-users-toggle{position:relative;flex:0 0 auto;min-width:64px;height:38px;padding:0 10px;display:inline-flex;align-items:center;justify-content:center;gap:5px;background:var(--white)}
.mobile-unread-count{min-width:17px;height:17px;padding:0 4px;display:grid;place-items:center;border-radius:9px;background:#e53935;color:#fff;font:700 9px var(--font)}
.mobile-unread-count[hidden]{display:none}
body.mobile-users-open .profile-panel{position:fixed;z-index:18;inset:56px 0 0;width:100%;min-height:0;padding:16px;overflow:hidden;display:flex;flex-direction:column;align-items:stretch;gap:14px;border:0;background:#f7f8f4}
body.mobile-users-open .profile-panel .mobile-users-close{width:100%;height:40px;min-height:40px;flex:none;display:block;background:var(--dark);color:var(--white)}
body.mobile-users-open .profile-panel .identity{width:100%;max-width:none;flex:none}
body.mobile-users-open .profile-panel .user-directory{width:100%;min-height:0;flex:1 1 0;display:flex}
body.mobile-users-open .profile-panel .user-list{padding-bottom:10px}
body.mobile-users-open .profile-panel .user-row{height:44px}
}
:root{--lan-dark:#090a09;--lan-dark-2:#101210;--surface:#151815;--surface-2:#1b1f1b;--bone:#edeadd;--acid:#c8ff36;--signal:#ff5a3d;--cyan:#8be9df;--mist:#899087;--hair:rgba(237,234,221,.13);--hair-hot:rgba(200,255,54,.32);--ink:var(--bone);--muted:var(--mist);--line:var(--hair);--paper:var(--lan-dark);--lime:var(--acid);--coral:var(--signal);--white:var(--bone);--dark:var(--lan-dark);--amber:#ffb84a;--font:'Segoe UI Variable','PingFang SC','Microsoft YaHei',sans-serif;--display:'Arial Narrow','Segoe UI Variable Display','PingFang SC',sans-serif;--mx:72%;--my:22%}
*{border-radius:0}
html{background:var(--lan-dark)}
body{color:var(--bone);background:var(--lan-dark);cursor:default}
body::before{content:'';position:fixed;inset:0;z-index:0;pointer-events:none;background:radial-gradient(560px circle at var(--mx) var(--my),rgba(200,255,54,.09),transparent 62%),radial-gradient(480px circle at 18% 82%,rgba(255,90,61,.07),transparent 65%);transition:background .12s linear}
::selection{color:var(--lan-dark);background:var(--acid)}
.lucide{width:18px;height:18px;flex:0 0 auto;fill:none;stroke:currentColor;stroke-width:1.7;stroke-linecap:round;stroke-linejoin:round}
.shell{isolation:isolate;z-index:1;grid-template-rows:76px minmax(0,1fr);background:linear-gradient(90deg,transparent 0 33.333%,rgba(255,255,255,.015) 33.333% 66.666%,transparent 66.666%)}
header{position:relative;padding:0 26px;border-color:var(--hair);background:rgba(9,10,9,.78);backdrop-filter:blur(18px)}
header::after{content:'';position:absolute;right:0;bottom:-1px;width:38%;height:1px;background:linear-gradient(90deg,transparent,var(--acid))}
.brand{gap:14px;color:var(--bone);font:650 13px var(--font);letter-spacing:.28em}
.brand-lockup{display:flex;align-items:center;gap:14px}
.brand-icon{width:34px;height:34px;display:grid;place-items:center;color:var(--lan-dark);background:var(--acid);transform:rotate(-7deg);transition:transform .5s cubic-bezier(.2,.8,.2,1)}
.brand-icon .lucide{width:18px;height:18px;stroke-width:2}
.brand:hover .brand-icon{transform:rotate(8deg) scale(1.08)}
.brand-index{margin-left:4px;color:#5d635d;font-size:9px;letter-spacing:.1em}
.status{gap:11px;color:#7f867e;font-size:10px;letter-spacing:.15em;text-transform:uppercase}
.pulse{position:relative;width:7px;height:7px;background:var(--acid);box-shadow:none}
.pulse::after{content:'';position:absolute;inset:-5px;border:1px solid var(--acid);border-radius:50%;animation:signal-pulse 2.3s ease-out infinite}
main{position:relative;grid-template-columns:minmax(250px,20vw) minmax(460px,1fr) minmax(220px,17vw);background:linear-gradient(rgba(237,234,221,.025) 1px,transparent 1px),linear-gradient(90deg,rgba(237,234,221,.025) 1px,transparent 1px);background-size:44px 44px}
.profile-panel{position:relative;padding:30px 24px 22px;gap:22px;border-color:var(--hair);background:rgba(12,14,12,.9);scrollbar-color:#3b413b transparent}
.profile-panel::after{content:'01';position:absolute;right:-2px;top:8px;color:rgba(237,234,221,.045);font:800 clamp(90px,9vw,150px)/1 var(--display);letter-spacing:-.08em;writing-mode:vertical-rl;pointer-events:none}
.kicker{display:flex;align-items:center;gap:9px;color:var(--acid);font-size:9px;letter-spacing:.28em}
.kicker::before{content:'';width:26px;height:1px;background:currentColor}
h1{position:relative;z-index:1;max-width:240px;margin:20px 0 16px;color:var(--bone);font:650 clamp(38px,3.4vw,62px)/.86 var(--display);letter-spacing:-.075em}
.intro{max-width:220px;color:#797f78;font-size:11px;line-height:1.8;letter-spacing:.05em}
.identity{position:relative;z-index:2;padding:10px;grid-template-columns:46px minmax(0,1fr);gap:10px;border-color:var(--hair);background:rgba(237,234,221,.035);box-shadow:none;overflow:hidden;transition:border-color .25s,background .25s,transform .25s}
.identity::before{content:'';position:absolute;inset:auto 0 0;height:2px;background:linear-gradient(90deg,var(--acid),transparent 72%);transform:scaleX(.18);transform-origin:left;transition:transform .35s ease}
.identity:hover{border-color:var(--hair-hot);background:rgba(200,255,54,.045);transform:translateY(-2px)}
.identity:hover::before{transform:scaleX(1)}
.avatar{width:46px;height:46px;color:var(--lan-dark);border:0;background:var(--acid)}
.avatar .lucide{width:22px;height:22px;stroke-width:1.8}
.identity small{margin-bottom:3px;color:#6c736b;font-size:8px;letter-spacing:.18em;text-transform:uppercase}
.identity input{height:auto;color:var(--bone);font-size:13px;font-weight:600;letter-spacing:.04em}
.identity input:focus{border-color:var(--acid);box-shadow:none}
.user-directory{position:relative;z-index:2;gap:10px}
.search-shell{position:relative}
.search-shell .lucide{position:absolute;left:11px;top:50%;width:14px;height:14px;color:#687068;transform:translateY(-50%);pointer-events:none}
.user-search{height:38px;padding:8px 10px 8px 34px}
.user-list{gap:3px}
.user-entry{gap:3px}
.user-row{height:41px;padding:0 10px;grid-template-columns:20px minmax(0,1fr) auto auto;gap:9px;border-color:transparent;background:transparent;color:#aeb4ac}
.user-row:hover{border-color:var(--hair);background:rgba(237,234,221,.04);color:var(--bone)}
.user-row.active{border-color:var(--acid);color:var(--lan-dark);background:var(--acid)}
.user-row-avatar{width:20px;height:20px;display:grid;place-items:center}
.user-row-avatar .lucide{width:15px;height:15px}
.user-row-name{font-size:11px}
.user-row-channel{color:#626962;font-size:8px;letter-spacing:.08em}
.user-row.active .user-row-channel{color:rgba(9,10,9,.55)}
.unread-dot{border-radius:0;background:var(--signal);box-shadow:none}
.user-admin-button{width:38px;min-width:38px;height:41px;color:var(--lan-dark);border:0;background:var(--amber)}
.user-admin-button .lucide{width:14px;height:14px}
.chat{position:relative;grid-template-rows:94px minmax(0,1fr) 88px;border-right:1px solid var(--hair);background:rgba(12,13,12,.76);backdrop-filter:blur(6px)}
.chat::before{content:'LAN';position:absolute;z-index:0;right:-1.8vw;top:13%;color:rgba(237,234,221,.023);font:900 clamp(100px,16vw,260px)/.7 var(--display);letter-spacing:-.09em;writing-mode:vertical-rl;pointer-events:none}
.chat-top{position:relative;z-index:2;padding:0 28px;border-color:var(--hair);background:rgba(9,10,9,.46)}
.chat-title{color:var(--bone);font:650 clamp(26px,2.4vw,38px)/1 var(--display);letter-spacing:-.055em}
.messages{z-index:1;background:transparent;scrollbar-color:#3b423b transparent}
.messages-window{padding:28px 30px 34px;gap:20px}
.empty{position:relative;color:#6f766e;font-size:12px;line-height:1.9;letter-spacing:.08em}
.empty::before{content:'';display:block;width:42px;height:1px;margin:0 auto 16px;background:var(--acid);box-shadow:0 6px 20px var(--acid)}
.message{grid-template-columns:34px minmax(0,1fr);column-gap:11px;max-width:980px}
.message-avatar{width:34px;height:34px;color:var(--bone);border-color:var(--hair);border-radius:0;background:var(--surface)}
.message-avatar .lucide{width:16px;height:16px}
.message-meta{gap:9px}
.message-name{color:var(--signal);font-size:9px;letter-spacing:.16em;text-transform:uppercase}
.message-bubble{min-width:160px;max-width:min(64%,620px);padding:12px 15px 35px;color:#d6d5cb;border-color:var(--hair);border-radius:0;background:rgba(237,234,221,.045);box-shadow:none;font-size:14px;line-height:1.7;backdrop-filter:blur(8px)}
.message-bubble::before{content:'';position:absolute;left:-1px;top:-1px;width:18px;height:1px;background:var(--signal)}
.message.self .message-bubble{color:var(--lan-dark);border-color:var(--acid);background:var(--acid);box-shadow:8px 8px 0 rgba(200,255,54,.1)}
.message.self .message-bubble::before{left:auto;right:-1px;width:32px;background:var(--lan-dark)}
.message.self .message-avatar{color:var(--lan-dark);border-color:var(--cyan);background:var(--cyan)}
.message.self .message-name{color:var(--cyan)}
.message.self{grid-template-columns:minmax(0,1fr) 34px}
.message-footer{bottom:6px}
.message-action{height:22px;color:#737a72}
.message-action .lucide{width:13px;height:13px;margin:auto}
.message.self .message-action,.message.self .message-time{color:rgba(9,10,9,.55)}
.message-action:hover{color:var(--bone);background:rgba(237,234,221,.08)}
.message.self .message-action:hover{color:var(--lan-dark);background:rgba(9,10,9,.1)}
.message-time{color:#666d66;font-size:9px;letter-spacing:.08em}
.message.recalled .message-bubble{color:#6e756e;border-style:solid;background:transparent}
.message-file{min-width:250px}
.file-download{gap:6px;color:var(--bone);border-color:var(--hair);border-radius:0;background:transparent}
.file-download:hover{color:var(--lan-dark);background:var(--acid)}
.composer{z-index:6;gap:8px;padding:18px 28px 20px;border-color:var(--hair);background:rgba(9,10,9,.84);backdrop-filter:blur(18px)}
input,.mobile-channel-select{color:var(--bone);border-color:var(--hair);background:rgba(237,234,221,.035);caret-color:var(--acid)}
input::placeholder{color:#555c55}
input:focus{border-color:var(--acid);box-shadow:0 0 0 1px rgba(200,255,54,.15),0 0 32px rgba(200,255,54,.05)}
#message{height:50px;padding:13px 16px}
button{height:50px;color:var(--lan-dark);border-color:var(--acid);background:var(--acid);letter-spacing:.08em;transition:transform .25s cubic-bezier(.2,.8,.2,1),box-shadow .25s,background .25s,color .25s}
button:hover{transform:translateY(-2px);box-shadow:0 8px 22px rgba(200,255,54,.12)}
#send{min-width:112px;display:inline-flex;align-items:center;justify-content:center;gap:10px}
#send .lucide{width:15px;height:15px;transition:transform .25s ease}
#send:hover .lucide{transform:translate(3px,-3px)}
.file-toggle{width:50px;min-width:50px;height:50px;padding:0;display:grid;place-items:center;color:var(--bone);border-color:var(--hair);background:transparent}
.file-toggle:hover{color:var(--lan-dark);border-color:var(--acid);background:var(--acid)}
.file-toggle .lucide{width:17px;height:17px}
.room-panel{position:relative;padding:30px 20px 22px;gap:24px;border:0;background:rgba(9,10,9,.9);scrollbar-color:#3b413b transparent}
.room-panel h2{display:flex;align-items:center;gap:9px;color:#a8aea6;font-size:9px;letter-spacing:.24em}
.room-panel h2 .lucide{width:13px;height:13px;color:var(--acid)}
.channel-list{gap:4px}
.channel-button{position:relative;height:47px;padding:0 11px;color:#8b928a;border-color:transparent;background:transparent;font-size:11px;overflow:hidden}
.channel-button::before{content:'';position:absolute;left:0;top:0;bottom:0;width:2px;background:var(--acid);transform:scaleY(0);transition:transform .25s}
.channel-button:hover{color:var(--bone);border-color:var(--hair);background:rgba(237,234,221,.03)}
.channel-button.active{color:var(--bone);border-color:var(--hair);background:rgba(237,234,221,.055)}
.channel-button.active::before{transform:scaleY(1)}
.channel-count{color:#5e655e}
.channel-button.active .channel-count{color:var(--acid)}
.metric{padding:20px 0;border-color:var(--hair)}
.metric-label{color:#666d66;font-size:8px;letter-spacing:.16em}
.metric-value{color:var(--bone);font:650 32px/1 var(--display);letter-spacing:-.04em}
.online-value::before{background:var(--acid);box-shadow:0 0 16px var(--acid)}
.rules{color:#666d66;border-color:var(--hair);font-size:9px;line-height:1.9;letter-spacing:.05em}
.rules b{color:#aeb4ac}
.sync{color:#686f68;font-size:8px;letter-spacing:.1em}
.sync::before{color:var(--acid)}
.fab-admin{right:18px;bottom:18px;min-width:142px;color:var(--lan-dark);border:0;border-radius:0;background:var(--amber);box-shadow:7px 7px 0 rgba(255,184,74,.12)}
.fab-admin .lucide{width:15px;height:15px}
.fab-admin::before{display:none}
.modal-backdrop{background:rgba(4,5,4,.82);backdrop-filter:blur(14px)}
.modal{border-color:var(--hair-hot);background:#101310;box-shadow:12px 12px 0 rgba(200,255,54,.12)}
.modal h2{color:var(--bone);font:650 27px var(--display);letter-spacing:-.04em}
.modal-actions button{color:var(--lan-dark)}
.modal-actions button:first-child{color:var(--bone);border-color:var(--hair);background:transparent}
.admin-ban-tools,.metric{border-color:var(--hair)}
.admin-status,.user-detail{color:#7d847c}
.admin-status b,.user-detail b{color:var(--bone)}
.banned-row button,.admin-channel-row button{color:var(--lan-dark);background:var(--acid)}
.blocker{background:rgba(5,6,5,.94)}
.blocker-card{border-color:var(--acid);background:var(--lan-dark-2);box-shadow:14px 14px 0 rgba(200,255,54,.09)}
.blocker-card h2{color:var(--acid);font:700 34px var(--display)}
.toast-message{border-color:var(--hair);border-radius:0;color:var(--bone);background:#151815;box-shadow:0 18px 50px rgba(0,0,0,.38)}
.toast-message.success,.toast-message.warning,.toast-message.error{color:var(--bone);background:#151815}
.toast-icon{border:0;border-radius:0}
.toast-icon .lucide{width:17px;height:17px}
.mobile-users-toggle,.mobile-users-close{gap:7px}
@keyframes signal-pulse{0%{opacity:.8;transform:scale(.4)}
80%,100%{opacity:0;transform:scale(1.35)}
}
@keyframes rise{from{opacity:0;transform:translateY(12px) scale(.985)}
to{opacity:1;transform:none}
}
@media (max-width:1000px){main{grid-template-columns:230px minmax(0,1fr)}
.room-panel{display:none}
.mobile-channel-select{display:block;min-width:130px}
.chat-title{display:none}
}
@media (max-width:700px){.shell{grid-template-rows:60px minmax(0,1fr)}
header{padding:0 15px}
.brand-index{display:none}
main{display:grid;grid-template-columns:1fr;grid-template-rows:auto minmax(0,1fr)}
.profile-panel{padding:10px 14px;border-color:var(--hair);background:#0e100e}
.identity{padding:7px;grid-template-columns:38px minmax(0,1fr)}
.avatar{width:38px;height:38px}
.chat{grid-template-rows:62px minmax(0,1fr) 76px;border:0}
.chat-top{padding:0 14px}
.messages-window{padding:20px 14px 26px}
.message-bubble{width:auto;max-width:82%;min-width:120px;font-size:13px}
.composer{gap:7px;padding:12px 14px 14px}
#message{height:48px}
#send{min-width:48px;width:48px;height:48px;padding:0}
#send .send-label{display:none}
.file-toggle{width:48px;min-width:48px;height:48px}
.mobile-channel-select{height:38px;font-size:11px}
.mobile-users-toggle{height:38px;color:var(--bone);border-color:var(--hair);background:transparent}
body.mobile-users-open .profile-panel{inset:60px 0 0;padding:16px;background:#0d0f0d}
body.mobile-users-open .profile-panel .mobile-users-close{color:var(--lan-dark);background:var(--acid)}
body.mobile-users-open .fab-admin{display:none!important}
.fab-admin{right:12px;bottom:88px;width:46px;min-width:46px;height:46px;padding:0;box-shadow:5px 5px 0 rgba(255,184,74,.12)}
.fab-admin span{display:none}
}
@media (prefers-reduced-motion:reduce){*,*::before,*::after{animation-duration:.01ms!important;animation-iteration-count:1!important;scroll-behavior:auto!important;transition-duration:.01ms!important}
}
:root{--sky:#7f9fc4;--sky-deep:#678bb6;--sky-light:#a9c0d9;--glass:rgba(255,255,255,.12);--glass-strong:rgba(255,255,255,.22);--glass-line:rgba(255,255,255,.28);--glass-soft:rgba(255,255,255,.08);--cloud:#fff;--cloud-70:rgba(255,255,255,.7);--cloud-45:rgba(255,255,255,.45);--blue-ink:#52779f;--ink:#fff;--bone:#fff;--acid:#fff;--signal:#fff;--cyan:#fff;--lan-dark:#6f93bc;--hair:rgba(255,255,255,.22);--hair-hot:rgba(255,255,255,.5);--font:'Barlow','Segoe UI','PingFang SC','Microsoft YaHei',sans-serif;--display:'Instrument Serif','Times New Roman','Songti SC',serif}
body{color:#fff;background:linear-gradient(135deg,#6f92bb 0%,#87a5c8 48%,#7196bf 100%);font-family:var(--font);font-weight:300}
body::before{inset:-20%;background:radial-gradient(600px circle at var(--mx) var(--my),rgba(255,255,255,.22),transparent 62%),radial-gradient(42% 36% at 11% 18%,rgba(220,235,250,.32),transparent 72%),radial-gradient(36% 42% at 91% 82%,rgba(86,124,169,.3),transparent 74%);filter:blur(16px);animation:liquid-breathe 12s ease-in-out infinite alternate}
.shell{grid-template-rows:86px minmax(0,1fr);padding:0 16px 16px;background:transparent}
header{height:62px;margin:14px 2px 10px;padding:0 20px;border:1px solid var(--glass-line);border-radius:999px;background:rgba(255,255,255,.1);box-shadow:0 16px 40px rgba(47,77,112,.1),inset 0 1px 1px rgba(255,255,255,.28);backdrop-filter:blur(24px) saturate(130%);-webkit-backdrop-filter:blur(24px) saturate(130%)}
header::after{display:none}
.brand{color:#fff;font-size:12px;font-weight:500;letter-spacing:.26em}
.brand-icon{width:38px;height:38px;color:#fff;border:1px solid rgba(255,255,255,.5);border-radius:50%;background:rgba(255,255,255,.13);box-shadow:inset 0 1px 1px rgba(255,255,255,.32);transform:none}
.brand:hover .brand-icon{transform:rotate(10deg) scale(1.04)}
.brand-index{color:rgba(255,255,255,.5);font-size:8px;font-weight:400}
.status{color:rgba(255,255,255,.72);font-size:9px;font-weight:400}
.pulse{background:#fff;box-shadow:0 0 14px rgba(255,255,255,.9)}
.pulse::after{border-color:#fff}
main{gap:12px;grid-template-columns:minmax(248px,19vw) minmax(480px,1fr) minmax(220px,17vw);background:transparent}
.profile-panel,.chat,.room-panel{border:1px solid var(--glass-line);border-radius:28px;background:var(--glass);box-shadow:0 22px 55px rgba(40,72,109,.12),inset 0 1px 1px rgba(255,255,255,.3);backdrop-filter:blur(30px) saturate(125%);-webkit-backdrop-filter:blur(30px) saturate(125%)}
.profile-panel{padding:30px 24px 22px}
.profile-panel::after{content:'01';right:6px;top:18px;color:rgba(255,255,255,.07);font-family:var(--display);font-style:italic}
.profile-panel>div:first-child{animation:glass-reveal .9s cubic-bezier(.2,.8,.2,1) both}
.kicker{color:rgba(255,255,255,.72);font-size:9px;font-weight:500;letter-spacing:.22em}
.kicker::before{width:30px;background:rgba(255,255,255,.72)}
h1{max-width:250px;margin:24px 0 18px;color:#fff;font:italic 400 clamp(45px,4vw,66px)/.82 var(--display);letter-spacing:-.055em;text-wrap:balance}
.intro{max-width:230px;color:rgba(255,255,255,.64);font-size:11px;font-weight:300;line-height:1.75}
.identity{padding:8px;grid-template-columns:46px minmax(0,1fr);border:1px solid var(--glass-line);border-radius:22px;background:rgba(255,255,255,.1);box-shadow:inset 0 1px 1px rgba(255,255,255,.25);overflow:hidden}
.identity::before{inset:0;height:auto;border-radius:inherit;background:linear-gradient(120deg,rgba(255,255,255,.28),transparent 32%,transparent 68%,rgba(255,255,255,.14));opacity:.4;transform:none;pointer-events:none}
.identity:hover{border-color:rgba(255,255,255,.48);background:rgba(255,255,255,.16);transform:translateY(-2px)}
.avatar{width:46px;height:46px;color:var(--blue-ink);border:0;border-radius:50%;background:rgba(255,255,255,.9);box-shadow:0 8px 20px rgba(47,80,116,.12)}
.identity small{color:rgba(255,255,255,.5);font-weight:500}
.identity input{color:#fff;font-weight:500}
.identity input:focus{border-color:rgba(255,255,255,.65)}
.search-shell .lucide{color:rgba(255,255,255,.55)}
input,.mobile-channel-select{color:#fff;border:1px solid rgba(255,255,255,.22);border-radius:999px;background:rgba(255,255,255,.08);box-shadow:inset 0 1px 1px rgba(255,255,255,.16);font-family:var(--font);font-weight:300}
input::placeholder{color:rgba(255,255,255,.45)}
input:focus{border-color:rgba(255,255,255,.58);box-shadow:0 0 0 4px rgba(255,255,255,.08),inset 0 1px 1px rgba(255,255,255,.22)}
.user-row{color:rgba(255,255,255,.73);border:1px solid transparent;border-radius:15px}
.user-row:hover{color:#fff;border-color:rgba(255,255,255,.22);background:rgba(255,255,255,.1)}
.user-row.active{color:var(--blue-ink);border-color:rgba(255,255,255,.65);background:rgba(255,255,255,.88)}
.user-row-channel{color:rgba(255,255,255,.44)}
.user-row.active .user-row-channel{color:rgba(82,119,159,.65)}
.unread-dot{border-radius:999px;background:#fff;color:var(--blue-ink)}
.user-admin-button{color:var(--blue-ink);border:0;border-radius:15px;background:rgba(255,255,255,.84)}
.chat{grid-template-rows:92px minmax(0,1fr) 88px;border-right:1px solid var(--glass-line);overflow:hidden}
.chat::before{content:'CHAT';right:-1vw;top:18%;color:rgba(255,255,255,.045);font-family:var(--display);font-style:italic}
.chat-top{padding:0 28px;border-color:rgba(255,255,255,.16);background:rgba(255,255,255,.025)}
.chat-title{color:#fff;font:italic 400 clamp(34px,3vw,46px)/1 var(--display);letter-spacing:-.035em;animation:glass-reveal .7s .12s both}
.messages{background:radial-gradient(circle at 50% 48%,rgba(255,255,255,.07),transparent 48%)}
.empty{color:rgba(255,255,255,.58);font-weight:300}
.empty::before{background:#fff;box-shadow:0 4px 20px rgba(255,255,255,.7)}
.message-avatar{color:#fff;border-color:rgba(255,255,255,.28);border-radius:50%;background:rgba(255,255,255,.1)}
.message-name{color:rgba(255,255,255,.82);font-weight:500}
.message-bubble{color:#fff;border:1px solid rgba(255,255,255,.24);border-radius:22px 22px 22px 7px;background:rgba(255,255,255,.11);box-shadow:0 12px 32px rgba(48,79,115,.1),inset 0 1px 1px rgba(255,255,255,.2);backdrop-filter:blur(22px)}
.message-bubble::before{display:none}
.message.self .message-bubble{color:var(--blue-ink);border-color:rgba(255,255,255,.72);border-radius:22px 22px 7px 22px;background:rgba(255,255,255,.9);box-shadow:0 16px 38px rgba(48,79,115,.14),inset 0 1px 1px #fff}
.message.self .message-avatar{color:var(--blue-ink);border-color:rgba(255,255,255,.72);background:rgba(255,255,255,.82)}
.message.self .message-name{color:#fff}
.message-action,.message-time{color:rgba(255,255,255,.58)}
.message.self .message-action,.message.self .message-time{color:rgba(82,119,159,.62)}
.message-action:hover{color:#fff;border-radius:999px;background:rgba(255,255,255,.13)}
.message.self .message-action:hover{color:var(--blue-ink);background:rgba(82,119,159,.09)}
.message.recalled .message-bubble{color:rgba(255,255,255,.65);border-style:dashed;background:rgba(255,255,255,.05)}
.file-download{color:#fff;border-color:rgba(255,255,255,.3);border-radius:999px;background:rgba(255,255,255,.08)}
.file-download:hover{color:var(--blue-ink);background:#fff}
.composer{padding:17px 24px 20px;border-color:rgba(255,255,255,.16);background:linear-gradient(180deg,transparent,rgba(255,255,255,.035));backdrop-filter:none}
#message{padding-left:19px;background:rgba(255,255,255,.1)}
button{color:var(--blue-ink);border:1px solid rgba(255,255,255,.64);border-radius:999px;background:rgba(255,255,255,.9);box-shadow:0 8px 24px rgba(47,80,116,.1),inset 0 1px 1px #fff;font-family:var(--font);font-weight:500}
button:hover{transform:translateY(-2px);box-shadow:0 12px 28px rgba(47,80,116,.16),inset 0 1px 1px #fff}
.file-toggle{color:#fff;border-color:rgba(255,255,255,.3);background:rgba(255,255,255,.1)}
.file-toggle:hover{color:var(--blue-ink);border-color:#fff;background:#fff}
.room-panel{padding:30px 20px 22px}
.room-panel h2{color:rgba(255,255,255,.72);font-weight:500}
.room-panel h2 .lucide{color:#fff}
.channel-button{color:rgba(255,255,255,.7);border:1px solid transparent;border-radius:16px;background:transparent;box-shadow:none}
.channel-button::before{left:9px;top:50%;bottom:auto;width:6px;height:6px;border-radius:50%;background:#fff;transform:translateY(-50%) scale(0)}
.channel-button:hover{color:#fff;border-color:rgba(255,255,255,.24);background:rgba(255,255,255,.08);box-shadow:none}
.channel-button.active{padding-left:24px;color:var(--blue-ink);border-color:rgba(255,255,255,.72);background:rgba(255,255,255,.88);box-shadow:0 12px 28px rgba(47,80,116,.1)}
.channel-button.active::before{transform:translateY(-50%) scale(1);background:var(--blue-ink)}
.channel-count,.channel-button.active .channel-count{color:inherit;opacity:.68}
.metric,.rules{border-color:rgba(255,255,255,.18)}
.metric-label,.rules,.sync{color:rgba(255,255,255,.54)}
.metric-value{color:#fff;font:italic 400 36px/1 var(--display)}
.online-value::before{background:#fff;box-shadow:0 0 18px rgba(255,255,255,.9)}
.rules b,.sync::before{color:rgba(255,255,255,.86)}
.fab-admin{color:var(--blue-ink);border-color:rgba(255,255,255,.72);border-radius:999px;background:rgba(255,255,255,.9);box-shadow:0 16px 38px rgba(47,80,116,.18)}
.modal-backdrop{background:rgba(55,82,114,.42);backdrop-filter:blur(20px)}
.modal{color:#fff;border:1px solid rgba(255,255,255,.36);border-radius:28px;background:rgba(105,143,185,.76);box-shadow:0 28px 70px rgba(38,66,98,.22),inset 0 1px 1px rgba(255,255,255,.3);backdrop-filter:blur(36px)}
.modal h2{color:#fff;font:italic 400 36px var(--display)}
.modal-actions button:first-child{color:#fff;border-color:rgba(255,255,255,.3);background:rgba(255,255,255,.08)}
.admin-status,.user-detail{color:rgba(255,255,255,.7)}
.admin-status b,.user-detail b{color:#fff}
.blocker{background:rgba(76,109,148,.78);backdrop-filter:blur(26px)}
.blocker-card{border:1px solid rgba(255,255,255,.35);border-radius:28px;background:rgba(255,255,255,.12);box-shadow:0 28px 70px rgba(38,66,98,.22)}
.blocker-card h2{color:#fff;font:italic 400 42px var(--display)}
.toast-message,.toast-message.success,.toast-message.warning,.toast-message.error{color:#fff;border:1px solid rgba(255,255,255,.3);border-radius:999px;background:rgba(103,140,183,.72);box-shadow:0 18px 50px rgba(40,70,104,.18);backdrop-filter:blur(28px)}
.toast-icon{color:#fff}
@keyframes glass-reveal{from{opacity:0;filter:blur(12px);transform:translateY(24px)}
55%{opacity:.65;filter:blur(4px);transform:translateY(-3px)}
to{opacity:1;filter:blur(0);transform:none}
}
@keyframes liquid-breathe{from{transform:scale(1) translate3d(-1%,0,0)}
to{transform:scale(1.05) translate3d(1%,1%,0)}
}
@media (max-width:1000px){main{grid-template-columns:220px minmax(0,1fr)}
.room-panel{display:none}
.mobile-channel-select{display:block}
}
@media (max-width:700px){body{background:linear-gradient(160deg,#7699c0,#88a8ca 52%,#6f94bd)}
.shell{grid-template-rows:74px minmax(0,1fr);padding:0 8px 8px}
header{height:54px;margin:10px 0;padding:0 13px}
.brand-icon{width:34px;height:34px}
main{gap:8px}
.profile-panel{padding:8px 10px;border-radius:22px;background:rgba(255,255,255,.11)}
.identity{border-radius:17px}
.chat{grid-template-rows:58px minmax(0,1fr) 72px;border-radius:22px}
.chat-top{padding:0 10px}
.mobile-channel-select{height:38px;border-radius:999px;background:rgba(255,255,255,.1)}
.mobile-users-toggle{color:#fff;border-color:rgba(255,255,255,.25);background:rgba(255,255,255,.1);box-shadow:none}
.messages-window{padding:18px 12px 24px}
.message-bubble{max-width:84%}
.composer{padding:10px 10px 12px}
#message{height:48px}
#send{color:var(--blue-ink);background:rgba(255,255,255,.92)}
body.mobile-users-open .profile-panel{inset:74px 8px 8px;padding:14px;border:1px solid rgba(255,255,255,.3);border-radius:24px;background:rgba(117,154,195,.72);backdrop-filter:blur(32px)}
body.mobile-users-open .profile-panel .mobile-users-close{color:var(--blue-ink);border-radius:999px;background:rgba(255,255,255,.9)}
.fab-admin{bottom:84px}
}
:root{--navy:#183a5b;--navy-2:#315979;--navy-muted:#456682;--ice:#c3d6e7;--ice-2:#adc7df}
body{color:var(--navy);background:linear-gradient(145deg,#cbdbea 0%,#acc6df 48%,#c2d6e8 100%)}
body::before{background:radial-gradient(620px circle at var(--mx) var(--my),rgba(255,255,255,.55),transparent 65%),radial-gradient(42% 40% at 8% 12%,rgba(255,255,255,.42),transparent 70%),radial-gradient(38% 40% at 92% 86%,rgba(93,139,181,.2),transparent 72%)}
header{color:var(--navy);border-color:rgba(255,255,255,.58);background:rgba(255,255,255,.28);box-shadow:0 16px 42px rgba(46,81,114,.12),inset 0 1px 1px rgba(255,255,255,.72)}
.brand,.status{color:var(--navy)}
.brand-index{color:rgba(24,58,91,.58)}
.brand-icon{color:var(--navy);border-color:rgba(255,255,255,.76);background:rgba(255,255,255,.5)}
.pulse{background:#fff;box-shadow:0 0 0 3px rgba(255,255,255,.34),0 0 14px rgba(255,255,255,.9)}
.profile-panel,.chat,.room-panel{color:var(--navy);border-color:rgba(255,255,255,.54);background:rgba(255,255,255,.22);box-shadow:0 22px 55px rgba(48,82,116,.12),inset 0 1px 1px rgba(255,255,255,.72)}
.profile-panel{overflow-x:hidden;overscroll-behavior-x:none}
.profile-panel::after,.chat::before{color:rgba(255,255,255,.18)}
.kicker{color:var(--navy-2)}
.kicker::before{background:var(--navy-2)}
h1,.chat-title{color:var(--navy)}
.intro{color:var(--navy-muted);font-weight:400}
.identity{border-color:rgba(255,255,255,.66);background:rgba(255,255,255,.3);box-shadow:inset 0 1px 1px rgba(255,255,255,.78)}
.identity:hover{border-color:rgba(255,255,255,.9);background:rgba(255,255,255,.4)}
.avatar{color:#fff;background:var(--navy)}
.identity small{color:rgba(24,58,91,.58)}
.identity input,.mobile-channel-select,input{color:var(--navy);border-color:rgba(255,255,255,.6);background:rgba(255,255,255,.3)}
input::placeholder{color:rgba(24,58,91,.52)}
input:focus{border-color:rgba(24,58,91,.45);box-shadow:0 0 0 4px rgba(255,255,255,.18),inset 0 1px 1px rgba(255,255,255,.75)}
select option{color:var(--navy);background:#e3edf5}
.search-shell .lucide{color:var(--navy-muted)}
.user-row{color:var(--navy-2);font-weight:400}
.user-row:hover{color:var(--navy);border-color:rgba(255,255,255,.65);background:rgba(255,255,255,.28)}
.user-row.active{color:#fff;border-color:var(--navy);background:var(--navy)}
.user-row-channel{color:rgba(24,58,91,.58)}
.user-row.active .user-row-channel{color:rgba(255,255,255,.64)}
.unread-dot{color:#fff;background:var(--navy)}
.chat-top{border-color:rgba(255,255,255,.42);background:rgba(255,255,255,.08)}
.messages{background:radial-gradient(circle at 50% 45%,rgba(255,255,255,.22),transparent 48%)}
.empty{color:var(--navy-muted);font-weight:400}
.empty::before{background:var(--navy);box-shadow:0 5px 18px rgba(24,58,91,.25)}
.message-avatar{color:var(--navy);border-color:rgba(255,255,255,.7);background:rgba(255,255,255,.42)}
.message-name{color:var(--navy)}
.message-bubble{color:var(--navy);border-color:rgba(255,255,255,.7);background:rgba(255,255,255,.38);box-shadow:0 12px 32px rgba(48,79,115,.1),inset 0 1px 1px rgba(255,255,255,.82)}
.message.self .message-bubble{color:#fff;border-color:rgba(24,58,91,.72);background:linear-gradient(145deg,#244d72,#183a5b);box-shadow:0 16px 38px rgba(35,72,106,.22),inset 0 1px 1px rgba(255,255,255,.16)}
.message.self .message-avatar{color:#fff;border-color:var(--navy);background:var(--navy)}
.message.self .message-name{color:var(--navy)}
.message-action,.message-time{color:rgba(24,58,91,.62)}
.message.self .message-action,.message.self .message-time{color:rgba(255,255,255,.68)}
.message-action:hover{color:var(--navy);background:rgba(255,255,255,.46)}
.message.self .message-action:hover{color:#fff;background:rgba(255,255,255,.12)}
.message.recalled .message-bubble{color:var(--navy-muted);border-color:rgba(24,58,91,.2);background:rgba(255,255,255,.14)}
.composer{overflow:visible;border-color:rgba(255,255,255,.42);background:linear-gradient(180deg,rgba(255,255,255,.02),rgba(255,255,255,.14))}
#message{background:rgba(255,255,255,.34)}
button{color:#fff;border-color:rgba(24,58,91,.78);background:var(--navy);box-shadow:0 9px 24px rgba(36,72,107,.18),inset 0 1px 1px rgba(255,255,255,.16)}
button:hover{box-shadow:0 13px 28px rgba(36,72,107,.24),inset 0 1px 1px rgba(255,255,255,.18)}
.file-toggle,.emoji-toggle{color:var(--navy);border-color:rgba(255,255,255,.65);background:rgba(255,255,255,.34);box-shadow:inset 0 1px 1px rgba(255,255,255,.7)}
.file-toggle:hover,.emoji-toggle:hover,.emoji-toggle[aria-expanded="true"]{color:#fff;border-color:var(--navy);background:var(--navy)}
.emoji-wrap{position:relative;z-index:12;flex:0 0 50px}
.emoji-toggle{width:50px;min-width:50px;height:50px;padding:0;display:grid;place-items:center}
.emoji-panel{position:absolute;left:0;bottom:62px;z-index:20;width:300px;height:270px;padding:14px;display:grid;grid-template-rows:minmax(0,1fr) 32px;gap:10px;border:1px solid rgba(255,255,255,.82);border-radius:26px;background:rgba(225,237,247,.78);box-shadow:0 24px 60px rgba(34,70,104,.22),inset 0 1px 1px #fff;backdrop-filter:blur(32px) saturate(135%);-webkit-backdrop-filter:blur(32px) saturate(135%);overflow:hidden;transform-origin:left bottom;animation:emoji-pop .22s cubic-bezier(.2,.8,.2,1)}
.emoji-panel[hidden]{display:none}
.emoji-grid{min-height:0;display:grid;grid-template-columns:repeat(6,1fr);grid-template-rows:repeat(4,1fr);gap:5px}
.emoji-option{width:100%;min-width:0;height:100%;min-height:0;padding:0;display:grid;place-items:center;color:initial;border:0;border-radius:13px;background:transparent;box-shadow:none;font-family:'Segoe UI Emoji','Apple Color Emoji',sans-serif;font-size:21px;line-height:1}
.emoji-option:hover{transform:translateY(-2px) scale(1.08);color:initial;background:rgba(255,255,255,.6);box-shadow:0 8px 18px rgba(36,72,107,.1)}
.emoji-pagination{display:flex;align-items:center;justify-content:center;gap:10px}
.emoji-page-button{width:32px;min-width:32px;height:32px;padding:0;display:grid;place-items:center;color:var(--navy);border:1px solid rgba(255,255,255,.7);background:rgba(255,255,255,.48);box-shadow:none}
.emoji-page-button:hover{color:#fff;background:var(--navy)}
.emoji-page-button:disabled{opacity:.35}
.emoji-page-label{min-width:48px;color:var(--navy-muted);text-align:center;font-size:10px;font-weight:500;letter-spacing:.12em}
.room-panel h2,.room-panel h2 .lucide{color:var(--navy)}
.channel-button{color:var(--navy-2);font-weight:400}
.channel-button:hover{color:var(--navy);border-color:rgba(255,255,255,.65);background:rgba(255,255,255,.28)}
.channel-button.active{color:#fff;border-color:var(--navy);background:var(--navy)}
.channel-button.active::before{background:#fff}
.metric,.rules{border-color:rgba(255,255,255,.5)}
.metric-label,.rules,.sync{color:var(--navy-muted);font-weight:400}
.metric-value,.rules b,.sync::before{color:var(--navy)}
.online-value::before{background:var(--navy);box-shadow:0 0 0 4px rgba(24,58,91,.12)}
.fab-admin{color:#fff;border-color:var(--navy);background:var(--navy)}
.modal-backdrop{background:rgba(55,83,112,.28)}
.modal{color:var(--navy);border-color:rgba(255,255,255,.8);background:rgba(223,235,245,.88);box-shadow:0 30px 74px rgba(36,70,103,.25),inset 0 1px 1px #fff}
.modal h2{color:var(--navy)}
.modal-actions button:first-child{color:var(--navy);border-color:rgba(24,58,91,.22);background:rgba(255,255,255,.38)}
.admin-status,.user-detail{color:var(--navy-muted)}
.admin-status b,.user-detail b{color:var(--navy)}
.toast-message,.toast-message.success,.toast-message.warning,.toast-message.error{color:#fff;border-color:rgba(24,58,91,.72);background:rgba(24,58,91,.88)}
@keyframes emoji-pop{from{opacity:0;filter:blur(8px);transform:translateY(10px) scale(.96)}
to{opacity:1;filter:blur(0);transform:none}
}
@media (max-width:700px){body{background:linear-gradient(160deg,#c8dbea,#abc6df 52%,#bed3e6)}
main{grid-template-columns:1fr;grid-template-rows:auto minmax(0,1fr)}
.mobile-channel-select{color:var(--navy);background:rgba(255,255,255,.34)}
.mobile-users-toggle{color:var(--navy);border-color:rgba(255,255,255,.62);background:rgba(255,255,255,.3)}
#send{color:#fff;background:var(--navy)}
.emoji-wrap{flex-basis:48px}
.emoji-toggle{width:48px;min-width:48px;height:48px}
.emoji-panel{left:-2px;bottom:58px;width:min(292px,calc(100vw - 28px));height:260px;padding:12px;border-radius:22px}
body.mobile-users-open .profile-panel{width:auto;color:var(--navy);background:rgba(215,231,243,.9)}
body.mobile-users-open .profile-panel .mobile-users-close{color:#fff;background:var(--navy)}
}
:root{--ios-blue:#0a84ff;--ios-blue-deep:#0066d6;--ios-ink:#1d1d1f;--ios-secondary:#5e6470;--ios-tertiary:#7a8290;--ios-glass:rgba(250,252,255,.5);--ios-glass-strong:rgba(255,255,255,.7);--ios-stroke:rgba(255,255,255,.72);--ios-stroke-soft:rgba(255,255,255,.42);--ios-shadow:0 18px 44px rgba(43,63,89,.15);--ios-radius:30px;--ios-inner:20px;--font:-apple-system,BlinkMacSystemFont,'SF Pro Text','SF Pro Display','Segoe UI','PingFang SC','Microsoft YaHei',sans-serif;--display:-apple-system,BlinkMacSystemFont,'SF Pro Display','Segoe UI','PingFang SC','Microsoft YaHei',sans-serif}
html{background:#b8cbe2}
body{color:var(--ios-ink);background:radial-gradient(circle at 8% 0%,rgba(255,255,255,.92),transparent 30%),radial-gradient(circle at 90% 14%,rgba(214,196,255,.62),transparent 31%),radial-gradient(circle at 75% 92%,rgba(255,205,190,.42),transparent 32%),linear-gradient(145deg,#b8d2ea 0%,#dbe8f4 47%,#a9c6e3 100%);font-family:var(--font);font-weight:400}
body::before{inset:0;background:radial-gradient(ellipse 28% 42% at 23% 64%,rgba(80,155,255,.22),transparent 72%),radial-gradient(ellipse 36% 30% at 72% 36%,rgba(255,255,255,.34),transparent 74%);filter:none;animation:none}
.shell{grid-template-rows:76px minmax(0,1fr);padding:0 12px 12px}
header{height:56px;margin:10px 2px;padding:0 16px;color:var(--ios-ink);border:1px solid var(--ios-stroke);border-radius:28px;background:linear-gradient(140deg,rgba(255,255,255,.67),rgba(255,255,255,.34));box-shadow:0 12px 30px rgba(46,70,98,.12),inset 0 1px 1px rgba(255,255,255,.95),inset 0 -1px 0 rgba(255,255,255,.25);backdrop-filter:blur(22px) saturate(145%);-webkit-backdrop-filter:blur(22px) saturate(145%);contain:paint}
.brand,.status{color:var(--ios-ink)}
.brand{font-size:12px;font-weight:650;letter-spacing:.16em}
.brand-index{color:var(--ios-secondary);font-size:8px;font-weight:500}
.brand-icon{width:38px;height:38px;color:var(--ios-blue);border:1px solid rgba(255,255,255,.85);border-radius:14px;background:linear-gradient(145deg,rgba(255,255,255,.9),rgba(255,255,255,.48));box-shadow:0 5px 16px rgba(36,73,110,.12),inset 0 1px 1px #fff}
.status{color:var(--ios-secondary);font-weight:500;letter-spacing:.04em;text-transform:none}
.pulse{background:#34c759;box-shadow:0 0 0 3px rgba(52,199,89,.16)}
.pulse::after{display:none}
main{gap:10px;grid-template-columns:minmax(250px,19vw) minmax(480px,1fr) minmax(220px,17vw);background:transparent}
.profile-panel,.chat,.room-panel{color:var(--ios-ink);border:1px solid var(--ios-stroke);border-radius:var(--ios-radius);background:linear-gradient(145deg,rgba(255,255,255,.58),rgba(242,248,255,.33));box-shadow:var(--ios-shadow),inset 0 1px 1px rgba(255,255,255,.94),inset 0 -1px 0 rgba(255,255,255,.22);backdrop-filter:blur(22px) saturate(135%);-webkit-backdrop-filter:blur(22px) saturate(135%);contain:paint}
.profile-panel{padding:24px 20px 18px;overflow-x:hidden}
.profile-panel::after,.chat::before{display:none}
.profile-panel>div:first-child,.chat-title{animation:none;filter:none}
.kicker{color:var(--ios-blue);font-size:9px;font-weight:650;letter-spacing:.14em}
.kicker::before{width:22px;height:2px;border-radius:2px;background:var(--ios-blue)}
h1{max-width:230px;margin:18px 0 13px;color:var(--ios-ink);font:700 clamp(36px,3vw,50px)/.96 var(--display);letter-spacing:-.055em}
.intro{color:var(--ios-secondary);font-size:11px;font-weight:450;line-height:1.65}
.identity{padding:7px;grid-template-columns:46px minmax(0,1fr);border:1px solid rgba(255,255,255,.78);border-radius:22px;background:linear-gradient(145deg,rgba(255,255,255,.62),rgba(255,255,255,.3));box-shadow:0 8px 20px rgba(52,76,103,.08),inset 0 1px 1px #fff;backdrop-filter:none}
.identity::before{display:none}
.identity:hover{border-color:#fff;background:rgba(255,255,255,.68);transform:scale(1.01)}
.avatar{width:46px;height:46px;color:#fff;border-radius:15px;background:linear-gradient(145deg,#3b9cff,#087cff);box-shadow:0 7px 18px rgba(10,132,255,.25),inset 0 1px 1px rgba(255,255,255,.35)}
.identity small{color:var(--ios-tertiary);font-weight:600}
.identity input{color:var(--ios-ink);font-size:13px;font-weight:600}
input,.mobile-channel-select{color:var(--ios-ink);border:1px solid rgba(255,255,255,.76);border-radius:16px;background:rgba(255,255,255,.43);box-shadow:inset 0 1px 1px rgba(255,255,255,.92);backdrop-filter:none}
input::placeholder{color:var(--ios-tertiary)}
input:focus{border-color:rgba(10,132,255,.5);box-shadow:0 0 0 4px rgba(10,132,255,.12),inset 0 1px 1px #fff}
.search-shell .lucide{color:var(--ios-tertiary)}
.user-row{color:var(--ios-secondary);border:1px solid transparent;border-radius:15px;font-weight:500;box-shadow:none}
.user-row:hover{color:var(--ios-ink);border-color:rgba(255,255,255,.65);background:rgba(255,255,255,.42)}
.user-row.active{color:#fff;border-color:rgba(10,132,255,.78);background:linear-gradient(145deg,#3099ff,#0a84ff);box-shadow:0 7px 18px rgba(10,132,255,.2)}
.user-row-channel{color:var(--ios-tertiary)}
.user-row.active .user-row-channel{color:rgba(255,255,255,.7)}
.unread-dot{color:#fff;background:#ff3b30}
.user-admin-button{color:var(--ios-blue);border-color:rgba(255,255,255,.8);border-radius:15px;background:rgba(255,255,255,.62);box-shadow:inset 0 1px 1px #fff}
.chat{grid-template-rows:78px minmax(0,1fr) 84px;background:linear-gradient(150deg,rgba(250,252,255,.68),rgba(238,246,254,.4));overflow:hidden}
.chat-top{padding:0 24px;border:0;background:linear-gradient(180deg,rgba(255,255,255,.18),transparent)}
.chat-title{color:var(--ios-ink);font:700 clamp(24px,2.3vw,34px)/1 var(--display);letter-spacing:-.04em}
.messages{background:linear-gradient(180deg,rgba(255,255,255,.08),rgba(255,255,255,.18));contain:strict}
.messages-window{contain:layout style}
.empty{color:var(--ios-tertiary);font-weight:500}
.empty::before{width:32px;height:3px;border-radius:3px;background:var(--ios-blue);box-shadow:none}
.message-avatar{color:var(--ios-blue);border-color:rgba(255,255,255,.78);border-radius:14px;background:rgba(255,255,255,.66);box-shadow:0 5px 12px rgba(48,70,96,.08)}
.message-name{color:var(--ios-secondary);font-weight:650;letter-spacing:.06em}
.message-bubble{color:var(--ios-ink);border:1px solid rgba(255,255,255,.78);border-radius:21px;background:rgba(255,255,255,.68);box-shadow:0 8px 22px rgba(43,66,92,.09),inset 0 1px 1px #fff;backdrop-filter:none}
.message.self .message-bubble{color:#fff;border-color:rgba(10,132,255,.75);border-radius:21px;background:linear-gradient(145deg,#339cff,#0a84ff);box-shadow:0 10px 24px rgba(10,132,255,.22),inset 0 1px 1px rgba(255,255,255,.3)}
.message.self .message-avatar{color:#fff;border-color:rgba(10,132,255,.75);background:var(--ios-blue)}
.message.self .message-name{color:var(--ios-blue)}
.message-action,.message-time{color:var(--ios-tertiary)}
.message.self .message-action,.message.self .message-time{color:rgba(255,255,255,.72)}
.message-action:hover{color:var(--ios-blue);background:rgba(10,132,255,.09)}
.message.self .message-action:hover{color:#fff;background:rgba(255,255,255,.13)}
.message.recalled .message-bubble{color:var(--ios-secondary);border-color:rgba(118,118,128,.16);background:rgba(255,255,255,.35)}
.composer{margin:8px 12px 12px;padding:8px;gap:7px;border:1px solid rgba(255,255,255,.8);border-radius:27px;background:linear-gradient(145deg,rgba(255,255,255,.72),rgba(255,255,255,.4));box-shadow:0 12px 30px rgba(39,62,88,.13),inset 0 1px 1px #fff;backdrop-filter:none;overflow:visible;contain:layout style}
#message{height:48px;padding:0 16px;border:0;border-radius:19px;background:rgba(255,255,255,.42);box-shadow:none}
#message:focus{box-shadow:inset 0 0 0 2px rgba(10,132,255,.2)}
button{color:var(--ios-ink);border:1px solid rgba(255,255,255,.8);border-radius:17px;background:linear-gradient(145deg,rgba(255,255,255,.82),rgba(255,255,255,.48));box-shadow:0 5px 14px rgba(44,69,95,.1),inset 0 1px 1px #fff;font-weight:600;transition:transform .16s ease,background .16s ease,box-shadow .16s ease}
button:hover{transform:scale(1.025);box-shadow:0 7px 18px rgba(44,69,95,.14),inset 0 1px 1px #fff}
button:active{transform:scale(.97)}
#send{color:#fff;border-color:rgba(10,132,255,.72);border-radius:19px;background:linear-gradient(145deg,#3b9fff,#0a84ff);box-shadow:0 7px 18px rgba(10,132,255,.25),inset 0 1px 1px rgba(255,255,255,.3)}
.file-toggle,.emoji-toggle{color:var(--ios-blue);border-color:rgba(255,255,255,.84);border-radius:19px;background:rgba(255,255,255,.62);box-shadow:inset 0 1px 1px #fff}
.file-toggle:hover,.emoji-toggle:hover,.emoji-toggle[aria-expanded="true"]{color:#fff;border-color:var(--ios-blue);background:var(--ios-blue)}
.emoji-panel{border-color:rgba(255,255,255,.86);border-radius:28px;background:linear-gradient(145deg,rgba(250,253,255,.88),rgba(235,244,253,.7));box-shadow:0 22px 58px rgba(38,61,88,.2),inset 0 1px 1px #fff;backdrop-filter:blur(20px) saturate(140%);-webkit-backdrop-filter:blur(20px) saturate(140%)}
.emoji-option{border-radius:14px}
.emoji-option:hover{background:rgba(255,255,255,.74)}
.emoji-page-button{color:var(--ios-blue);border-color:rgba(255,255,255,.85);background:rgba(255,255,255,.7)}
.emoji-page-button:hover{color:#fff;background:var(--ios-blue)}
.emoji-page-label{color:var(--ios-secondary)}
.room-panel{padding:24px 18px 18px}
.room-panel h2,.room-panel h2 .lucide{color:var(--ios-secondary)}
.channel-button{color:var(--ios-secondary);border-radius:17px;font-weight:550}
.channel-button:hover{color:var(--ios-ink);border-color:rgba(255,255,255,.72);background:rgba(255,255,255,.4)}
.channel-button.active{color:#fff;border-color:rgba(10,132,255,.72);background:linear-gradient(145deg,#329aff,#0a84ff);box-shadow:0 7px 18px rgba(10,132,255,.2)}
.channel-button.active::before{background:#fff}
.metric,.rules{border-color:rgba(255,255,255,.6)}
.metric-label,.rules,.sync{color:var(--ios-secondary);font-weight:500}
.metric-value,.rules b,.sync::before{color:var(--ios-ink)}
.metric-value{font:700 30px/1 var(--display)}
.online-value::before{background:#34c759;box-shadow:0 0 0 4px rgba(52,199,89,.13)}
.fab-admin{color:#fff;border-color:rgba(10,132,255,.72);border-radius:19px;background:linear-gradient(145deg,#319aff,#0a84ff);box-shadow:0 12px 28px rgba(10,132,255,.22),inset 0 1px 1px rgba(255,255,255,.3)}
.modal-backdrop{background:rgba(58,75,96,.22);backdrop-filter:blur(12px)}
.modal{color:var(--ios-ink);border-color:rgba(255,255,255,.85);border-radius:32px;background:linear-gradient(145deg,rgba(250,253,255,.9),rgba(231,241,251,.8));box-shadow:0 28px 70px rgba(39,60,84,.22),inset 0 1px 1px #fff;backdrop-filter:blur(22px) saturate(130%)}
.modal h2{color:var(--ios-ink);font:700 28px var(--display);letter-spacing:-.04em}
.modal input{background:rgba(255,255,255,.62)}
.modal-actions button:first-child{color:var(--ios-blue);border-color:rgba(255,255,255,.85);background:rgba(255,255,255,.62)}
.admin-status,.user-detail{color:var(--ios-secondary)}
.admin-status b,.user-detail b{color:var(--ios-ink)}
.toast-message,.toast-message.success,.toast-message.warning,.toast-message.error{color:var(--ios-ink);border-color:rgba(255,255,255,.86);border-radius:20px;background:rgba(248,251,255,.88);box-shadow:0 16px 42px rgba(37,59,84,.18),inset 0 1px 1px #fff;backdrop-filter:blur(18px)}
.toast-icon{color:var(--ios-blue)}
@supports not ((backdrop-filter:blur(1px)) or (-webkit-backdrop-filter:blur(1px))){header,.profile-panel,.chat,.room-panel,.emoji-panel,.modal{background:rgba(241,247,253,.94)}
}
@media (max-width:1000px){main{grid-template-columns:220px minmax(0,1fr)}
}
@media (max-width:700px){body{background:radial-gradient(circle at 18% 0%,rgba(255,255,255,.9),transparent 32%),radial-gradient(circle at 86% 80%,rgba(204,188,255,.44),transparent 34%),linear-gradient(160deg,#b7d1ea,#dce8f4 54%,#abc8e4)}
.shell{grid-template-rows:70px minmax(0,1fr);padding:0 7px 7px}
header{height:52px;margin:9px 0;padding:0 12px;border-radius:24px}
.brand-icon{width:34px;height:34px;border-radius:13px}
main{grid-template-columns:1fr;grid-template-rows:auto minmax(0,1fr);gap:7px}
.profile-panel{padding:7px 9px;border-radius:26px}
.identity{border-radius:19px}
.avatar{border-radius:14px}
.chat{grid-template-rows:58px minmax(0,1fr) 72px;border-radius:28px}
.chat-top{padding:0 9px}
.mobile-channel-select{height:40px;border-radius:17px}
.mobile-users-toggle{height:40px;color:var(--ios-blue);border-color:rgba(255,255,255,.82);border-radius:17px;background:rgba(255,255,255,.6);box-shadow:inset 0 1px 1px #fff}
.messages-window{padding:16px 11px 22px}
.composer{margin:6px 7px 8px;padding:6px;border-radius:24px}
#message{height:46px;border-radius:17px}
#send,.file-toggle,.emoji-toggle{width:46px;min-width:46px;height:46px;border-radius:17px}
.emoji-wrap{flex-basis:46px}
.emoji-panel{left:-1px;bottom:56px;width:min(292px,calc(100vw - 24px));border-radius:26px}
body.mobile-users-open .profile-panel{width:auto;inset:70px 7px 7px;border-radius:28px;background:rgba(239,247,253,.86)}
body.mobile-users-open .profile-panel .mobile-users-close{color:#fff;border-radius:18px;background:var(--ios-blue)}
.fab-admin{bottom:80px;border-radius:18px}
}
html.performance-lite header,html.performance-lite .profile-panel,html.performance-lite .chat,html.performance-lite .room-panel{-webkit-backdrop-filter:blur(12px) saturate(115%);backdrop-filter:blur(12px) saturate(115%);box-shadow:0 12px 30px rgba(46,75,105,.11),inset 0 1px 0 rgba(255,255,255,.9)}
html.performance-lite .emoji-panel,html.performance-lite .modal,html.performance-lite .toast-message{-webkit-backdrop-filter:blur(10px) saturate(110%);backdrop-filter:blur(10px) saturate(110%)}
@media (max-width:700px),(hover:none){
button:hover{transform:none}
}
@media (prefers-reduced-motion:reduce){button,.message,.emoji-panel,.toast-message{transition:none!important;animation:none!important}
}
.brand{font-size:13px}
.brand-index{font-size:10px}
.status{font-size:11px}
.kicker{font-size:11px}
.intro{font-size:13px}
.identity small{font-size:10px}
.identity input{font-size:14px}
.user-search{font-size:14px}
.user-row-name{font-size:13px}
.user-row-channel{font-size:11px}
.user-empty{font-size:12px}
.unread-dot{font-size:11px}
.message-name{font-size:11px}
.message-time{font-size:11px}
.file-meta{font-size:12px}
.file-download{font-size:12px}
.emoji-page-label{font-size:12px}
.room-panel h2{font-size:11px}
.channel-button{font-size:12px}
.metric-label{font-size:10px}
.rules{font-size:11px}
.sync{font-size:10px}
.admin-status,.banned-empty{font-size:13px}
.admin-channel-row,.banned-row,.blocker-meta{font-size:13px}
.admin-ban-tools h3{font-size:12px}
.toast-message{font-size:14px}
.mobile-channel-select{font-size:12px}
.identity input{height:28px;padding:2px 1px 3px;cursor:text!important;caret-color:var(--ios-blue);user-select:text;pointer-events:auto;border:0;border-bottom:1px solid rgba(29,29,31,.3);border-radius:0;background:transparent;box-shadow:none;transition:border-color .16s ease,box-shadow .16s ease,color .16s ease}
.identity input:hover{border-bottom-color:rgba(10,132,255,.62)}
.identity input:focus{border-bottom-color:var(--ios-blue);box-shadow:0 3px 0 -2px rgba(10,132,255,.28)}
.identity:focus-within{border-color:rgba(10,132,255,.42);box-shadow:0 8px 22px rgba(10,132,255,.1),inset 0 1px 1px #fff}
.profile-panel h1{width:100%;max-width:none;white-space:nowrap}
.message-bubble,.message.self .message-bubble{color:var(--ios-ink);border:1px solid rgba(255,255,255,.88);background:radial-gradient(circle at 14% 0%,rgba(255,255,255,.72),transparent 38%),linear-gradient(145deg,rgba(255,255,255,.58),rgba(232,243,253,.34));box-shadow:0 10px 26px rgba(43,66,92,.1),inset 0 1px 1px rgba(255,255,255,.98),inset 0 -1px 0 rgba(255,255,255,.28);backdrop-filter:none}
.message.self .message-bubble{border-color:rgba(194,224,255,.9);background:radial-gradient(circle at 82% 0%,rgba(255,255,255,.86),transparent 38%),linear-gradient(145deg,rgba(223,240,255,.72),rgba(191,220,248,.48));box-shadow:0 11px 28px rgba(31,91,145,.13),inset 0 1px 1px #fff,inset 0 -1px 0 rgba(120,177,227,.16)}
.message.self .message-avatar{color:var(--ios-blue);border-color:rgba(255,255,255,.9);background:linear-gradient(145deg,rgba(255,255,255,.88),rgba(218,237,253,.62));box-shadow:0 6px 16px rgba(48,88,124,.11),inset 0 1px 1px #fff}
.message.self .message-action,.message.self .message-time{color:var(--ios-secondary)}
.message.self .message-action:hover{color:var(--ios-blue);background:rgba(255,255,255,.46)}
.file-download,.file-download:visited{color:#17496f;border-color:rgba(23,73,111,.28);background:radial-gradient(circle at 25% 0%,rgba(255,255,255,.98),transparent 50%),linear-gradient(145deg,rgba(255,255,255,.84),rgba(216,235,251,.7));box-shadow:0 5px 14px rgba(32,71,105,.13),inset 0 1px 1px #fff;font-weight:750}
.file-download .lucide{color:#0b72c9;stroke-width:2.5}
.file-download:hover{color:#fff;border-color:rgba(10,106,190,.72);background:linear-gradient(145deg,#268ee6,#0a6abe);box-shadow:0 7px 18px rgba(10,106,190,.24),inset 0 1px 1px rgba(255,255,255,.34)}
.file-download:hover .lucide{color:#fff}
.file-download:focus-visible{outline:3px solid rgba(10,132,255,.24);outline-offset:2px}
button,#send,.file-toggle,.emoji-toggle,.fab-admin,.user-admin-button{color:var(--ios-ink);border-color:rgba(255,255,255,.9);background:radial-gradient(circle at 22% 0%,rgba(255,255,255,.95),transparent 46%),linear-gradient(145deg,rgba(255,255,255,.72),rgba(226,239,251,.48));box-shadow:0 7px 18px rgba(42,68,94,.11),inset 0 1px 1px #fff,inset 0 -1px 0 rgba(255,255,255,.3)}
button:hover,#send:hover,.file-toggle:hover,.emoji-toggle:hover,.fab-admin:hover{color:var(--ios-blue);border-color:rgba(255,255,255,1);background:radial-gradient(circle at 25% 0%,#fff,transparent 48%),linear-gradient(145deg,rgba(255,255,255,.86),rgba(222,239,254,.62));box-shadow:0 9px 22px rgba(41,76,108,.14),inset 0 1px 1px #fff}
#send .lucide,.fab-admin .lucide{color:var(--ios-blue)}
.emoji-toggle[aria-expanded="true"]{color:var(--ios-blue);border-color:rgba(10,132,255,.28);background:linear-gradient(145deg,rgba(255,255,255,.9),rgba(211,234,253,.68))}
.channel-button.active .channel-count,.user-row.active .user-row-channel{color:var(--ios-secondary)}
.admin-channel-row button,.admin-ban-entry button,.banned-row button,.admin-settings-save,.modal-actions button,body.mobile-users-open .profile-panel .mobile-users-close{color:var(--ios-ink);border-color:rgba(255,255,255,.9);background:linear-gradient(145deg,rgba(255,255,255,.82),rgba(223,238,251,.56));box-shadow:0 6px 16px rgba(42,68,94,.1),inset 0 1px 1px #fff}
.admin-tool-panel{border-color:rgba(255,255,255,.82);background:linear-gradient(145deg,rgba(255,255,255,.62),rgba(225,239,251,.42));box-shadow:0 10px 24px rgba(42,68,94,.09),inset 0 1px 1px #fff}
.admin-setting-row{color:var(--ios-secondary)}
.admin-setting-row input{color:var(--ios-ink);border-color:rgba(255,255,255,.9);background:linear-gradient(145deg,rgba(255,255,255,.86),rgba(226,239,251,.62));box-shadow:inset 0 1px 1px #fff}
@media (max-width:700px){#send{color:var(--ios-ink)}
#send .lucide{color:var(--ios-blue)}
}
html,body,.shell{width:100%;max-width:100%;overflow-x:hidden}
@supports (overflow:clip){html,body{overflow-x:clip}
}
@media (max-width:700px){.shell,main,.profile-panel,.chat,.chat-top,.messages,.composer{min-width:0;max-width:100%}
main{width:100%;grid-template-columns:minmax(0,1fr)}
.profile-panel,.chat{width:100%}
.identity{width:min(100%,280px);max-width:100%;min-width:0}
.chat-top{width:100%;display:grid;grid-template-columns:minmax(0,1fr) 64px;gap:7px}
.mobile-channel-select{width:100%;min-width:0;max-width:100%}
.mobile-users-toggle{width:64px;min-width:0;max-width:64px;padding:0 7px;gap:3px;overflow:hidden}
.mobile-unread-count{position:absolute;top:3px;right:3px}
.composer{width:auto;max-width:calc(100% - 14px)}
.composer>*{min-width:0}
.emoji-wrap,#send,.file-toggle{width:46px;min-width:46px;max-width:46px;flex:0 0 46px}
#message{width:0;min-width:0;max-width:none;flex:1 1 0}
.message,.message-file,.message-bubble{min-width:0;max-width:100%}
}
.room-panel{scrollbar-width:thin;scrollbar-color:rgba(54,91,126,.62) transparent;scrollbar-gutter:stable}
.user-list{padding-right:5px;scrollbar-width:auto;scrollbar-color:rgba(54,91,126,.72) rgba(255,255,255,.3);scrollbar-gutter:stable}
.room-panel::-webkit-scrollbar{width:8px}
.room-panel::-webkit-scrollbar-track{background:transparent}
.room-panel::-webkit-scrollbar-thumb{min-height:46px;border:2px solid transparent;border-radius:999px;background:rgba(54,91,126,.62) padding-box}
.room-panel::-webkit-scrollbar-thumb:hover{background:rgba(24,70,113,.86) padding-box}
.user-list::-webkit-scrollbar-button,.profile-panel::-webkit-scrollbar-button,.room-panel::-webkit-scrollbar-button,.messages::-webkit-scrollbar-button{display:none;width:0;height:0}
.user-list::-webkit-scrollbar{width:11px}
.user-list::-webkit-scrollbar-track{border:1px solid rgba(255,255,255,.62);border-radius:999px;background:rgba(255,255,255,.28);box-shadow:inset 0 1px 3px rgba(50,76,103,.1)}
.user-list::-webkit-scrollbar-thumb{min-height:42px;border:2px solid transparent;border-radius:999px;background:linear-gradient(180deg,rgba(80,129,174,.86),rgba(42,83,121,.78)) padding-box;box-shadow:inset 0 1px 1px rgba(255,255,255,.55),0 2px 6px rgba(35,66,95,.16)}
.user-list::-webkit-scrollbar-thumb:hover{background:linear-gradient(180deg,rgba(55,118,178,.96),rgba(24,70,113,.9)) padding-box}
.user-list::-webkit-scrollbar-thumb:active{background:var(--ios-blue)}
@media (max-width:700px){.user-list{scrollbar-width:thin}
.user-list::-webkit-scrollbar{width:8px}
}
@media (min-width:701px){.profile-panel,.user-list,.room-panel{-ms-overflow-style:none;scrollbar-width:none;scrollbar-gutter:auto}
.profile-panel::-webkit-scrollbar,.user-list::-webkit-scrollbar,.room-panel::-webkit-scrollbar{display:none;width:0;height:0}
}
#message{position:relative;z-index:1;cursor:text!important;caret-color:var(--ios-blue)!important;user-select:text;-webkit-user-select:text;pointer-events:auto}
#message:focus{outline:none;box-shadow:inset 0 0 0 2px rgba(10,132,255,.22),0 0 0 1px rgba(255,255,255,.5)}
.composer:focus-within{border-color:rgba(10,132,255,.4);box-shadow:0 12px 30px rgba(39,62,88,.13),0 0 0 3px rgba(10,132,255,.08),inset 0 1px 1px #fff}
#admin-password,#admin-retention,#admin-file-limit,#admin-ban-ip,.admin-channel-row input{position:relative;z-index:1;cursor:text!important;caret-color:var(--ios-blue)!important;user-select:text;-webkit-user-select:text;pointer-events:auto}
#admin-password:focus,#admin-retention:focus,#admin-file-limit:focus,#admin-ban-ip:focus,.admin-channel-row input:focus{outline:none;border-color:rgba(10,132,255,.55);box-shadow:0 0 0 4px rgba(10,132,255,.12),inset 0 1px 1px #fff}
.avatar-initial{--avatar-from:#4ca4ff;--avatar-to:#0a74e8;color:#fff!important;border-color:rgba(255,255,255,.88)!important;background:linear-gradient(145deg,var(--avatar-from),var(--avatar-to))!important;box-shadow:0 6px 16px rgba(40,78,116,.18),inset 0 1px 1px rgba(255,255,255,.42)!important;font-family:var(--font);font-weight:750;line-height:1;text-shadow:0 1px 2px rgba(0,0,0,.26);text-transform:uppercase;user-select:none}
.avatar.avatar-initial{font-size:18px}
.user-row-avatar.avatar-initial{width:24px;height:24px;border:1px solid rgba(255,255,255,.88);border-radius:9px;display:grid;place-items:center;font-size:11px}
.message-avatar.avatar-initial{font-size:13px}
.transfer-task{position:absolute;z-index:12;left:24px;right:24px;bottom:94px;padding:12px 14px;border:1px solid rgba(255,255,255,.82);border-radius:20px;color:var(--lan-dark);background:linear-gradient(145deg,rgba(255,255,255,.84),rgba(232,242,252,.66));box-shadow:0 14px 36px rgba(37,67,96,.18),inset 0 1px 1px #fff;backdrop-filter:blur(18px) saturate(135%)}
.transfer-task[hidden]{display:none}
.transfer-task-head{display:grid;grid-template-columns:minmax(0,1fr) auto;gap:12px;align-items:center}
.transfer-task-name{overflow:hidden;color:#15212d;font-size:13px;font-weight:750;text-overflow:ellipsis;white-space:nowrap}
.transfer-task-status{margin-top:3px;color:#53677a;font-size:12px}
.transfer-task-actions{display:flex;gap:6px}
.transfer-task-button{position:relative;z-index:2;width:36px;min-width:36px;height:36px;padding:0;border-radius:13px;color:#24445f;background:rgba(255,255,255,.66);pointer-events:auto;touch-action:manipulation}
.transfer-task-button .lucide{width:17px;height:17px}
.transfer-task-track{height:6px;margin-top:10px;overflow:hidden;border-radius:999px;background:rgba(56,87,113,.13)}
.transfer-task-progress{width:0;height:100%;border-radius:inherit;background:linear-gradient(90deg,#52a8ee,#397bb7);box-shadow:0 0 12px rgba(61,139,205,.35);transition:width .2s ease}
@media (max-width:700px){.transfer-task{left:10px;right:10px;bottom:82px;padding:10px 12px;border-radius:17px}
}
.performance-lite .transfer-task{backdrop-filter:none}
.typing-indicator{position:absolute;left:24px;bottom:3px;max-width:45%;overflow:hidden;color:#526a7e;font-size:12px;font-weight:650;text-overflow:ellipsis;white-space:nowrap}
.typing-indicator[hidden]{display:none}
.message-status{color:#60778a;font-size:10px;font-weight:650;white-space:nowrap}
@media (max-width:700px){.typing-indicator{left:10px;max-width:130px;font-size:11px}
header .status span{display:none}
}
body{background-color:#edf4fa;background-image:linear-gradient(rgba(71,116,154,.09) 1px,transparent 1px),linear-gradient(90deg,rgba(71,116,154,.09) 1px,transparent 1px),radial-gradient(circle at 12% 8%,rgba(255,255,255,.92),transparent 32%),radial-gradient(circle at 88% 82%,rgba(139,184,222,.18),transparent 36%);background-size:32px 32px,32px 32px,auto,auto;background-attachment:fixed}
header,.profile-panel,.chat,.room-panel{border:0!important;border-radius:0!important;background:transparent!important;box-shadow:none!important;backdrop-filter:none!important;-webkit-backdrop-filter:none!important}
header{height:56px;margin:0 2px!important;padding:0 18px!important}
main{gap:24px}
.profile-panel,.room-panel{padding-top:24px}
.chat{overflow:hidden}
.chat-top,.messages{border:0!important;background:transparent!important}
.composer{margin:0 12px 16px!important;padding:0!important;gap:10px!important;border:0!important;border-radius:0!important;background:transparent!important;box-shadow:none!important;backdrop-filter:none!important;-webkit-backdrop-filter:none!important}
.composer:focus-within{border-color:transparent!important;box-shadow:none!important}
#message{height:46px;min-height:46px;padding:0 4px!important;border:0!important;border-bottom:1px solid rgba(72,104,132,.35)!important;border-radius:0!important;background:transparent!important;box-shadow:none!important}
#message:focus{border-bottom-color:var(--ios-blue)!important;box-shadow:none!important}
#send{width:auto!important;min-width:auto!important;height:46px!important;padding:0 6px!important;color:var(--ios-blue)!important;border:0!important;border-radius:0!important;background:transparent!important;box-shadow:none!important}
#send:hover,#send:active{transform:none!important;background:transparent!important;box-shadow:none!important}
.emoji-toggle,.file-toggle{width:42px!important;min-width:42px!important;height:42px!important;padding:0!important;color:var(--ios-ink)!important;border:1px solid rgba(255,255,255,.9)!important;border-radius:19px!important;background:radial-gradient(circle at 22% 0%,rgba(255,255,255,.95),transparent 46%),linear-gradient(145deg,rgba(255,255,255,.72),rgba(226,239,251,.48))!important;box-shadow:0 7px 18px rgba(42,68,94,.11),inset 0 1px 1px #fff,inset 0 -1px 0 rgba(255,255,255,.3)!important;backdrop-filter:none!important;-webkit-backdrop-filter:none!important}
.emoji-wrap{width:42px!important;min-width:42px!important;height:42px!important;flex:0 0 42px!important;display:grid;place-items:center}
.emoji-toggle,.file-toggle{display:grid!important;place-items:center!important;box-sizing:border-box!important;aspect-ratio:1}
.emoji-toggle .lucide,.file-toggle .lucide{color:var(--ios-blue)}
.emoji-toggle:hover,.file-toggle:hover,.emoji-toggle[aria-expanded="true"]{color:var(--ios-blue)!important;border-color:#fff!important;background:radial-gradient(circle at 25% 0%,#fff,transparent 48%),linear-gradient(145deg,rgba(255,255,255,.86),rgba(222,239,254,.62))!important;box-shadow:0 9px 22px rgba(41,76,108,.14),inset 0 1px 1px #fff!important}
.identity,.search-shell,.mobile-channel-select,.channel-button,.user-row,.metric,.rules{background-color:rgba(255,255,255,.16)!important}
.message-bubble,.emoji-panel,.transfer-task,.modal,.file-download{position:relative;z-index:0;isolation:isolate;overflow:hidden;border-color:transparent!important;background:linear-gradient(135deg,rgba(255,255,255,.42),rgba(255,255,255,.14))!important;box-shadow:inset 0 1px 0 rgba(255,255,255,.7),inset 0 -1px 0 rgba(255,255,255,.25),inset 5px 5px 15px rgba(255,255,255,.12),0 10px 28px rgba(55,83,108,.15)!important;backdrop-filter:blur(12px) saturate(1.18)!important;-webkit-backdrop-filter:blur(12px) saturate(1.18)!important}
.message-bubble::before,.transfer-task::before,.file-download::before{content:"";position:absolute;z-index:-1;inset:-42%;pointer-events:none;opacity:.9;background:radial-gradient(ellipse at 20% 18%,rgba(255,255,255,.92),transparent 18%),radial-gradient(ellipse at 77% 74%,rgba(122,191,241,.34),transparent 27%),linear-gradient(118deg,transparent 25%,rgba(255,255,255,.5) 47%,transparent 66%);background-size:150% 150%;transform:translate3d(-4%,-2%,0) rotate(-5deg)}
html.performance-lite .message-bubble::before,html.performance-lite .transfer-task::before,html.performance-lite .file-download::before{opacity:.54}
.channel-button.active{color:var(--ios-blue)!important;border-color:transparent!important;background:transparent!important;box-shadow:none!important;backdrop-filter:none!important;-webkit-backdrop-filter:none!important;isolation:auto;overflow:visible}
.channel-button.active::before{display:none!important}
.channel-button.active>span:first-child{font-weight:750}
.channel-button.active .channel-count{color:var(--ios-secondary)!important;font-weight:500}
.user-row.active{color:var(--ios-secondary)!important;border-color:transparent!important;background:transparent!important;box-shadow:none!important;backdrop-filter:none!important;-webkit-backdrop-filter:none!important;isolation:auto;overflow:visible}
.user-row.active::before{display:none!important}
.user-row.active .user-row-name{color:var(--ios-blue);font-weight:750}
.identity{margin-left:-6px;align-items:center!important;border:0!important;border-radius:0!important;background:transparent!important;box-shadow:none!important;backdrop-filter:none!important;-webkit-backdrop-filter:none!important;overflow:visible!important}
.identity>div:last-child{min-width:0;align-self:stretch;display:flex;flex-direction:column;justify-content:center}
.identity::before{display:none}
.metric,.rules{border-radius:0!important;background:transparent!important;box-shadow:none!important;backdrop-filter:none!important;-webkit-backdrop-filter:none!important}
.rules #retention-rule{color:inherit!important;font-weight:500!important}
body.mobile-users-open .profile-panel .mobile-users-close{display:grid!important;place-items:center;text-align:center}
.chat{position:relative}
.transfer-task{position:absolute!important;z-index:16!important;left:clamp(12px,2vw,24px)!important;right:clamp(12px,2vw,24px)!important;width:auto!important;max-width:calc(100% - clamp(24px,4vw,48px))!important;min-width:0;box-sizing:border-box}
.transfer-task-head,.transfer-task-head>div:first-child,.transfer-task-status,.transfer-task-track{min-width:0;max-width:100%}
.transfer-task-status{overflow-wrap:anywhere}
.transfer-task-progress{max-width:100%}
.modal-backdrop{padding:clamp(10px,3vw,24px);overflow:auto;overscroll-behavior:contain}
.modal,.modal.admin-modal-wide{width:min(100%,460px);max-width:calc(100vw - clamp(20px,6vw,48px));min-width:0;max-height:calc(100dvh - clamp(20px,6vw,48px));box-sizing:border-box;overflow-x:hidden}
.modal.admin-modal-wide.tools-open{width:min(100%,1080px)}
.modal input,.modal select,.admin-tool-panel,.admin-tools-layout,.admin-channel-row,.admin-ban-entry,.modal-actions{min-width:0;max-width:100%;box-sizing:border-box}
.modal-actions{flex-wrap:wrap}.modal-actions button{min-width:0;flex:1 1 96px}
.admin-tools-layout{grid-template-columns:repeat(3,minmax(0,1fr))!important}.admin-tool-panel{overflow-wrap:anywhere}
@media (max-width:900px){.admin-tools-layout{grid-template-columns:repeat(2,minmax(0,1fr))!important}}
@media (max-width:620px){.admin-tools-layout{grid-template-columns:minmax(0,1fr)!important}.admin-ban-tools{grid-column:auto!important}.modal,.modal.admin-modal-wide,.modal.admin-modal-wide.tools-open{max-width:calc(100vw - 20px);padding:clamp(14px,4vw,20px)}.admin-channel-row{grid-template-columns:64px minmax(0,1fr) 56px;gap:6px}.transfer-task{left:10px!important;right:10px!important;max-width:calc(100% - 20px)!important}.transfer-task-actions{gap:4px}.transfer-task-button{width:34px;min-width:34px;height:34px}}
@media (max-width:700px){main{gap:0;grid-template-rows:minmax(0,1fr)!important}header{padding:0 12px!important}main>.profile-panel{display:none}.room-panel{padding-top:18px}.chat{grid-template-rows:52px minmax(0,1fr) 72px}.chat-top{grid-template-columns:minmax(0,1fr) minmax(0,1.12fr) 58px!important;gap:6px!important;padding:0 10px!important}.mobile-channel-select{height:38px!important;padding:0 8px!important;font-size:11px}.mobile-users-toggle{width:58px!important;max-width:58px!important;height:38px!important;padding:0 5px!important;font-size:11px}.composer{margin:0 8px 12px!important}.emoji-wrap,#send,.file-toggle{width:42px!important;min-width:42px!important;max-width:42px!important;flex-basis:42px!important}#send{padding:0!important}#send .send-label{display:none}body.mobile-users-open main>.profile-panel{display:flex}body.mobile-users-open .profile-panel{border:0!important;border-radius:0!important;background:rgba(235,246,255,.8)!important;backdrop-filter:blur(18px)!important;-webkit-backdrop-filter:blur(18px)!important}}
:where(.modal,.admin-tool-panel,.admin-tools-layout,.admin-channels,.admin-settings,.admin-ban-tools,.banned-list,.banned-row,.admin-ban-entry,.message,.message-bubble,.message-file,.file-download,.emoji-panel,.toast-message,.transfer-task,.blocker-card){min-width:0;max-width:100%;box-sizing:border-box}
.admin-tool-panel{overflow:hidden}.admin-tools-layout{width:100%}
.admin-tool-panel{contain:layout style;border-color:transparent!important;background:transparent!important;box-shadow:none!important;backdrop-filter:none!important;-webkit-backdrop-filter:none!important}
#admin-modal{background:rgba(45,63,82,.32)!important;backdrop-filter:none!important;-webkit-backdrop-filter:none!important}
.modal.admin-modal-wide.tools-open{background:linear-gradient(145deg,rgba(248,252,255,.97),rgba(225,238,249,.94))!important;box-shadow:0 18px 48px rgba(45,69,94,.18),inset 0 1px 0 #fff!important;backdrop-filter:none!important;-webkit-backdrop-filter:none!important}
.banned-list{width:100%;overflow-x:hidden;overscroll-behavior-inline:contain}.banned-row{width:100%;grid-template-columns:minmax(0,1fr) 56px;overflow:hidden}.banned-row>span{min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}.banned-row button{width:56px;min-width:56px}
.message-bubble{width:fit-content!important;min-width:min(140px,100%)!important;max-width:100%!important;font-size:13px}.message-file{width:min(360px,100%);min-width:0!important;max-width:100%}.file-download{min-width:0;max-width:100%}
.emoji-panel{position:absolute!important;top:auto!important;right:auto!important;bottom:calc(100% + 12px)!important;left:0!important;width:min(292px,calc(100vw - 24px))!important;max-width:calc(100vw - 24px)!important;transform-origin:left bottom}
#admin-tools>.modal-actions{justify-content:flex-end;margin-top:4px}#admin-tools>.modal-actions button{flex:0 0 auto;min-width:78px;height:36px;padding:0 14px;color:var(--ios-ink);border:1px solid rgba(255,255,255,.7);border-radius:14px;background:rgba(255,255,255,.28);box-shadow:inset 0 1px 0 rgba(255,255,255,.72),0 5px 14px rgba(42,68,94,.1);backdrop-filter:none;-webkit-backdrop-filter:none}#admin-tools>.modal-actions button:hover{color:var(--ios-blue);background:rgba(255,255,255,.48);transform:none}
#user-modal{background:rgba(83,108,133,.12);backdrop-filter:blur(7px) saturate(1.08);-webkit-backdrop-filter:blur(7px) saturate(1.08)}#user-modal .modal{border:1px solid rgba(255,255,255,.68)!important;background:linear-gradient(145deg,rgba(255,255,255,.28),rgba(223,239,252,.1))!important;box-shadow:inset 0 1px 0 rgba(255,255,255,.82),inset 0 -1px 0 rgba(255,255,255,.2),0 22px 58px rgba(45,69,94,.18)!important}#user-modal .modal::after{content:"";position:absolute;inset:0;z-index:-1;pointer-events:none;border-radius:inherit;background:radial-gradient(circle at 14% 0%,rgba(255,255,255,.72),transparent 34%),radial-gradient(circle at 88% 100%,rgba(116,187,240,.2),transparent 38%)}#user-modal .modal-actions button{color:var(--ios-ink);border:1px solid rgba(255,255,255,.7);background:rgba(255,255,255,.2);box-shadow:inset 0 1px 0 rgba(255,255,255,.76),0 6px 16px rgba(42,68,94,.1)}#user-modal .modal-actions button:hover{color:var(--ios-blue);background:rgba(255,255,255,.4);transform:none}
.user-admin-button{color:var(--ios-secondary)!important;border:0!important;border-radius:0!important;background:transparent!important;box-shadow:none!important;backdrop-filter:none!important;-webkit-backdrop-filter:none!important}
.user-admin-button:hover,.user-admin-button:active{color:var(--ios-blue)!important;background:transparent!important;box-shadow:none!important;transform:none!important}
.user-admin-button:focus-visible{outline:2px solid rgba(10,132,255,.45);outline-offset:-5px}
@media (max-width:420px){.banned-row{grid-template-columns:minmax(0,1fr) 52px}.banned-row button{width:52px;min-width:52px}.admin-ban-entry{grid-template-columns:minmax(0,1fr) 62px}.admin-ban-entry button{padding:0 6px}#admin-tools>.modal-actions button{min-width:72px;height:34px;padding:0 12px}}
.chat-top>.identity{display:none}
@media (max-width:700px){.chat-top>.identity{width:auto!important;min-width:0;height:38px;margin:0!important;padding:0!important;display:grid;grid-template-columns:28px minmax(0,1fr);gap:5px;align-items:center;overflow:visible!important}.chat-top>.identity .avatar{width:28px;height:28px;border-radius:10px!important;font-size:11px!important}.chat-top>.identity>div:last-child{min-width:0;display:block}.chat-top>.identity small{display:none}.chat-top>.identity input{width:100%;min-width:0;height:38px;padding:0 8px;color:var(--ios-ink);border:1px solid rgba(255,255,255,.76);border-radius:15px;background:rgba(255,255,255,.43);box-shadow:inset 0 1px 1px rgba(255,255,255,.92);font-family:var(--font);font-size:12px;font-weight:600;caret-color:var(--ios-blue)}.chat-top>.identity input:focus{outline:none;border-color:rgba(10,132,255,.55);box-shadow:0 0 0 3px rgba(10,132,255,.1),inset 0 1px 1px #fff}}
.rules{display:grid;gap:11px;padding-top:17px!important;color:var(--ios-secondary)!important;font:11px/1.55 var(--font)!important;letter-spacing:0!important}
.rules-title{display:flex;align-items:center;gap:7px;color:var(--ios-ink);font-size:12px;font-weight:750;letter-spacing:.08em}
.rules-title .lucide{width:15px;height:15px;color:var(--ios-blue);stroke-width:2}
.rules-list{display:grid;gap:7px;margin:0;padding:0;list-style:none}
.rules-list li{position:relative;margin:0;padding-left:13px;overflow-wrap:anywhere}
.rules-list li::before{content:'';position:absolute;left:0;top:.62em;width:4px;height:4px;border-radius:50%;background:var(--ios-blue);box-shadow:0 0 0 3px rgba(10,132,255,.08)}
.rules-list b,.rules-list #retention-rule{color:var(--ios-ink)!important;font-weight:650!important}
.rules-note{padding-top:9px;border-top:1px solid rgba(118,118,128,.14);color:var(--ios-tertiary);font-size:10px;line-height:1.55}
.header-actions{display:flex;align-items:center;gap:10px}.notification-toggle{width:34px!important;min-width:34px!important;height:34px!important;padding:0!important;display:grid!important;place-items:center;color:var(--ios-secondary)!important;border:0!important;border-radius:50%!important;background:transparent!important;box-shadow:none!important}.notification-toggle:hover{color:var(--ios-blue)!important;transform:none!important;background:rgba(255,255,255,.34)!important}.notification-toggle.enabled{color:var(--ios-blue)!important}.notification-toggle .lucide{width:17px;height:17px}
.message-name.mention-target{cursor:pointer}.message-name.mention-target:hover{text-decoration:underline}.message-reply{display:flex;flex-direction:column;gap:1px;margin:-2px 0 8px;padding:6px 9px;border-left:3px solid var(--ios-blue);border-radius:8px;background:rgba(255,255,255,.3);white-space:normal}.message-reply[hidden]{display:none}.message-reply b{overflow:hidden;color:var(--ios-blue);font-size:10px;line-height:1.4;text-overflow:ellipsis;white-space:nowrap}.message-reply span{display:block;max-width:42ch;overflow:hidden;color:var(--ios-secondary);font-size:11px;line-height:1.4;text-overflow:ellipsis;white-space:nowrap}.message.self .message-reply{border-left-color:rgba(10,132,255,.72);background:rgba(255,255,255,.38)}.message.mentioned .message-bubble{box-shadow:inset 0 0 0 2px rgba(255,149,0,.5),0 10px 28px rgba(255,149,0,.16)!important}
.reply-preview{position:absolute;left:0;right:0;bottom:calc(100% + 8px);min-width:0;padding:8px 10px 8px 13px;display:flex;align-items:center;justify-content:space-between;gap:10px;border:1px solid rgba(255,255,255,.86);border-left:3px solid var(--ios-blue);border-radius:15px;background:rgba(244,250,255,.94);box-shadow:0 9px 24px rgba(43,66,92,.14);backdrop-filter:blur(12px);-webkit-backdrop-filter:blur(12px)}.reply-preview[hidden]{display:none}.reply-preview>div{min-width:0;display:flex;flex-direction:column}.reply-preview b{color:var(--ios-blue);font-size:11px}.reply-preview span{overflow:hidden;color:var(--ios-secondary);font-size:11px;text-overflow:ellipsis;white-space:nowrap}.reply-preview button{width:30px!important;min-width:30px!important;height:30px!important;padding:0!important;border:0!important;border-radius:50%!important;background:transparent!important;box-shadow:none!important}.reply-preview button:hover{color:var(--ios-blue)!important;transform:none!important;background:rgba(10,132,255,.08)!important}.reply-preview .lucide{width:15px;height:15px}
.chat.file-dragging::after{content:'松开发送文件';position:absolute;z-index:18;inset:12px;display:grid;place-items:center;border:2px dashed rgba(10,132,255,.65);border-radius:24px;color:var(--ios-blue);background:rgba(239,248,255,.9);font-size:18px;font-weight:750;letter-spacing:.08em;pointer-events:none;backdrop-filter:blur(9px);-webkit-backdrop-filter:blur(9px)}
.message-file.has-image{grid-template-areas:'preview preview' 'name download' 'meta download';width:min(360px,100%)}.file-image-button{grid-area:preview;width:100%!important;min-width:0!important;height:auto!important;max-height:none!important;margin:0 0 9px;padding:0!important;display:block;overflow:hidden;border:0!important;border-radius:14px!important;background:rgba(255,255,255,.3)!important;box-shadow:none!important;line-height:0}.file-image-button[hidden]{display:none}.file-image-button:hover{transform:none!important;box-shadow:0 6px 18px rgba(35,70,105,.16)!important}.file-image{display:block;width:100%;max-height:240px;object-fit:contain;background:rgba(22,35,48,.08);cursor:zoom-in}.image-preview-modal{z-index:40;background:rgba(10,16,23,.88)!important;backdrop-filter:blur(10px)!important;-webkit-backdrop-filter:blur(10px)!important}.image-preview-frame{position:relative;width:min(94vw,1280px);height:min(90vh,900px);display:grid;grid-template-rows:minmax(0,1fr) auto;place-items:center;gap:10px}.image-preview-image{display:block;max-width:100%;max-height:calc(90vh - 52px);object-fit:contain;border-radius:12px;box-shadow:0 22px 70px rgba(0,0,0,.46)}.image-preview-caption{max-width:min(90vw,760px);overflow:hidden;color:#fff;font-size:13px;text-overflow:ellipsis;white-space:nowrap}.image-preview-close{position:absolute!important;z-index:2;top:0;right:0;width:42px!important;min-width:42px!important;height:42px!important;padding:0!important;display:grid!important;place-items:center;color:#fff!important;border:1px solid rgba(255,255,255,.35)!important;border-radius:50%!important;background:rgba(12,18,25,.55)!important;box-shadow:none!important}.image-preview-close:hover{transform:none!important;background:rgba(255,255,255,.2)!important}.image-preview-close .lucide{width:20px;height:20px}
.channel-meta{display:flex;align-items:center;gap:7px}.channel-unread{min-width:18px;height:18px;padding:0 5px;display:grid;place-items:center;border-radius:9px;color:#fff;background:#ff3b30;font-size:10px;font-weight:750;line-height:1;box-shadow:0 0 0 2px rgba(255,59,48,.1)}
.message-reactions{display:flex;flex-wrap:wrap;gap:5px;margin-top:8px;white-space:normal}.message-reactions[hidden]{display:none}.reaction-button{width:auto!important;min-width:34px!important;height:25px!important;padding:0 8px!important;border:1px solid rgba(90,112,132,.16)!important;border-radius:999px!important;color:var(--ios-secondary)!important;background:rgba(255,255,255,.28)!important;box-shadow:none!important;font-size:12px!important;line-height:1!important;letter-spacing:0!important}.reaction-button:hover{color:var(--ios-blue)!important;border-color:rgba(10,132,255,.28)!important;background:rgba(255,255,255,.52)!important;transform:none!important;box-shadow:none!important}.reaction-button.active{color:var(--ios-blue)!important;border-color:rgba(10,132,255,.34)!important;background:rgba(10,132,255,.12)!important}.message.self .reaction-button{background:rgba(255,255,255,.42)!important}.message.jump-highlight .message-bubble{box-shadow:0 0 0 4px rgba(230,162,60,.48),0 12px 34px rgba(230,162,60,.2)!important}
.message-reply{width:100%!important;min-width:0!important;height:auto!important;text-align:left!important;color:inherit!important;border:0!important;border-left:3px solid var(--ios-blue)!important;box-shadow:none!important;letter-spacing:0!important;cursor:pointer}.message-reply:hover{transform:none!important;box-shadow:none!important;background:rgba(255,255,255,.5)!important}
@media (max-width:700px){.header-actions{gap:5px}.notification-toggle{width:30px!important;min-width:30px!important;height:30px!important}.reply-preview{left:-2px;right:-2px}.message-reply span{max-width:26ch}}
</style>
</head>
<body>
  <svg width="0" height="0" aria-hidden="true" style="position:absolute;overflow:hidden">
    <defs>
      <symbol id="lucide-radio" viewBox="0 0 24 24"><path d="M4.9 19.1a10 10 0 0 1 0-14.2M7.8 16.2a6 6 0 0 1 0-8.5M12 13a1 1 0 1 0 0-2 1 1 0 0 0 0 2Z"/><path d="M16.2 7.8a6 6 0 0 1 0 8.5M19.1 4.9a10 10 0 0 1 0 14.2"/></symbol>
      <symbol id="lucide-users" viewBox="0 0 24 24"><path d="M16 21v-2a4 4 0 0 0-4-4H6a4 4 0 0 0-4 4v2M9 11a4 4 0 1 0 0-8 4 4 0 0 0 0 8ZM22 21v-2a4 4 0 0 0-3-3.87M16 3.13a4 4 0 0 1 0 7.75"/></symbol>
      <symbol id="lucide-chevron-left" viewBox="0 0 24 24"><path d="m15 18-6-6 6-6"/></symbol>
      <symbol id="lucide-chevron-right" viewBox="0 0 24 24"><path d="m9 18 6-6-6-6"/></symbol>
      <symbol id="lucide-x" viewBox="0 0 24 24"><path d="M18 6 6 18M6 6l12 12"/></symbol>
      <symbol id="lucide-smile" viewBox="0 0 24 24"><circle cx="12" cy="12" r="10"/><path d="M8 14s1.5 2 4 2 4-2 4-2M9 9h.01M15 9h.01"/></symbol>
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
      <symbol id="lucide-pause" viewBox="0 0 24 24"><rect width="4" height="16" x="6" y="4" rx="1"/><rect width="4" height="16" x="14" y="4" rx="1"/></symbol>
      <symbol id="lucide-play" viewBox="0 0 24 24"><path d="m6 3 14 9-14 9Z"/></symbol>
      <symbol id="lucide-reply" viewBox="0 0 24 24"><path d="m9 17-5-5 5-5"/><path d="M20 18v-2a4 4 0 0 0-4-4H4"/></symbol>
      <symbol id="lucide-bell" viewBox="0 0 24 24"><path d="M10.3 21a2 2 0 0 0 3.4 0M18 8a6 6 0 0 0-12 0c0 7-3 7-3 9h18c0-2-3-2-3-9"/></symbol>
      <symbol id="lucide-bell-off" viewBox="0 0 24 24"><path d="m2 2 20 20M6.3 6.3A6 6 0 0 0 6 8c0 7-3 7-3 9h14M10.3 21a2 2 0 0 0 3.4 0M18 13.7V8a6 6 0 0 0-8.7-5.4M18 18H9"/></symbol>
    </defs>
  </svg>
  <div class="shell">
    <header><div class="brand"><div class="brand-lockup"><span class="brand-icon"><svg class="lucide"><use href="#lucide-radio"></use></svg></span><span>LAN / CHAT</span><span class="brand-index">LIQUID LOCAL MESSENGER</span></div></div><div class="header-actions"><button class="notification-toggle" id="notification-toggle" type="button" title="开启桌面通知" aria-label="开启桌面通知"><svg class="lucide"><use href="#lucide-bell-off"></use></svg></button><div class="status"><i class="pulse"></i><span id="connection">正在连接</span></div></div></header>
    <main>
      <aside class="profile-panel">
        <div><div class="kicker" id="kicker">LOCAL / 001</div><h1>轻声落下，<br>即刻消散。</h1><div class="intro">同一网络中的短暂信号。没有账号，没有档案，只留下此刻的回声。</div></div>
        <button class="mobile-users-close" id="mobile-users-close" type="button">返回聊天</button>
        <div class="identity"><div class="avatar" id="my-avatar"></div><div><small>YOUR SIGNAL</small><input id="my-name" maxlength="5" value="匿名访客" aria-label="编辑用户名"></div></div>
        <div class="user-directory"><div class="search-shell"><svg class="lucide"><use href="#lucide-search"></use></svg><input class="user-search" id="user-search" type="search" placeholder="检索在线用户" aria-label="搜索在线用户"></div><div class="user-list" id="user-list"></div></div>
      </aside>
      <section class="chat"><div class="chat-top"><div class="chat-title" id="channel-title">频道1（0）</div><div class="typing-indicator" id="typing-indicator" hidden></div><select class="mobile-channel-select" id="mobile-channel-select" aria-label="切换频道"></select><button class="mobile-users-toggle" id="mobile-users-toggle" type="button" aria-label="查看在线用户" aria-expanded="false"><svg class="lucide"><use href="#lucide-users"></use></svg><span>用户</span><span class="mobile-unread-count" id="mobile-unread-count" hidden></span></button></div><div class="messages" id="messages"><div class="messages-spacer" id="messages-spacer"><div class="messages-window" id="messages-window"></div></div></div><div class="transfer-task" id="transfer-task" hidden><div class="transfer-task-head"><div><div class="transfer-task-name" id="transfer-task-name"></div><div class="transfer-task-status" id="transfer-task-status"></div></div><div class="transfer-task-actions"><button class="transfer-task-button" id="transfer-pause" type="button" title="暂停上传" aria-label="暂停上传"><svg class="lucide"><use href="#lucide-pause"></use></svg></button><button class="transfer-task-button" id="transfer-cancel" type="button" title="取消上传" aria-label="取消上传"><svg class="lucide"><use href="#lucide-x"></use></svg></button></div></div><div class="transfer-task-track"><div class="transfer-task-progress" id="transfer-task-progress"></div></div></div><form class="composer" id="composer"><div class="reply-preview" id="reply-preview" hidden><div><b id="reply-preview-name"></b><span id="reply-preview-text"></span></div><button id="reply-cancel" type="button" title="取消回复" aria-label="取消回复"><svg class="lucide"><use href="#lucide-x"></use></svg></button></div><div class="emoji-wrap"><button class="emoji-toggle" id="emoji-toggle" type="button" aria-label="打开表情面板" aria-expanded="false"><svg class="lucide"><use href="#lucide-smile"></use></svg></button><div class="emoji-panel" id="emoji-panel" hidden></div></div><button class="file-toggle" id="file-toggle" type="button" title="发送文件（最大 1 MB，10 分钟后销毁）" aria-label="选择文件"><svg class="lucide"><use href="#lucide-paperclip"></use></svg></button><input class="file-input" id="file-input" type="file" tabindex="-1"><input id="message" maxlength="500" autocomplete="off" placeholder="说点什么……"><button id="send" type="submit"><span class="send-label">发送</span><svg class="lucide"><use href="#lucide-send"></use></svg></button></form></section>
      <aside class="room-panel"><h2><svg class="lucide"><use href="#lucide-hash"></use></svg><span>CHANNELS</span></h2><div class="channel-list" id="channel-list"></div><div class="metric"><span class="metric-label">全站在线 / CAPACITY</span><div class="metric-value online-value"><span id="total-online">0</span> / 100</div></div><section class="rules" aria-label="温馨提示"><div class="rules-title"><svg class="lucide"><use href="#lucide-info"></use></svg><span>温馨提示</span></div><ul class="rules-list"><li><span id="retention-rule">消息与中转文件将在 10 分钟后自动销毁</span></li><li>消息发送后 <b>3 分钟内</b>可以撤回</li><li>点击昵称可快速 <b>@用户</b>，消息下方支持回复与表情回应</li><li>可拖放、粘贴或点击回形针发送文件，<b id="file-limit-rule">单文件上限 1 MB</b></li><li>支持的图片会直接显示，点击即可放大预览</li><li>每 5 秒最多发送 <b>2 条</b>文字或文件消息</li></ul><div class="rules-note">这里没有服务端账号，重要内容请在自动销毁前及时保存。</div></section><div class="room-admin-entry"><div class="admin-status" id="admin-status" hidden></div><div class="sync" id="refresh">等待同步</div></div></aside>
    </main>
  </div>
  <div class="toast-host" id="toast-host" aria-live="polite" aria-atomic="true"></div>
  <button class="fab-admin" id="fab-admin" type="button" hidden><svg class="lucide"><use href="#lucide-shield-check"></use></svg><span>验证管理员</span></button>
  <div class="modal-backdrop" id="admin-modal" hidden>
    <div class="modal admin-modal-wide">
      <h2 id="admin-modal-title">验证管理员</h2>
      <div id="admin-login"><input id="admin-password" type="password" autocomplete="current-password" placeholder="输入管理员密码"><div class="modal-actions"><button type="button" data-close="admin-modal">取消</button><button type="button" id="admin-login-button">验证</button></div></div>
      <div id="admin-tools" hidden>
        <div class="admin-tools-layout">
          <section class="admin-tool-panel"><h3>频道名称</h3><div class="admin-channels" id="admin-channels"></div></section>
          <section class="admin-tool-panel">
            <h3>内容限制</h3>
            <div class="admin-settings">
              <label class="admin-setting-row"><span>消息与文件销毁时间（分钟）</span><input id="admin-retention" type="text" inputmode="numeric" pattern="[0-9]*" maxlength="4" value="10" autocomplete="off" aria-label="销毁时间，单位分钟，仅允许输入数字"></label>
              <label class="admin-setting-row"><span>单个文件大小上限（MB，最高 20 GB）</span><input id="admin-file-limit" type="text" inputmode="numeric" pattern="[0-9]*" maxlength="5" value="1" autocomplete="off" aria-label="文件大小上限，单位 MB，最高 20 GB，仅允许输入数字"></label>
              <button class="admin-settings-save" type="button" id="admin-settings-save">应用设置</button>
              <p class="admin-settings-note">可输入 1–1440 分钟和 1–20480 MB（20 GB）。设置实时同步给所有在线用户，并在服务重启后继续生效。</p>
            </div>
          </section>
          <section class="admin-tool-panel admin-ban-tools"><h3>IP 封禁管理</h3><div class="admin-ban-entry"><input id="admin-ban-ip" placeholder="输入 IP 地址" aria-label="要封禁的 IP 地址"><button type="button" id="admin-ban-button">封禁</button></div><div class="banned-list" id="banned-list"></div></section>
        </div>
        <div class="modal-actions"><button type="button" data-close="admin-modal">完成</button></div>
      </div>
    </div>
  </div>
  <div class="modal-backdrop" id="user-modal" hidden><div class="modal"><h2>用户信息</h2><div class="user-detail" id="user-detail">正在读取</div><div class="modal-actions user-modal-actions"><button type="button" id="user-ban-button" hidden>封禁此 IP</button><button type="button" data-close="user-modal">关闭</button></div></div></div>
  <div class="modal-backdrop image-preview-modal" id="image-preview-modal" hidden><div class="image-preview-frame"><button class="image-preview-close" id="image-preview-close" type="button" title="关闭图片预览" aria-label="关闭图片预览"><svg class="lucide"><use href="#lucide-x"></use></svg></button><img class="image-preview-image" id="image-preview-image" alt="图片预览"><div class="image-preview-caption" id="image-preview-caption"></div></div></div>
  <div class="blocker" id="blocker" hidden><div class="blocker-card"><h2 id="blocker-title">ROOM IS FULL</h2><p id="blocker-message">当前聊天室同时在线已满，新的连接暂时无法进入。请稍后刷新再试，或等待现有连接超时释放。</p><div class="blocker-meta"><span id="blocker-meta-limit">LIMIT 100</span><span id="blocker-retry">RETRY IN 5s</span></div></div></div>
  <script>
    const names = ['雾中信号','午夜电台','路过的人','蓝色回声','未读消息','七号窗口','风的背面','纸上月光','无名之声','半格电量','雨后电台','凌晨三点','玻璃海岸','远方来客','静默频道','白噪音','南墙以北','小行星带','旧磁带','临时月亮','低空飞行','纸船渡口','橘色回声','没有署名','第九街角','慢速星球','失眠旅人','空白信笺','北纬三十','候车室里','微光入口','借过一下','晴天留声机','倒带之前','未完句号','晚风收件箱','路灯下面','隐身模式','落日存档','匿名观测员','月面漫步者','雨伞借我','发呆俱乐部','半夜醒来','蓝调星期五','海边的字','轻声路过','没有目的地','风筝线外','借来的名字'];
    const LOCAL_NAME_KEY = 'lan-chat.user-name.v1';
    const SESSION_ID_KEY = 'lan-chat.session-id.v1';
    const NOTIFICATION_KEY = 'lan-chat.desktop-notifications.v1';
    const BASE_TITLE = 'LAN CHAT';
    function normalizedName(value) { return Array.from(String(value||'').trim()).slice(0,5).join(''); }
    function readLocalName() {
      try { return normalizedName(localStorage.getItem(LOCAL_NAME_KEY)); }
      catch { return ''; }
    }
    function saveLocalName(value) {
      const name=normalizedName(value);
      try {
        if(name) localStorage.setItem(LOCAL_NAME_KEY,name);
        else localStorage.removeItem(LOCAL_NAME_KEY);
      } catch {}
      return name;
    }
    const localName=readLocalName();
    function sessionIdentityId() {
      let value=''; try { value=String(sessionStorage.getItem(SESSION_ID_KEY)||''); } catch {}
      if(!/^[a-z0-9-]{12,128}$/i.test(value)) value=crypto.randomUUID ? crypto.randomUUID() : Math.random().toString(36).slice(2)+Date.now().toString(36);
      try { sessionStorage.setItem(SESSION_ID_KEY,value); } catch {} return value;
    }
    const identity = { name:localName||names[Math.floor(Math.random()*names.length)], id:sessionIdentityId() };
    saveLocalName(identity.name);
    const state = { messages:[], users:[], typing:[], privateUnread:{}, previousPrivateUnread:{}, channelUnread:{}, previousChannelUnread:{}, privateActivity:{}, online:0, cursor:0, polling:false, uploading:false, uploadTask:null, nameEdited:false, mode:'channel', peer:null, channel:'channel1', channels:[], onlineByChannel:{}, adminToken:'', full:false, blockedReason:'', sendCooldownUntil:0, retentionMs:600000, recallWindowMs:180000, maxFileBytes:1048576, maxImagePreviewBytes:25*1024*1024, renderBatch:100, pollInterval:1500, blockRetry:5000, canAdmin:false, scrollLocked:true, replyingTo:null, notificationsEnabled:false, pageUnread:0, suppressIncomingOnce:true, previewingMessageId:'' };
    const RTC_DIRECT_MAX_BYTES=64*1024*1024;
    const rtcPeers=new Map(); const rtcAckWaiters=new Map(); const directFiles=new Map();
    const $ = id => document.getElementById(id);
    const renderCache = { channels:'', users:'' };
    const prefersLessMotion=matchMedia('(prefers-reduced-motion: reduce)').matches;
    const limitedCpu=Number(navigator.hardwareConcurrency||8)<=4;
    const limitedMemory=Number(navigator.deviceMemory||8)<=4;
    document.documentElement.classList.toggle('performance-lite',prefersLessMotion||limitedCpu||limitedMemory);
    const availableIcons = new Set(['radio','users','smile','chevron-left','chevron-right','x','paperclip','send','copy','rotate-ccw','download','settings-2','shield-check','check','info','triangle-alert','circle-x','search','hash','pause','play','reply','bell','bell-off']);
    function iconNode(name, className='lucide') {
      const safe=availableIcons.has(name)?name:'radio';
      const svg=document.createElementNS('http://www.w3.org/2000/svg','svg');
      svg.setAttribute('class',className); svg.setAttribute('aria-hidden','true');
      const use=document.createElementNS('http://www.w3.org/2000/svg','use');
      use.setAttribute('href','#lucide-'+safe); svg.append(use); return svg;
    }
    function setIcon(target,name) {
      const safe=availableIcons.has(name)?name:'radio';
      if(target.dataset.icon===safe&&target.childElementCount===1) return;
      target.replaceChildren(iconNode(safe));
      target.dataset.icon=safe;
    }
    function setupLiquidRefraction() {
      const selector='.message-bubble,.file-download,.transfer-task,.modal:not(.tools-open),#user-modal .modal-actions button';
      const supports=CSS.supports('backdrop-filter','url("#liquid-test") blur(.25px)')||CSS.supports('-webkit-backdrop-filter','url("#liquid-test") blur(.25px)');
      if(!supports||document.documentElement.classList.contains('performance-lite')||!window.ResizeObserver) return;
      const NS='http://www.w3.org/2000/svg';
      const svg=document.createElementNS(NS,'svg'); svg.setAttribute('width','0'); svg.setAttribute('height','0'); svg.setAttribute('aria-hidden','true'); svg.style.cssText='position:fixed;inset:0;pointer-events:none';
      const defs=document.createElementNS(NS,'defs'); svg.append(defs); document.body.append(svg);
      const maps=new Map(),tracked=new Set(); let scheduled=0;
      const smooth=(a,b,t)=>{t=Math.max(0,Math.min(1,(t-a)/(b-a)));return t*t*(3-2*t)};
      const sdf=(x,y,w,h,r)=>{const qx=Math.abs(x)-w+r,qy=Math.abs(y)-h+r;return Math.min(Math.max(qx,qy),0)+Math.hypot(Math.max(qx,0),Math.max(qy,0))-r};
      function createMap(width,height) {
        const mapWidth=Math.min(180,Math.max(48,Math.round(width*.55))),mapHeight=Math.min(112,Math.max(32,Math.round(height*.55)));
        const canvas=document.createElement('canvas'); canvas.width=mapWidth; canvas.height=mapHeight;
        const context=canvas.getContext('2d'),image=context.createImageData(mapWidth,mapHeight),raw=new Float32Array(mapWidth*mapHeight*2); let max=1,index=0;
        const radius=Math.min(.2,.46*Math.min(1,height/Math.max(width,1))+.04);
        for(let y=0;y<mapHeight;y++) for(let x=0;x<mapWidth;x++) {
          const ux=x/mapWidth-.5,uy=y/mapHeight-.5,d=sdf(ux,uy,.47,.47,radius),edge=1-smooth(0,.16,Math.abs(d)),scale=1-edge*.2;
          const dx=(ux*scale+.5)*mapWidth-x,dy=(uy*scale+.5)*mapHeight-y; raw[index++]=dx; raw[index++]=dy; max=Math.max(max,Math.abs(dx),Math.abs(dy));
        }
        index=0;
        for(let i=0;i<image.data.length;i+=4) { image.data[i]=(raw[index++]/(max*2)+.5)*255; image.data[i+1]=(raw[index++]/(max*2)+.5)*255; image.data[i+2]=128; image.data[i+3]=255; }
        context.putImageData(image,0,0);
        const id='liquid-ui-'+maps.size,filter=document.createElementNS(NS,'filter'),map=document.createElementNS(NS,'feImage'),displace=document.createElementNS(NS,'feDisplacementMap');
        filter.id=id; filter.setAttribute('filterUnits','userSpaceOnUse'); filter.setAttribute('color-interpolation-filters','sRGB'); filter.setAttribute('x',String(-width*.08)); filter.setAttribute('y',String(-height*.08)); filter.setAttribute('width',String(width*1.16)); filter.setAttribute('height',String(height*1.16));
        map.setAttribute('href',canvas.toDataURL()); map.setAttribute('width',String(width)); map.setAttribute('height',String(height)); map.setAttribute('preserveAspectRatio','none'); map.setAttribute('result','map');
        displace.setAttribute('in','SourceGraphic'); displace.setAttribute('in2','map'); displace.setAttribute('scale',String(Math.min(26,Math.max(12,max*1.5)))); displace.setAttribute('xChannelSelector','R'); displace.setAttribute('yChannelSelector','G');
        filter.append(map,displace); defs.append(filter); return id;
      }
      function apply(element) {
        const rect=element.getBoundingClientRect(); if(rect.width<8||rect.height<8) return;
        const width=Math.max(64,Math.round(rect.width/64)*64),height=Math.max(32,Math.round(rect.height/32)*32),key=width+'x'+height;
        let id=maps.get(key); if(!id) { id=createMap(width,height); maps.set(key,id); }
        const value='url("#'+id+'") blur(.35px) contrast(1.08) brightness(1.06) saturate(1.12)';
        element.style.setProperty('backdrop-filter',value,'important'); element.style.setProperty('-webkit-backdrop-filter',value,'important');
      }
      const resize=new ResizeObserver(entries=>entries.forEach(entry=>apply(entry.target)));
      function sync() {
        scheduled=0; const current=new Set(document.querySelectorAll(selector));
        tracked.forEach(element=>{if(!current.has(element)){resize.unobserve(element);element.style.removeProperty('backdrop-filter');element.style.removeProperty('-webkit-backdrop-filter');tracked.delete(element)}});
        current.forEach(element=>{if(!tracked.has(element)){tracked.add(element);resize.observe(element)} apply(element)});
      }
      const schedule=()=>{if(!scheduled) scheduled=requestAnimationFrame(sync)};
      new MutationObserver(schedule).observe(document.body,{subtree:true,childList:true,attributes:true,attributeFilter:['class','hidden']});
      sync();
    }
    setupLiquidRefraction();
    const avatarSegmenter=typeof Intl.Segmenter==='function'?new Intl.Segmenter('zh-CN',{granularity:'grapheme'}):null;
    const avatarColors=Array.from({length:50},(_,tone)=>{const hue=Math.round(210+tone*137.508)%360,saturation=62+tone%4*5,lightness=44+tone%3*3;return ['hsl('+hue+','+saturation+'%,'+lightness+'%)','hsl('+((hue+22)%360)+','+Math.min(82,saturation+5)+'%,'+(32+tone%2*4)+'%)'];});
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
      return hash%avatarColors.length;
    }
    function setAvatarInitial(target,name) {
      const value=String(name||'').trim()||'匿名';
      const initial=avatarInitial(value).toLocaleUpperCase('zh-CN');
      const toneIndex=avatarTone(value),tone=String(toneIndex);
      if(target.dataset.avatarInitial!==initial) target.textContent=initial;
      target.classList.add('avatar-initial');
      target.dataset.avatarInitial=initial;
      if(target.dataset.avatarTone!==tone) {
        const colors=avatarColors[toneIndex];
        target.dataset.avatarTone=tone;
        target.style.setProperty('--avatar-from',colors[0]);
        target.style.setProperty('--avatar-to',colors[1]);
      }
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
    function updateTitleReminder() {
      document.title=state.pageUnread?BASE_TITLE+' · 未读消息 '+state.pageUnread:BASE_TITLE;
    }
    function clearPageUnread() { state.pageUnread=0; updateTitleReminder(); }
    function addPageUnread(count=1) {
      if(!document.hidden&&document.hasFocus()) return;
      state.pageUnread=Math.min(999,state.pageUnread+Math.max(1,count));
      updateTitleReminder();
    }
    function notificationSupported() { return 'Notification' in window; }
    function saveNotificationPreference(enabled) { try { localStorage.setItem(NOTIFICATION_KEY,enabled?'1':'0'); } catch {} }
    function syncNotificationToggle() {
      const button=$('notification-toggle');
      const enabled=notificationSupported()&&Notification.permission==='granted'&&state.notificationsEnabled;
      state.notificationsEnabled=enabled;
      button.classList.toggle('enabled',enabled); setIcon(button,enabled?'bell':'bell-off');
      button.title=enabled?'桌面通知已开启，点击关闭':'开启桌面通知'; button.setAttribute('aria-label',button.title);
    }
    async function toggleDesktopNotifications() {
      if(!notificationSupported()) { showToast('当前浏览器不支持桌面通知','warning'); return; }
      if(state.notificationsEnabled) { state.notificationsEnabled=false; saveNotificationPreference(false); syncNotificationToggle(); showToast('桌面通知已关闭','info'); return; }
      let permission=Notification.permission;
      try { if(permission!=='granted') permission=await Notification.requestPermission(); }
      catch { permission='denied'; }
      state.notificationsEnabled=permission==='granted'; saveNotificationPreference(state.notificationsEnabled); syncNotificationToggle();
      showToast(state.notificationsEnabled?'桌面通知已开启':'未获得通知权限',state.notificationsEnabled?'success':'warning');
    }
    function messagePreview(message) {
      if(message.file) return '[文件] '+message.file.name;
      return String(message.text||'').replace(/\s+/g,' ').slice(0,90)||'发来一条新消息';
    }
    function messageMentionsMe(message) { return message.senderId!==identity.id&&!!identity.name&&String(message.text||'').includes('@'+identity.name); }
    function notifyDesktop(title,body,tag) {
      if(!state.notificationsEnabled||!notificationSupported()||Notification.permission!=='granted'||(!document.hidden&&document.hasFocus())) return;
      try { const notice=new Notification(title,{body,tag}); notice.onclick=()=>{ window.focus(); notice.close(); }; } catch {}
    }
    function handleIncomingMessages(items,suppress) {
      if(suppress||!items.length) return;
      const incoming=items.filter(message=>message.senderId!==identity.id&&!message.recalled);
      if(!incoming.length) return;
      addPageUnread(incoming.length);
      incoming.forEach(message=>{
        const mentioned=messageMentionsMe(message);
        const context=message.mode==='private'?'私聊消息':mentioned?'有人提到了你':'频道新消息';
        notifyDesktop(context+' · '+message.name,messagePreview(message),'lan-chat-message-'+message.id);
        if(mentioned&&!document.hidden&&document.hasFocus()) showToast(message.name+' 在消息中提到了你','info');
      });
    }
    function handlePrivateUnreadIncreases(previous,next,suppress) {
      if(suppress) return;
      Object.entries(next).forEach(([peerId,count])=>{
        const delta=Number(count||0)-Number(previous[peerId]||0);
        if(delta<=0) return;
        const user=state.users.find(item=>item.id===peerId); const name=user?.name||'一位用户';
        addPageUnread(delta); notifyDesktop(name+' 发来私聊消息',delta+' 条未读私聊消息','lan-chat-private-'+peerId);
      });
    }
    function handleChannelUnreadIncreases(previous,next,suppress) {
      if(suppress) return;
      Object.entries(next).forEach(([channelId,count])=>{
        const delta=Number(count||0)-Number(previous[channelId]||0);
        if(delta<=0) return;
        const channel=state.channels.find(item=>item.id===channelId); const name=channel?.name||'公共频道';
        addPageUnread(delta); notifyDesktop(name+' 有新消息',delta+' 条未读频道消息','lan-chat-channel-'+channelId);
      });
    }
    try { state.notificationsEnabled=notificationSupported()&&Notification.permission==='granted'&&localStorage.getItem(NOTIFICATION_KEY)==='1'; } catch {}
    syncNotificationToggle();
    $('notification-toggle').addEventListener('click',toggleDesktopNotifications);
    document.addEventListener('visibilitychange',()=>{ if(!document.hidden) clearPageUnread(); });
    window.addEventListener('focus',clearPageUnread);
    const identityCard=document.querySelector('.identity');
    function placeIdentityForViewport(usersOpen=document.body.classList.contains('mobile-users-open')) {
      const chatTop=document.querySelector('.chat-top');
      const profilePanel=document.querySelector('.profile-panel');
      const channelSelect=$('mobile-channel-select');
      const userDirectory=profilePanel?.querySelector('.user-directory');
      if(!identityCard||!chatTop||!profilePanel||!channelSelect||!userDirectory) return false;
      const target=window.innerWidth<=700&&!usersOpen?chatTop:profilePanel;
      const before=target===chatTop?channelSelect:userDirectory;
      if(identityCard.parentElement!==target||identityCard.nextElementSibling!==before) target.insertBefore(identityCard,before);
      return true;
    }
    function setMobileUsersOpen(open) {
      document.body.classList.toggle('mobile-users-open',!!open);
      $('mobile-users-toggle').setAttribute('aria-expanded',open?'true':'false');
      placeIdentityForViewport(!!open);
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
    $('my-name').value=identity.name;
    setAvatarInitial($('my-avatar'),identity.name);
    if(!placeIdentityForViewport(false)&&document.readyState==='loading') document.addEventListener('DOMContentLoaded',()=>placeIdentityForViewport(false),{once:true});
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
        if(state.previewingMessageId===messageId) closeImagePreview();
        const index=state.messages.findIndex(message=>message.id===messageId);
        if(index!==-1) { releaseDirectFile(state.messages[index]); state.messages[index]=data.message; }
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
    function privateMessageStatus(message) {
      if(message.senderId!==identity.id||message.mode!=='private'||message.recalled) return '';
      if(message.file?.receivedAt) return '对方已接收';
      if(message.readAt) return '已读';
      if(message.deliveredAt) return '已送达';
      if(state.peer?.id===message.recipientId&&state.peer.online===false) return '对方离线';
      return '已发送';
    }
    function releaseDirectFile(message) {
      const transferId=message?.file?.direct&&(message.file.transferId||message.file.id); const directFile=transferId&&directFiles.get(transferId);
      if(directFile) { URL.revokeObjectURL(directFile.url); directFiles.delete(transferId); }
    }
    function replyText(message) { return message.file?'[文件] '+message.file.name:String(message.text||'').replace(/\s+/g,' ').slice(0,120); }
    function renderReplyPreview() {
      const reply=state.replyingTo; const root=$('reply-preview'); root.hidden=!reply;
      if(!reply) return;
      $('reply-preview-name').textContent='回复 '+reply.name;
      $('reply-preview-text').textContent=reply.preview;
    }
    function clearReply() { state.replyingTo=null; renderReplyPreview(); }
    function setReplyTarget(message) {
      if(!message||message.recalled) return;
      state.replyingTo={id:message.id,name:message.name||'匿名用户',preview:replyText(message),at:message.at};
      renderReplyPreview(); $('message').focus();
    }
    function insertMention(name) {
      const input=$('message'); const mention='@'+String(name||'').trim()+' ';
      if(mention==='@ ') return;
      const start=input.selectionStart??input.value.length; const end=input.selectionEnd??start;
      const prefix=input.value.slice(0,start); const spacer=prefix&&!/\s$/.test(prefix)?' ':'';
      const next=(prefix+spacer+mention+input.value.slice(end)).slice(0,Number(input.maxLength)||500);
      input.value=next; input.focus(); input.selectionStart=input.selectionEnd=Math.min(next.length,start+spacer.length+mention.length);
      input.dispatchEvent(new Event('input',{bubbles:true}));
    }
    function jumpToMessage(messageId) {
      const index=state.messages.findIndex(message=>message.id===messageId);
      if(index===-1) { showToast('原消息已过期或未加载','warning'); return; }
      syncPrefix(); const root=$('messages'); state.scrollLocked=false;
      root.scrollTop=Math.max(0,vlist.prefixSum[index]-Math.max(20,root.clientHeight/3)); render({force:true});
      requestAnimationFrame(()=>requestAnimationFrame(()=>{
        const row=vlist.nodeMap.get(messageId);
        if(!row) { showToast('暂时无法定位原消息','warning'); return; }
        row.scrollIntoView({block:'center',behavior:prefersLessMotion?'auto':'smooth'}); row.classList.add('jump-highlight');
        setTimeout(()=>row.classList.remove('jump-highlight'),1400);
      }));
    }
    function clientPreviewImageType(file) {
      const declared=String(file?.type||'').toLowerCase().split(';')[0].trim();
      if(['image/jpeg','image/png','image/gif','image/webp','image/avif','image/bmp'].includes(declared)) return declared;
      const match=String(file?.name||'').toLowerCase().match(/\.(jpe?g|png|gif|webp|avif|bmp)$/);
      return match?match[1]:'';
    }
    function closeImagePreview() {
      state.previewingMessageId=''; $('image-preview-modal').hidden=true; $('image-preview-image').removeAttribute('src'); $('image-preview-caption').textContent='';
    }
    function openImagePreview(src,name,messageId) {
      state.previewingMessageId=messageId; $('image-preview-image').src=src; $('image-preview-image').alt=name;
      $('image-preview-caption').textContent=name; $('image-preview-modal').hidden=false; $('image-preview-close').focus();
    }
    function createRow(m, isNew) {
      const self = m.senderId === identity.id;
      const row = document.createElement('div');
      row.className = 'message' + (self ? ' self' : '') + (isNew ? ' is-new' : '') + (m.recalled ? ' recalled' : '') + (messageMentionsMe(m)?' mentioned':'');
      row.dataset.id = m.id;
      row.dataset.sender = m.senderId || '';
      row.dataset.at = String(m.at);
      row.dataset.expiresAt = String(m.at + state.retentionMs);
      row.innerHTML = '<div class="message-avatar"></div><div class="message-meta"><div class="message-name"></div><span class="message-status"></span></div><div class="message-bubble"><button class="message-reply" type="button" hidden><b></b><span></span></button><span class="message-text"></span><div class="message-file" hidden><button class="file-image-button" type="button" hidden><img class="file-image" loading="lazy" decoding="async"></button><div class="file-name"></div><div class="file-meta"></div><a class="file-download"></a></div><div class="message-footer"><button class="message-action reply-action" type="button" title="回复消息" aria-label="回复消息"></button><button class="message-action copy-action" type="button" title="复制消息" aria-label="复制消息"></button><time class="message-time"></time><button class="message-action recall-action" type="button" title="撤回消息" aria-label="撤回消息"></button></div></div>';
      setAvatarInitial(row.querySelector('.message-avatar'),m.name);
      const messageName=row.querySelector('.message-name'); messageName.textContent=m.name;
      if(!self&&!m.recalled) { messageName.classList.add('mention-target'); messageName.title='点击在输入框中 @'+m.name; messageName.addEventListener('click',()=>insertMention(m.name)); }
      const statusText=privateMessageStatus(m); row.querySelector('.message-status').textContent=statusText; row.querySelector('.message-status').hidden=!statusText;
      const replyCard=row.querySelector('.message-reply');
      if(m.reply) { replyCard.hidden=false; replyCard.querySelector('b').textContent=m.reply.name; replyCard.querySelector('span').textContent=m.reply.preview; replyCard.title='跳转到被引用的消息'; replyCard.setAttribute('aria-label','跳转到 '+m.reply.name+' 的原消息'); replyCard.addEventListener('click',()=>jumpToMessage(m.reply.id)); }
      const textNode=row.querySelector('.message-text');
      textNode.textContent = m.recalled ? '该消息已撤回' : m.text;
      const fileCard=row.querySelector('.message-file');
      if(m.file&&!m.recalled) {
        textNode.hidden=true; fileCard.hidden=false;
        row.querySelector('.file-name').textContent=m.file.name;
        row.querySelector('.file-meta').textContent=formatFileSize(m.file.size)+' · '+formatDuration(state.retentionMs)+'后销毁';
        const download=row.querySelector('.file-download');
        let previewUrl='';
        if(m.file.direct) {
          const directFile=directFiles.get(m.file.transferId||m.file.id);
          if(directFile) { previewUrl=directFile.url; download.href=directFile.url; download.download=m.file.name; download.title='下载 '+m.file.name; download.append(iconNode('download'),document.createTextNode('下载')); }
          else { download.removeAttribute('href'); download.setAttribute('aria-disabled','true'); download.title='点对点传输已完成'; download.append(iconNode('check'),document.createTextNode(self?'已直传':'已接收')); }
        } else {
          const fileUrl=apiBase+'/api/file/'+encodeURIComponent(m.file.id)+'?client='+encodeURIComponent(identity.id)+'&token='+encodeURIComponent(m.file.token);
          download.href=fileUrl; previewUrl=fileUrl+'&preview=1';
          download.download=m.file.name; download.title='下载 '+m.file.name; download.append(iconNode('download'),document.createTextNode('下载'));
        }
        if(previewUrl&&clientPreviewImageType(m.file)&&m.file.size<=state.maxImagePreviewBytes) {
          fileCard.classList.add('has-image'); const previewButton=row.querySelector('.file-image-button'); const image=previewButton.querySelector('img');
          previewButton.hidden=false; previewButton.title='点击放大预览 '+m.file.name; previewButton.setAttribute('aria-label',previewButton.title); image.alt=m.file.name; image.src=previewUrl;
          previewButton.addEventListener('click',()=>openImagePreview(previewUrl,m.file.name,m.id));
          image.addEventListener('load',()=>requestAnimationFrame(()=>{ const height=row.getBoundingClientRect().height; if(height) { vlist.heights.set(m.id,height); syncPrefix(); $('messages-spacer').style.height=(vlist.prefixSum[vlist.prefixSum.length-1]+BLOCK_PADDING)+'px'; } }),{once:true});
          image.addEventListener('error',()=>{ previewButton.hidden=true; fileCard.classList.remove('has-image'); },{once:true});
        }
      }
      const replyButton=row.querySelector('.reply-action');
      const copyButton=row.querySelector('.copy-action');
      const recallButton=row.querySelector('.recall-action');
      setIcon(replyButton,'reply'); setIcon(copyButton,'copy'); setIcon(recallButton,'rotate-ccw');
      replyButton.hidden=!!m.recalled;
      copyButton.hidden=!!m.recalled||!m.text;
      recallButton.hidden=!self||!!m.recalled||Date.now()-m.at>state.recallWindowMs;
      replyButton.addEventListener('click',()=>setReplyTarget(m));
      if(m.text) copyButton.addEventListener('click',()=>copyMessageText(m.text,copyButton));
      recallButton.addEventListener('click',()=>recallMessage(m.id,recallButton));
      updateMessageCountdown(row, m.at);
      return row;
    }
    function formatFileSize(bytes) {
      if(bytes<1024) return bytes+' B';
      if(bytes<1024*1024) return (bytes/1024).toFixed(bytes<10240?1:0)+' KB';
      if(bytes>=1024*1024*1024) {
        const gigabytes=bytes/(1024*1024*1024);
        return gigabytes.toFixed(Number.isInteger(gigabytes)?0:1)+' GB';
      }
      const megabytes=bytes/(1024*1024);
      return megabytes.toFixed(Number.isInteger(megabytes)?0:1)+' MB';
    }
    function formatDuration(ms) { return Math.round(ms/60000)+' 分钟'; }
    function syncLimitUI() {
      setText($('retention-rule'),'消息与文件默认保留 10 分钟，管理员可实时调整；当前为 '+formatDuration(state.retentionMs));
      setText($('file-limit-rule'),'单文件上限最高 20 GB，当前为 '+formatFileSize(state.maxFileBytes));
    }
    function formatRemaining(ms) {
      const seconds = Math.max(0, Math.ceil(ms / 1000));
      return String(Math.floor(seconds / 60)).padStart(2, '0') + ':' + String(seconds % 60).padStart(2, '0');
    }
    function updateMessageCountdown(row, at) {
      row.querySelector('.message-time').textContent = formatRemaining(at + state.retentionMs - Date.now());
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
      $('send').disabled=state.full||cooling||peerOffline;
      $('file-toggle').hidden=false;
      $('file-toggle').disabled=state.full||state.uploading||cooling||peerOffline;
      const fileRule='最大 '+formatFileSize(state.maxFileBytes)+'，'+formatDuration(state.retentionMs)+'后销毁';
      $('file-toggle').title=peerOffline?'对方已离线':state.uploading?'正在上传文件':state.mode==='private'?'发送私聊文件（'+fileRule+'）':'发送频道文件（'+fileRule+'）';
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
        state.channels.map(channel=>[channel.id,channel.name,state.onlineByChannel[channel.id]||0,state.channelUnread[channel.id]||0])
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
          button.innerHTML='<span class="channel-name"></span><span class="channel-meta"><span class="channel-count"></span></span>';
          button.querySelector('.channel-name').textContent=channel.name;
          button.querySelector('.channel-count').textContent=state.onlineByChannel[channel.id]||0;
          const unread=state.channelUnread[channel.id]||0;
          if(unread) { const badge=document.createElement('span'); badge.className='channel-unread'; badge.textContent=unread>99?'99+':String(unread); button.querySelector('.channel-meta').append(badge); }
          button.addEventListener('click',()=>switchChannel(channel.id));
          fragment.append(button);
          const option=document.createElement('option');
          option.value=channel.id;
          option.textContent=channel.name+'（'+(state.onlineByChannel[channel.id]||0)+'）'+(unread?' · 未读 '+unread:'');
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
        $('message').placeholder=state.peer.online===false?'对方已离线':'私下说点什么……';
        if(state.peer.online===false) $('send').disabled=true;
        else if(!state.full&&Date.now()>=state.sendCooldownUntil) $('send').disabled=false;
      } else if(current) {
        const idx = state.channels.indexOf(current)+1;
        const channelOnline=state.onlineByChannel[state.channel]||0;
        setText($('kicker'),'LOCAL / ' + String(idx).padStart(3,'0'));
        setText($('channel-title'),current.name+'（'+channelOnline+'）');
        $('message').placeholder='说点什么……';
        if(!state.full&&Date.now()>=state.sendCooldownUntil) $('send').disabled=false;
      }
      setText($('total-online'),state.online);
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
      const ban=$('user-ban-button');
      modal.hidden=false; detail.textContent='正在读取'; ban.hidden=true; ban.disabled=false; ban.onclick=null;
      const response=await fetch(apiBase+'/api/admin/user?client='+encodeURIComponent(clientId),{headers:{'X-Admin-Token':state.adminToken}});
      const data=await response.json().catch(()=>({}));
      if(!response.ok) { detail.textContent=data.error==='offline'?'该用户已经离线':'读取失败'; return; }
      const channel=state.channels.find(item=>item.id===data.channel);
      detail.replaceChildren();
      [['用户名',data.name],['IP 地址',data.ip],['所在频道',channel?channel.name:data.channel],['最后在线',new Date(data.lastSeen).toLocaleString()]].forEach(([label,value])=>{
        const line=document.createElement('div'); const strong=document.createElement('b'); strong.textContent=label+'：'; line.append(strong,document.createTextNode(String(value))); detail.append(line);
      });
      ban.textContent=data.banned?'解除 IP 封禁':'封禁此 IP'; ban.hidden=false;
      ban.onclick=async()=>{ ban.disabled=true; const ok=await setIpBan(data.ip,!data.banned); if(ok) modal.hidden=true; else ban.disabled=false; };
    }
    function switchChannel(channel) {
      if((state.mode==='channel'&&channel===state.channel)||!state.channels.some(item=>item.id===channel)) return;
      setMobileUsersOpen(false);
      state.mode='channel';
      state.peer=null;
      state.channel=channel;
      state.channelUnread[channel]=0;
      state.cursor=0;
      state.messages=[];
      state.suppressIncomingOnce=true;
      state.scrollLocked=true;
      closeImagePreview();
      clearReply();
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
      state.suppressIncomingOnce=true;
      state.scrollLocked=true;
      closeImagePreview();
      clearReply();
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
    function renderAdminSettings() {
      $('admin-retention').value=String(Math.round(state.retentionMs/60000));
      $('admin-file-limit').value=String(Math.round(state.maxFileBytes/(1024*1024)));
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
    async function saveAdminSettings() {
      const button=$('admin-settings-save');
      const retentionInput=$('admin-retention');
      const fileLimitInput=$('admin-file-limit');
      const digitsOnly=/^[0-9]+$/;
      const retentionMinutes=Number(retentionInput.value);
      const fileMegabytes=Number(fileLimitInput.value);
      if(!digitsOnly.test(retentionInput.value)||!Number.isInteger(retentionMinutes)||retentionMinutes<1||retentionMinutes>1440) {
        retentionInput.focus();
        showToast('销毁时间请输入 1–1440 之间的整数分钟','warning');
        return;
      }
      if(!digitsOnly.test(fileLimitInput.value)||!Number.isInteger(fileMegabytes)||fileMegabytes<1||fileMegabytes>20480) {
        fileLimitInput.focus();
        showToast('文件上限请输入 1–20480 之间的整数 MB','warning');
        return;
      }
      button.disabled=true;
      try {
        const response=await fetch(apiBase+'/api/admin/settings',{method:'POST',headers:{'Content-Type':'application/json','X-Admin-Token':state.adminToken},body:JSON.stringify({retentionMinutes:retentionInput.value,fileMegabytes:fileLimitInput.value})});
        const data=await response.json().catch(()=>({}));
        if(!response.ok) throw Error(data.error||'settings failed');
        if(typeof data.retentionMs==='number') state.retentionMs=data.retentionMs;
        if(typeof data.maxFileBytes==='number') state.maxFileBytes=data.maxFileBytes;
        syncLimitUI();
        updateComposerControls();
        tick();
        button.textContent='已应用';
        showToast('内容限制已实时更新','success');
      } catch {
        button.textContent='应用失败';
        showToast('内容限制更新失败，请重试','error');
      } finally {
        button.disabled=false;
        setTimeout(()=>button.textContent='应用设置',1000);
      }
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
      $('admin-modal').querySelector('.modal').classList.toggle('tools-open',!!state.adminToken);
      $('admin-password').value='';
      $('admin-password').placeholder='输入管理员密码';
      if(state.adminToken) {
        $('admin-login').hidden=true;
        $('admin-tools').hidden=false;
        $('admin-modal-title').textContent='管理员工具';
        renderAdminChannels();
        renderAdminSettings();
        loadBans();
      } else {
        $('admin-login').hidden=false;
        $('admin-tools').hidden=true;
        $('admin-modal-title').textContent='验证管理员';
        requestAnimationFrame(()=>$('admin-password').focus());
      }
    }
    function tick() {
      const now=Date.now();
      if(state.replyingTo&&now-state.replyingTo.at>=state.retentionMs) clearReply();
      const active=state.messages.filter(m=>now-m.at<state.retentionMs);
      if(active.length!==state.messages.length) {
        if(state.previewingMessageId&&!active.some(message=>message.id===state.previewingMessageId)) closeImagePreview();
        state.messages.filter(m=>now-m.at>=state.retentionMs).forEach(releaseDirectFile);
        state.messages=active;
        render({force:true});
      }
      if(!vlist.nodeMap.size) return;
      const messageById=new Map(state.messages.map(message=>[message.id,message]));
      vlist.nodeMap.forEach((row, id) => {
        const message=messageById.get(id);
        if (message) {
          updateMessageCountdown(row, message.at);
          const fileMeta=row.querySelector('.file-meta');
          if(fileMeta&&message.file&&!message.recalled) {
            const nextMeta=formatFileSize(message.file.size)+' · '+formatDuration(state.retentionMs)+'后销毁';
            if(fileMeta.textContent!==nextMeta) fileMeta.textContent=nextMeta;
          }
          const messageStatus=row.querySelector('.message-status');
          if(messageStatus) { const nextStatus=privateMessageStatus(message); messageStatus.textContent=nextStatus; messageStatus.hidden=!nextStatus; }
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
        const r=await fetch(apiBase+'/api/poll?since='+requestedCursor+'&client='+encodeURIComponent(identity.id)+'&channel='+encodeURIComponent(requestedChannel)+'&name='+encodeURIComponent(identity.name)+peerQuery);
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
        handleRtcSignals(data.rtcSignals||[]);
        if(requestedChannel!==state.channel||requestedMode!==state.mode||requestedPeer!==(state.peer?.id||'')) return;
        state.full=false;
        state.blockedReason='';
        updateBlocker(false);
        $('send').disabled=Date.now()<state.sendCooldownUntil;
        if(!state.nameEdited && data.assignedName && data.assignedName!==identity.name) {
          identity.name=data.assignedName;
          $('my-name').value=data.assignedName;
          setAvatarInitial($('my-avatar'),identity.name);
          saveLocalName(identity.name);
        }
        if(typeof data.renderBatch === 'number') state.renderBatch = data.renderBatch;
        if(typeof data.pollInterval === 'number') state.pollInterval = data.pollInterval;
        if(typeof data.recallWindowMs === 'number') state.recallWindowMs = data.recallWindowMs;
        if(typeof data.maxFileBytes === 'number') state.maxFileBytes = data.maxFileBytes;
        if(typeof data.maxImagePreviewBytes === 'number') state.maxImagePreviewBytes = data.maxImagePreviewBytes;
        state.limit = data.limit;
        state.cursor=data.cursor;
        state.online=data.online;
        state.channels=data.channels;
        state.onlineByChannel=data.onlineByChannel;
        state.users=data.users||[];
        state.typing=data.typing||[];
        const previousPrivateUnread=state.previousPrivateUnread;
        state.privateUnread=data.privateUnread||{};
        state.previousPrivateUnread={...state.privateUnread};
        const previousChannelUnread=state.previousChannelUnread;
        state.channelUnread=data.channelUnread||{};
        state.previousChannelUnread={...state.channelUnread};
        state.privateActivity=data.privateActivity||{};
        if(state.mode==='private'&&data.peer) state.peer=data.peer;
        if(typeof data.retentionMs==='number') state.retentionMs=data.retentionMs;
        const typingText=state.typing.length?(state.typing.length===1?state.typing[0]+' 正在输入':state.typing.length+' 人正在输入'):'';
        $('typing-indicator').textContent=typingText; $('typing-indicator').hidden=!typingText;
        syncLimitUI();
        const root=$('messages');
        const wasLocked = state.scrollLocked;
        const atBottom = wasLocked || Math.abs((root.scrollTop + root.clientHeight) - root.scrollHeight) < 6;
        const indexById = new Map(state.messages.map((message,index)=>[message.id,index]));
        const newIds = [];
        const newMessages = [];
        const merged = state.messages.slice();
        let hasUpdates=false;
        data.messages.forEach(m=>{
          if(Date.now()-m.at>=data.retentionMs) return;
          const existingIndex=indexById.get(m.id);
          if(existingIndex===undefined) { indexById.set(m.id,merged.length); merged.push(m); newIds.push(m.id); newMessages.push(m); return; }
          if((m.cursor||0)>(merged[existingIndex].cursor||0)) {
            if(m.recalled) { if(state.previewingMessageId===m.id) closeImagePreview(); releaseDirectFile(merged[existingIndex]); }
            merged[existingIndex]=m; hasUpdates=true;
            const oldNode=vlist.nodeMap.get(m.id); if(oldNode) oldNode.remove(); vlist.nodeMap.delete(m.id); vlist.heights.delete(m.id);
          }
        });
        const wasTrimmed=merged.length>state.renderBatch*2;
        state.messages = wasTrimmed ? merged.slice(-state.renderBatch * 2) : merged;
        if(state.previewingMessageId&&!state.messages.some(message=>message.id===state.previewingMessageId)) closeImagePreview();
        const suppressIncoming=state.suppressIncomingOnce;
        state.suppressIncomingOnce=false;
        handleIncomingMessages(newMessages,suppressIncoming);
        handlePrivateUnreadIncreases(previousPrivateUnread,state.privateUnread,suppressIncoming);
        handleChannelUnreadIncreases(previousChannelUnread,state.channelUnread,suppressIncoming);
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
    $('my-name').addEventListener('input',e=>{
      state.nameEdited=true;
      identity.name=Array.from(e.target.value).slice(0,5).join('');
      setAvatarInitial($('my-avatar'),identity.name||'匿名访客');
      saveLocalName(identity.name);
    });
    $('mobile-users-toggle').addEventListener('click',()=>setMobileUsersOpen(true));
    $('mobile-users-close').addEventListener('click',()=>setMobileUsersOpen(false));
    document.addEventListener('keydown',e=>{ if(e.key==='Escape'&&document.body.classList.contains('mobile-users-open')) setMobileUsersOpen(false); });
    window.addEventListener('resize',()=>{ if(window.innerWidth>700) setMobileUsersOpen(false); else placeIdentityForViewport(); });
    $('emoji-toggle').addEventListener('click',()=>{ const panel=$('emoji-panel'); panel.hidden=!panel.hidden; $('emoji-toggle').setAttribute('aria-expanded',panel.hidden?'false':'true'); });
    document.addEventListener('click',event=>{ if(!event.target.closest('.emoji-wrap')) { $('emoji-panel').hidden=true; $('emoji-toggle').setAttribute('aria-expanded','false'); } });
    document.addEventListener('keydown',event=>{ if(event.key==='Escape') { $('emoji-panel').hidden=true; $('emoji-toggle').setAttribute('aria-expanded','false'); } });
    const reactionRule=document.querySelector('.rules-list li:nth-child(3)');
    if(reactionRule) reactionRule.textContent='点击昵称可快速 @用户，消息下方支持回复';
    function postRtcSignal(target,signal) { return fetch(apiBase+'/api/rtc/signal',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({id:identity.id,target,signal})}).catch(()=>{}); }
    function setupRtcDataChannel(record,channel) {
      record.channel=channel; channel.binaryType='arraybuffer'; channel.bufferedAmountLowThreshold=256*1024;
      channel.addEventListener('message',async event=>{
        if(typeof event.data==='string') {
          let packet; try { packet=JSON.parse(event.data); } catch { return; }
          if(packet.kind==='file-meta') { record.incoming={meta:packet,chunks:[],received:0}; return; }
          if(packet.kind==='file-ack') { const waiter=rtcAckWaiters.get(packet.transferId); if(waiter) { rtcAckWaiters.delete(packet.transferId); packet.ok?waiter.resolve():waiter.reject(Error('rtc hash mismatch')); } return; }
          if(packet.kind==='file-cancel'&&record.incoming?.meta.transferId===packet.transferId) { record.incoming=null; return; }
          if(packet.kind==='file-done'&&record.incoming?.meta.transferId===packet.transferId) {
            const incoming=record.incoming; record.incoming=null;
            try {
              const blob=new Blob(incoming.chunks,{type:incoming.meta.type||'application/octet-stream'}); if(blob.size!==incoming.meta.size) throw Error('rtc size mismatch');
              const digest=await sha256Hex(await blob.arrayBuffer()); if(digest!==incoming.meta.sha256) throw Error('rtc hash mismatch');
              const previous=directFiles.get(packet.transferId); if(previous) URL.revokeObjectURL(previous.url);
              directFiles.set(packet.transferId,{url:URL.createObjectURL(blob),name:incoming.meta.name,size:blob.size});
              channel.send(JSON.stringify({kind:'file-ack',transferId:packet.transferId,ok:true})); showToast('点对点文件已接收，可在消息中下载','success');
            } catch { channel.send(JSON.stringify({kind:'file-ack',transferId:packet.transferId,ok:false})); showToast('点对点文件校验失败','error'); }
          }
          return;
        }
        if(record.incoming&&event.data instanceof ArrayBuffer) { record.incoming.chunks.push(event.data); record.incoming.received+=event.data.byteLength; }
      });
    }
    function createRtcPeer(peerId,initiator=false) {
      const old=rtcPeers.get(peerId); if(old) { try { old.pc.close(); } catch {} }
      const pc=new RTCPeerConnection({iceServers:[]}); const record={pc,channel:null,incoming:null}; rtcPeers.set(peerId,record);
      pc.addEventListener('icecandidate',event=>{ if(event.candidate) postRtcSignal(peerId,{kind:'candidate',candidate:event.candidate.toJSON?event.candidate.toJSON():event.candidate}); });
      pc.addEventListener('datachannel',event=>setupRtcDataChannel(record,event.channel));
      pc.addEventListener('connectionstatechange',()=>{ if(['failed','closed','disconnected'].includes(pc.connectionState)&&rtcPeers.get(peerId)===record) rtcPeers.delete(peerId); });
      if(initiator) setupRtcDataChannel(record,pc.createDataChannel('lan-chat-file',{ordered:true}));
      return record;
    }
    async function handleRtcSignals(signals) {
      if(!('RTCPeerConnection' in window)) return;
      for(const item of signals||[]) {
        const peerId=String(item.from||''); const signal=item.signal||{};
        try {
          if(signal.kind==='offer') { const record=createRtcPeer(peerId,false); await record.pc.setRemoteDescription(signal.description); const answer=await record.pc.createAnswer(); await record.pc.setLocalDescription(answer); await postRtcSignal(peerId,{kind:'answer',description:record.pc.localDescription}); }
          else if(signal.kind==='answer') { const record=rtcPeers.get(peerId); if(record) await record.pc.setRemoteDescription(signal.description); }
          else if(signal.kind==='candidate') { const record=rtcPeers.get(peerId); if(record) await record.pc.addIceCandidate(signal.candidate); }
        } catch { const record=rtcPeers.get(peerId); if(record) { try { record.pc.close(); } catch {} rtcPeers.delete(peerId); } }
      }
    }
    async function ensureRtcChannel(peerId) {
      let record=rtcPeers.get(peerId);
      if(record?.channel?.readyState==='open') return record.channel;
      if(!record) {
        record=createRtcPeer(peerId,true); const offer=await record.pc.createOffer(); await record.pc.setLocalDescription(offer); await postRtcSignal(peerId,{kind:'offer',description:record.pc.localDescription});
      }
      const channel=record.channel;
      if(!channel) throw Error('rtc channel unavailable');
      if(channel.readyState==='open') return channel;
      await new Promise((resolve,reject)=>{ const timer=setTimeout(()=>reject(Error('rtc timeout')),8000); channel.addEventListener('open',()=>{ clearTimeout(timer); resolve(); },{once:true}); channel.addEventListener('close',()=>{ clearTimeout(timer); reject(Error('rtc closed')); },{once:true}); });
      return channel;
    }
    async function waitRtcBuffer(channel,task) {
      const started=performance.now();
      while(channel.bufferedAmount>=512*1024) {
        if(task.cancelled) throw Error('cancelled');
        await waitWhileUploadPaused(task);
        if(performance.now()-started>8000) throw Error('rtc buffer timeout');
        await wait(40);
      }
    }
    const sha256Constants=new Uint32Array([0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2]);
    function rotateRight(value,bits) { return (value>>>bits)|(value<<(32-bits)); }
    async function sha256Hex(buffer) {
      if(crypto.subtle) {
        const digest=await crypto.subtle.digest('SHA-256',buffer);
        return Array.from(new Uint8Array(digest),byte=>byte.toString(16).padStart(2,'0')).join('');
      }
      const source=new Uint8Array(buffer); const paddedLength=Math.ceil((source.length+9)/64)*64; const padded=new Uint8Array(paddedLength); padded.set(source); padded[source.length]=0x80;
      const view=new DataView(padded.buffer); const bitLength=source.length*8; view.setUint32(paddedLength-8,Math.floor(bitLength/0x100000000)); view.setUint32(paddedLength-4,bitLength>>>0);
      const hash=new Uint32Array([0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19]); const words=new Uint32Array(64);
      for(let offset=0;offset<paddedLength;offset+=64) {
        if(offset&&offset%(64*128)===0) await new Promise(resolve=>setTimeout(resolve,0));
        for(let i=0;i<16;i++) words[i]=view.getUint32(offset+i*4);
        for(let i=16;i<64;i++) { const s0=rotateRight(words[i-15],7)^rotateRight(words[i-15],18)^(words[i-15]>>>3); const s1=rotateRight(words[i-2],17)^rotateRight(words[i-2],19)^(words[i-2]>>>10); words[i]=(words[i-16]+s0+words[i-7]+s1)>>>0; }
        let a=hash[0],b=hash[1],c=hash[2],d=hash[3],e=hash[4],f=hash[5],g=hash[6],h=hash[7];
        for(let i=0;i<64;i++) { const sum1=rotateRight(e,6)^rotateRight(e,11)^rotateRight(e,25); const choose=(e&f)^(~e&g); const temp1=(h+sum1+choose+sha256Constants[i]+words[i])>>>0; const sum0=rotateRight(a,2)^rotateRight(a,13)^rotateRight(a,22); const majority=(a&b)^(a&c)^(b&c); const temp2=(sum0+majority)>>>0; h=g;g=f;f=e;e=(d+temp1)>>>0;d=c;c=b;b=a;a=(temp1+temp2)>>>0; }
        hash[0]=(hash[0]+a)>>>0;hash[1]=(hash[1]+b)>>>0;hash[2]=(hash[2]+c)>>>0;hash[3]=(hash[3]+d)>>>0;hash[4]=(hash[4]+e)>>>0;hash[5]=(hash[5]+f)>>>0;hash[6]=(hash[6]+g)>>>0;hash[7]=(hash[7]+h)>>>0;
      }
      return Array.from(hash,value=>value.toString(16).padStart(8,'0')).join('');
    }
    async function tryDirectFile(file,peerId,channelId,replyTo='') {
      if(!('RTCPeerConnection' in window)||file.size>RTC_DIRECT_MAX_BYTES) return false;
      const task={file,requestedMode:'private',peerId,channelId,replyTo,uploadId:'',transferId:'',paused:false,cancelled:false,pauseAbort:false,resume:null,controller:null,startedAt:performance.now(),startedReceived:0,received:0,pausedMs:0,direct:true};
      state.uploadTask=task; state.uploading=true; resetTransferControls(); updateComposerControls(); renderTransferTask(task,0,'正在建立点对点连接');
      try {
        const channel=await ensureRtcChannel(peerId); if(task.cancelled) throw Error('cancelled');
        renderTransferTask(task,0,'正在计算文件校验值'); const buffer=await file.arrayBuffer(); if(task.cancelled) throw Error('cancelled');
        const sha256=await sha256Hex(buffer); await waitWhileUploadPaused(task); if(task.cancelled) throw Error('cancelled'); const transferId=crypto.randomUUID?crypto.randomUUID():Math.random().toString(36).slice(2).padEnd(36,'0').slice(0,36); task.transferId=transferId;
        channel.send(JSON.stringify({kind:'file-meta',transferId,name:file.name,size:file.size,type:file.type||'application/octet-stream',sha256}));
        const chunkSize=64*1024;
        for(let offset=0;offset<buffer.byteLength;offset+=chunkSize) {
          await waitWhileUploadPaused(task); if(task.cancelled) throw Error('cancelled'); await waitRtcBuffer(channel,task);
          const end=Math.min(offset+chunkSize,buffer.byteLength); channel.send(buffer.slice(offset,end)); renderTransferTask(task,end,'点对点直传 '+(end/file.size*100).toFixed(1)+'% · '+formatFileSize(end)+' / '+formatFileSize(file.size));
        }
        if(task.cancelled) throw Error('cancelled');
        const acknowledgement=new Promise((resolve,reject)=>{ const timer=setTimeout(()=>{ rtcAckWaiters.delete(transferId); reject(Error('rtc acknowledgement timeout')); },12000); rtcAckWaiters.set(transferId,{resolve:()=>{ clearTimeout(timer); resolve(); },reject:error=>{ clearTimeout(timer); reject(error); }}); });
        channel.send(JSON.stringify({kind:'file-done',transferId})); renderTransferTask(task,file.size,'等待对方校验文件'); await acknowledgement;
        let response; let data={};
        for(let attempt=0;attempt<3;attempt++) {
          response=await fetch(apiBase+'/api/direct-file',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({id:identity.id,peer:peerId,transferId,name:encodeURIComponent(file.name),size:file.size,type:file.type||'application/octet-stream',sha256,replyTo})});
          data=await response.json().catch(()=>({})); if(response.ok) break; await wait(300*(attempt+1));
        }
        if(!response?.ok) throw Error(data.error||'direct metadata failed');
        const previousDirectFile=directFiles.get(transferId); if(previousDirectFile) URL.revokeObjectURL(previousDirectFile.url);
        directFiles.set(transferId,{url:URL.createObjectURL(file),name:file.name,size:file.size});
        if(state.mode==='private'&&state.peer?.id===peerId&&!state.messages.some(message=>message.id===data.message?.id)) { state.messages.push(data.message); state.scrollLocked=true; render({newIds:[data.message.id],scrollToBottom:true}); }
        renderTransferTask(task,file.size,'点对点直传完成 · SHA-256 已校验'); $('connection').textContent='文件已点对点发送'; showToast('点对点文件发送成功','success'); return true;
      } catch(error) {
        if(task.transferId) { const waiter=rtcAckWaiters.get(task.transferId); if(waiter) { rtcAckWaiters.delete(task.transferId); waiter.reject(error); } }
        if(error.message==='cancelled') { renderTransferTask(task,task.received||0,'传输已取消'); showToast('已取消文件传输','info'); return true; }
        if(error.message==='invalid reply') { renderTransferTask(task,task.received||0,'引用消息已失效'); showToast('引用的消息已经失效，请重新发送文件','warning'); return true; }
        renderTransferTask(task,task.received||0,'点对点连接不可用，切换服务器中转'); showToast('点对点连接不可用，已切换服务器分片传输','info'); return false;
      } finally {
        state.uploading=false; if(state.uploadTask===task) state.uploadTask=null; updateComposerControls();
      }
    }
    function wait(ms) { return new Promise(resolve=>setTimeout(resolve,ms)); }
    function formatTransferTime(seconds) {
      if(!Number.isFinite(seconds)||seconds<0) return '计算中';
      if(seconds<60) return Math.max(1,Math.ceil(seconds))+' 秒';
      return Math.ceil(seconds/60)+' 分钟';
    }
    function resetTransferControls() {
      const pause=$('transfer-pause'),cancel=$('transfer-cancel');
      pause.disabled=false; cancel.disabled=false; setIcon(pause,'pause'); pause.title='暂停上传'; pause.setAttribute('aria-label',pause.title);
    }
    function renderTransferTask(task,received,status) {
      task.received=received;
      const root=$('transfer-task'); root.hidden=false; $('transfer-task-name').textContent=task.file.name;
      const percent=Math.min(100,received/task.file.size*100); $('transfer-task-progress').style.width=percent.toFixed(2)+'%';
      const elapsed=Math.max(.1,(performance.now()-task.startedAt-task.pausedMs)/1000); const speed=Math.max(0,(received-task.startedReceived)/elapsed); const eta=speed?(task.file.size-received)/speed:Infinity;
      $('transfer-task-status').textContent=status||percent.toFixed(1)+'% · '+formatFileSize(received)+' / '+formatFileSize(task.file.size)+' · '+formatFileSize(Math.round(speed))+'/s · 剩余 '+formatTransferTime(eta);
    }
    async function waitWhileUploadPaused(task) {
      if(!task.paused) return;
      const pausedAt=performance.now();
      await new Promise(resolve=>{ task.resume=resolve; });
      task.pausedMs+=performance.now()-pausedAt; task.resume=null;
    }
    async function sendUploadChunk(task,buffer,offset,hash) {
      for(let attempt=0;attempt<4;attempt++) {
        await waitWhileUploadPaused(task); if(task.cancelled) throw Error('cancelled');
        task.controller=new AbortController();
        try {
          const response=await fetch(apiBase+'/api/upload/'+encodeURIComponent(task.uploadId)+'/chunk?client='+encodeURIComponent(identity.id),{method:'PUT',headers:{'Content-Type':'application/octet-stream','X-Upload-Offset':String(offset),'X-Chunk-Sha256':hash},body:buffer,signal:task.controller.signal});
          const data=await response.json().catch(()=>({}));
          if(response.status===409&&Number.isInteger(data.received)) return data.received;
          if(!response.ok) throw Error(data.error||'chunk upload failed');
          return data.received;
        } catch(error) {
          if(task.cancelled) throw Error('cancelled');
          if(task.pauseAbort) { task.pauseAbort=false; await waitWhileUploadPaused(task); attempt--; continue; }
          if(attempt===3) throw error;
          renderTransferTask(task,offset,'网络波动，正在重试第 '+(attempt+1)+' 次');
          await wait(500*Math.pow(2,attempt));
        } finally { task.controller=null; }
      }
    }
    async function startChunkUpload(file,requestedMode,peerId,channelId,replyTo='') {
      const task={file,requestedMode,peerId,channelId,replyTo,uploadId:'',paused:false,cancelled:false,pauseAbort:false,resume:null,controller:null,startedAt:performance.now(),startedReceived:0,pausedMs:0};
      state.uploadTask=task; state.uploading=true; resetTransferControls(); updateComposerControls(); renderTransferTask(task,0,'正在建立安全上传会话');
      $('connection').textContent='正在发送 '+file.name;
      let completed=false;
      try {
        const fingerprint=[file.name,file.size,file.lastModified,requestedMode,peerId||channelId,replyTo].join(':');
        const response=await fetch(apiBase+'/api/upload/init',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({client:identity.id,peer:peerId,channel:channelId,name:encodeURIComponent(file.name),size:file.size,type:file.type||'application/octet-stream',fingerprint,replyTo})});
        const init=await response.json().catch(()=>({}));
        if(response.status===429) { state.sendCooldownUntil=Date.now()+(init.retryAfter||5000); throw Error('rate limit'); }
        if(!response.ok) { if(init.limit) { state.maxFileBytes=init.limit; syncLimitUI(); } throw Error(init.error||'upload init failed'); }
        task.uploadId=init.uploadId; task.startedReceived=init.received||0; let received=task.startedReceived; const chunkBytes=init.chunkBytes||1048576;
        if(init.resumed) showToast('已从 '+formatFileSize(received)+' 继续上传','info');
        while(received<file.size) {
          await waitWhileUploadPaused(task); if(task.cancelled) throw Error('cancelled');
          const end=Math.min(received+chunkBytes,file.size); const buffer=await file.slice(received,end).arrayBuffer(); if(task.cancelled) throw Error('cancelled');
          renderTransferTask(task,received,'正在校验 '+(received/file.size*100).toFixed(1)+'%');
          const hash=await sha256Hex(buffer); const next=await sendUploadChunk(task,buffer,received,hash);
          if(!Number.isInteger(next)||next<received||next>file.size) throw Error('invalid upload offset');
          received=next; renderTransferTask(task,received);
        }
        if(task.cancelled) throw Error('cancelled');
        renderTransferTask(task,file.size,'服务器正在核验完整文件');
        const doneResponse=await fetch(apiBase+'/api/upload/'+encodeURIComponent(task.uploadId)+'/complete',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({client:identity.id})});
        const done=await doneResponse.json().catch(()=>({})); if(!doneResponse.ok) throw Error(done.error||'upload finalize failed');
        const stillViewingTarget=requestedMode==='private'?(state.mode==='private'&&state.peer?.id===peerId):(state.mode==='channel'&&state.channel===channelId);
        if(stillViewingTarget&&!state.messages.some(message=>message.id===done.message?.id)) { state.messages.push(done.message); state.scrollLocked=true; render({newIds:[done.message.id],scrollToBottom:true}); }
        completed=true; renderTransferTask(task,file.size,'上传完成 · SHA-256 已校验'); $('connection').textContent='文件已发送'; showToast('文件发送成功','success');
      } catch(error) {
        if(error.message==='cancelled') { renderTransferTask(task,0,'上传已取消'); $('connection').textContent='上传已取消'; showToast('已取消文件上传','info'); }
        else if(error.message==='peer offline') { if(state.peer?.id===peerId) state.peer.online=false; renderTransferTask(task,0,'对方已离线'); showToast('对方已离线，文件未发送','warning'); renderChannels(); }
        else if(error.message==='channel changed') { renderTransferTask(task,0,'频道已切换'); showToast('频道已经切换，请重新选择文件','warning'); }
        else if(error.message==='invalid reply') { renderTransferTask(task,0,'引用消息已失效'); showToast('引用的消息已经失效，请重新发送文件','warning'); }
        else if(error.message==='file too large') showToast('文件不能超过 '+formatFileSize(state.maxFileBytes),'warning');
        else if(error.message==='rate limit') showToast('发送太快，每 5 秒只能发送 2 条内容','warning');
        else { renderTransferTask(task,0,'上传中断，重新选择同一文件可续传'); showToast('上传中断，24 小时内重新选择同一文件可继续','error'); }
      } finally {
        state.uploading=false; if(state.uploadTask===task) state.uploadTask=null; updateComposerControls();
        setTimeout(()=>{ if(!state.uploadTask) $('transfer-task').hidden=true; },completed?2400:4200);
      }
    }
    $('transfer-pause').addEventListener('click',()=>{
      const task=state.uploadTask; if(!task||task.cancelled) return;
      task.paused=!task.paused; setIcon($('transfer-pause'),task.paused?'play':'pause');
      $('transfer-pause').title=task.paused?'继续上传':'暂停上传'; $('transfer-pause').setAttribute('aria-label',$('transfer-pause').title);
      if(task.paused) { renderTransferTask(task,task.received||0,'上传已暂停'); if(task.controller) { task.pauseAbort=true; task.controller.abort(); } }
      else if(task.resume) task.resume();
    });
    $('transfer-cancel').addEventListener('click',async()=>{
      const task=state.uploadTask; if(!task) return; task.cancelled=true; if(task.resume) task.resume(); if(task.controller) task.controller.abort();
      $('transfer-pause').disabled=true; $('transfer-cancel').disabled=true; renderTransferTask(task,task.received||0,'正在取消上传');
      if(task.direct&&task.transferId) { const channel=rtcPeers.get(task.peerId)?.channel; if(channel?.readyState==='open') channel.send(JSON.stringify({kind:'file-cancel',transferId:task.transferId})); }
      if(task.transferId) { const waiter=rtcAckWaiters.get(task.transferId); if(waiter) { rtcAckWaiters.delete(task.transferId); waiter.reject(Error('cancelled')); } }
      if(task.uploadId) for(let attempt=0;attempt<3;attempt++) { try { const response=await fetch(apiBase+'/api/upload/'+encodeURIComponent(task.uploadId)+'?client='+encodeURIComponent(identity.id),{method:'DELETE'}); if(response.ok||response.status===404) break; } catch {} await wait(250); }
    });
    $('file-toggle').addEventListener('click',()=>{
      if(state.mode==='private'&&!state.peer) { showToast('当前私聊会话不可用','warning'); return; }
      if(state.mode==='private'&&state.peer.online===false) { $('connection').textContent='对方已离线'; showToast('对方已离线，暂时不能发送文件','warning'); return; }
      $('file-input').click();
    });
    async function handleSelectedFile(file) {
      if(!file) return;
      if(state.full||Date.now()<state.sendCooldownUntil) { showToast('当前暂时不能发送文件','warning'); return; }
      if(state.uploading) { showToast('请等待当前文件传输结束','warning'); return; }
      const requestedMode=state.mode;
      const peerId=requestedMode==='private'?(state.peer?.id||''):'';
      const channelId=state.channel;
      if(requestedMode==='private'&&(!peerId||state.peer?.online===false)) { showToast('对方已离线，暂时不能发送文件','warning'); return; }
      if(file.size<=0||file.size>state.maxFileBytes) { const tip=file.size<=0?'不能发送空文件':'文件不能超过 '+formatFileSize(state.maxFileBytes); $('connection').textContent=tip; showToast(tip,'warning'); return; }
      const replyTo=state.replyingTo?.id||'';
      if(replyTo) clearReply();
      if(requestedMode==='private') { const directResult=await tryDirectFile(file,peerId,channelId,replyTo); if(directResult) return; }
      await startChunkUpload(file,requestedMode,peerId,channelId,replyTo);
    }
    $('file-input').addEventListener('change',async e=>{
      const file=e.target.files?.[0]; e.target.value=''; await handleSelectedFile(file);
    });
    let dragDepth=0; const chatRoot=document.querySelector('.chat');
    function hasDraggedFiles(event) { return Array.from(event.dataTransfer?.types||[]).includes('Files'); }
    document.addEventListener('dragover',event=>{ if(hasDraggedFiles(event)) event.preventDefault(); });
    document.addEventListener('drop',event=>{ if(hasDraggedFiles(event)) event.preventDefault(); });
    chatRoot.addEventListener('dragenter',event=>{ if(!hasDraggedFiles(event)) return; event.preventDefault(); dragDepth++; chatRoot.classList.add('file-dragging'); });
    chatRoot.addEventListener('dragleave',event=>{ if(!hasDraggedFiles(event)) return; dragDepth=Math.max(0,dragDepth-1); if(!dragDepth) chatRoot.classList.remove('file-dragging'); });
    chatRoot.addEventListener('drop',async event=>{ if(!hasDraggedFiles(event)) return; event.preventDefault(); dragDepth=0; chatRoot.classList.remove('file-dragging'); const files=event.dataTransfer?.files; if(files?.length>1) showToast('当前一次只能发送一个文件，将发送第一个','info'); await handleSelectedFile(files?.[0]); });
    $('message').addEventListener('paste',async event=>{ const files=event.clipboardData?.files; if(!files?.length) return; event.preventDefault(); if(files.length>1) showToast('当前一次只能发送一个文件，将发送第一个','info'); await handleSelectedFile(files[0]); });
    $('reply-cancel').addEventListener('click',clearReply);
    let typingTimer=0; let lastTypingSentAt=0;
    function sendTypingState(active) {
      const now=Date.now();
      if(active&&now-lastTypingSentAt<700) return;
      lastTypingSentAt=active?now:0;
      fetch(apiBase+'/api/typing',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({id:identity.id,mode:state.mode,peer:state.peer?.id||'',channel:state.channel,active})}).catch(()=>{});
    }
    $('message').addEventListener('input',()=>{
      clearTimeout(typingTimer); const active=!!$('message').value.trim(); sendTypingState(active);
      if(active) typingTimer=setTimeout(()=>sendTypingState(false),1800);
    });
    $('message').addEventListener('blur',()=>{ clearTimeout(typingTimer); sendTypingState(false); });
    $('composer').addEventListener('submit', async e => {
      e.preventDefault();
      const input=$('message');
      const text=input.value.trim();
      if(!text || state.full) return;
      clearTimeout(typingTimer); sendTypingState(false);
      identity.name=normalizedName($('my-name').value)||'匿名访客';
      $('my-name').value=identity.name;
      saveLocalName(identity.name);
      $('send').disabled=true;
      let cooldown=0;
      try {
        const response=await fetch(apiBase+'/api/message',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({...identity,mode:state.mode,peer:state.peer?.id||'',channel:state.channel,text,replyTo:state.replyingTo?.id||''})});
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
          saveLocalName(identity.name);
        }
        input.value='';
        clearReply();
        state.scrollLocked = true;
      } catch(err) {
        if(err.message==='peer offline') {
          if(state.peer) state.peer.online=false;
          renderChannels();
          $('connection').textContent='对方已离线';
          showToast('对方已离线，消息未发送','warning');
        } else if(err.message==='invalid reply') { clearReply(); showToast('引用的消息已经失效，请重新选择','warning'); }
        else if(err.message!=='full'&&err.message!=='rate limit') { $('connection').textContent='发送失败，请重试'; showToast('发送失败，请重试','error'); }
      } finally {
        updateComposerControls();
        input.focus();
      }
    });
    fetch(apiBase+'/api/status').then(response=>response.json()).then(data=>{
      state.canAdmin = !!data.canAdmin;
      state.limit = data.limit || state.limit;
      if(typeof data.retentionMs==='number') state.retentionMs=data.retentionMs;
      if(typeof data.maxFileBytes==='number') state.maxFileBytes=data.maxFileBytes;
      if(typeof data.maxImagePreviewBytes==='number') state.maxImagePreviewBytes=data.maxImagePreviewBytes;
      syncLimitUI();
      updateComposerControls();
      if(state.canAdmin) {
        $('fab-admin').hidden=false;
      }
    }).catch(()=>{});
    $('fab-admin').addEventListener('click',openAdmin);
    [$('admin-retention'),$('admin-file-limit')].forEach(input=>input.addEventListener('input',()=>{
      const sanitized=input.value.replace(/[^0-9]/g,'').slice(0,input.maxLength);
      if(input.value!==sanitized) input.value=sanitized;
    }));
    $('admin-password').addEventListener('keydown',event=>{
      if(event.key!=='Enter'||event.isComposing) return;
      event.preventDefault();
      if(!$('admin-login-button').disabled) $('admin-login-button').click();
    });
    $('admin-login-button').addEventListener('click',async()=>{
      const btn = $('admin-login-button');
      btn.disabled = true;
      const response=await fetch(apiBase+'/api/admin/login',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({password:$('admin-password').value})});
      btn.disabled = false;
      if(!response.ok) {
        $('admin-password').value='';
        $('admin-password').placeholder='密码错误，请重试';
        $('admin-password').focus();
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
    document.querySelectorAll('.modal-backdrop').forEach(backdrop=>backdrop.addEventListener('click',event=>{ if(event.target===backdrop) backdrop.hidden=true; }));
    $('image-preview-close').addEventListener('click',closeImagePreview);
    $('image-preview-modal').addEventListener('click',event=>{ if(event.target===$('image-preview-modal')) closeImagePreview(); });
    $('image-preview-image').addEventListener('error',()=>{ if(state.previewingMessageId) { closeImagePreview(); showToast('图片预览已失效','warning'); } });
    document.addEventListener('keydown',event=>{ if(event.key==='Escape'&&!$('image-preview-modal').hidden) closeImagePreview(); });
    $('mobile-channel-select').addEventListener('change',e=>switchChannel(e.target.value));
    $('user-search').addEventListener('input',renderUsers);
    $('admin-ban-button').addEventListener('click',()=>setIpBan($('admin-ban-ip').value.trim(),true));
    $('admin-settings-save').addEventListener('click',saveAdminSettings);
    setInterval(tick,1000);
    window.addEventListener('beforeunload',()=>{ directFiles.forEach(file=>URL.revokeObjectURL(file.url)); });
    tick();
    poll();
  </script>
</body>
</html>
PAGE_END */
