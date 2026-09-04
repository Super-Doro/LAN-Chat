const fs = require('fs');
const path = require('path');
const { spawnSync } = require('child_process');

const root = path.resolve(__dirname, '..');
const sourcePath = path.join(root, 'server.js');
const buildDir = path.join(root, 'build');
const pagePath = path.join(buildDir, 'page.html');
const mainPath = path.join(buildDir, 'server.sea.js');
const configPath = path.join(buildDir, 'sea-config.json');
const requestedOutputName = String(process.env.LAN_CHAT_EXE_NAME || 'LAN_CHAT.exe');
if (!/^[A-Za-z0-9][A-Za-z0-9 ._-]*\.exe$/i.test(requestedOutputName)) throw new Error('LAN_CHAT_EXE_NAME 必须是安全的 .exe 文件名');
const rawOutputName = `${path.parse(requestedOutputName).name}.raw.exe`;
const outputPath = path.join(buildDir, rawOutputName);

const source=fs.readFileSync(sourcePath,'utf8');
const startMarker='/* PAGE_START';
const endMarker='PAGE_END */';
const start=source.lastIndexOf(startMarker);
const end=source.lastIndexOf(endMarker);
if(start<0||end<=start) throw new Error('无法从 server.js 中提取网页资源');
fs.mkdirSync(buildDir, { recursive: true });
fs.writeFileSync(pagePath,source.slice(start+startMarker.length,end).trimStart(),'utf8');
fs.writeFileSync(mainPath,source.slice(0,start).trimEnd()+'\n','utf8');

const config = {
  main: mainPath,
  mainFormat: 'commonjs',
  output: outputPath,
  disableExperimentalSEAWarning: true,
  useSnapshot: false,
  useCodeCache: false,
  execArgvExtension: 'none',
  assets: {
    'page.html': pagePath
  }
};

fs.writeFileSync(configPath, JSON.stringify(config, null, 2), 'utf8');

const result = spawnSync(process.execPath, ['--build-sea', configPath], {
  cwd: root,
  stdio: 'inherit'
});

if (result.error) throw result.error;
if (result.status !== 0) process.exit(result.status || 1);
for (const temporary of [pagePath,mainPath,configPath]) fs.rmSync(temporary,{force:true});

const sizeMb = (fs.statSync(outputPath).size / 1024 / 1024).toFixed(1);
console.log(`\n原始 SEA 已生成（尚未压缩）: ${outputPath}`);
console.log(`原始运行时大小: ${sizeMb} MB`);
