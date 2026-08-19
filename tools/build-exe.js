const fs = require('fs');
const path = require('path');
const { spawnSync } = require('child_process');

const root = path.resolve(__dirname, '..');
const sourcePath = path.join(root, 'server.js');
const buildDir = path.join(root, 'build');
const distDir = path.join(root, 'dist');
const pagePath = path.join(buildDir, 'page.html');
const configPath = path.join(buildDir, 'sea-config.json');
const requestedOutputName = String(process.env.VOID_CHAT_EXE_NAME || 'VOID-Chat.exe');
if (!/^[A-Za-z0-9._-]+\.exe$/i.test(requestedOutputName)) throw new Error('VOID_CHAT_EXE_NAME 必须是安全的 .exe 文件名');
const outputPath = path.join(distDir, requestedOutputName);

const source = fs.readFileSync(sourcePath, 'utf8');
const startMarker = '/* PAGE_START';
const endMarker = 'PAGE_END */';
const startIndex = source.lastIndexOf(startMarker);
const endIndex = source.lastIndexOf(endMarker);

if (startIndex === -1 || endIndex === -1 || endIndex <= startIndex) {
  throw new Error('无法从 server.js 中提取网页资源');
}

const page = source.slice(startIndex + startMarker.length, endIndex).trimStart();
fs.mkdirSync(buildDir, { recursive: true });
fs.mkdirSync(distDir, { recursive: true });
fs.writeFileSync(pagePath, page, 'utf8');

const config = {
  main: sourcePath,
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

const sizeMb = (fs.statSync(outputPath).size / 1024 / 1024).toFixed(1);
console.log(`\n构建完成: ${outputPath}`);
console.log(`文件大小: ${sizeMb} MB`);
