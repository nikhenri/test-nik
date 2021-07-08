//----------------------------------------------------------------------------
// Contains function to flag error in text
//----------------------------------------------------------------------------
const vscode = require('vscode')
const fs = require('fs')
const os = require("os")
const child_process = require('child_process');
const utils = require('./utils')
const ouputChannel = require('./ouputChannel')

//----------------------------------------------------------------------------
const collection = vscode.languages.createDiagnosticCollection('Nik');
const tempDir = os.tmpdir().replace(/\\/g,"/")
const tempWorkDir = tempDir + "/work"

//if(fs.existsSync(tempWorkDir)) fs.rmdirSync(tempWorkDir, { recursive: true }) //is it needed ?

//----------------------------------------------------------------------------
// Save activeTextEditor text in file
// search activeTextEditor dependancy
// create and execute vlog cmd
// Extract info from cmd stdout
// Add error wave
async function updateDiagnostic() {
    console.log("Diagnostic")
	await utils.getFileText() // init

	let fileNameWithoutExt = utils.uriToFileNameWithoutExt(vscode.window.activeTextEditor.document.uri)
    let tempFilePath = tempDir + `/${fileNameWithoutExt}.sv`
    await saveCurrentTextToTemporayFile(fileNameWithoutExt, tempFilePath)
    let fileStr = await getCompilationFileList(fileNameWithoutExt, tempFilePath)
	let cmdStr = `vlog -incr -quiet -warning error -svinputport=relaxed -lint=default -suppress 2181,7061,2254 -work ${tempWorkDir} ${fileStr}`
	ouputChannel.log(cmdStr)

	child_process.exec(cmdStr, (error, stdout, stderr) => {
		if(error) {
		    ouputChannel.log(stdout)
			let firstErrorInfo = getFirstErrorInfo(stdout)
			collection.set(vscode.window.activeTextEditor.document.uri, [new vscode.Diagnostic(
                new vscode.Range(new vscode.Position(firstErrorInfo.line, 0), new vscode.Position(firstErrorInfo.line, 999)),
                firstErrorInfo.msg,
                vscode.DiagnosticSeverity.Error
            )])
		} else {
			collection.clear();
		}
	})
}

//----------------------------------------------------------------------------
async function saveCurrentTextToTemporayFile(fileNameWithoutExt, tempFilePath) {
    let text = (await utils.getFileText(fileNameWithoutExt)).text
	fs.writeFileSync(tempFilePath, text)
}

//----------------------------------------------------------------------------
async function getCompilationFileList(fileNameWithoutExt, tempFilePath) {
    let importNameList = await utils.getImportNameListRecursive(fileNameWithoutExt)
	importNameList.reverse()
	let fileStr = ""
	for (let fileNameWithoutExtList of importNameList)
		fileStr += await utils.getFilePath(fileNameWithoutExtList) + " "
	fileStr += tempFilePath
    return fileStr
}

//----------------------------------------------------------------------------
// ** Error: C:/Users/nhenri/AppData/Local/Temp/tcp_regs.sv(478): (vlog-2730) Undefined variable: 'vg_Read_Datas'.
// ** Error: (vlog-13069) C:/Users/nhenri/AppData/Local/Temp/tcp_regs.sv(32): near "input": syntax error, unexpected input, expecting ')'.
// ** Error (suppressible): C:/Users/nhenri/AppData/Local/Temp/tcp_regs.sv(226): (vlog-2623) Undefined variable: i_cfg_axi_aclk_p.
function getFirstErrorInfo(text) {
    let matchAll = Array.from(text.matchAll(/\*\* Error.*?:.*? ([^(]*)\((\d+)\): (?:\(.*?\) )?(.*)/g))
	if(!matchAll.length) return {line:9999, msg:text} //in case regexp FAIL
    //let path = matchAll[0][1]
    let line = parseInt(matchAll[0][2])-1
    let msg = matchAll[0][3]
    return {line, msg}
}

//----------------------------------------------------------------------------
module.exports = {
	updateDiagnostic
}