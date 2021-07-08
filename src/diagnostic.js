const vscode = require('vscode')
const fs = require('fs')
const os = require("os")
const child_process = require('child_process');

const utils = require('./utils')

//----------------------------------------------------------------------------
const collection = vscode.languages.createDiagnosticCollection('nik');
const tempDir = os.tmpdir().replace(/\\/g,"/")
const tempWorkDir = tempDir + "/work"
const tempFilePath = tempDir + "/tmp.sv"

//if(fs.existsSync(tempWorkDir)) fs.rmdirSync(tempWorkDir, { recursive: true }) //is it needed ?

//----------------------------------------------------------------------------
async function updateDiagnostic() {
    console.log("Diagnostic")
	await utils.getFileText() // init
	let fileNameWithoutExt = utils.uriToFileNameWithoutExt(vscode.window.activeTextEditor.document.uri)

    await saveCurrentTextToTemporayFile(fileNameWithoutExt, tempFilePath)
    let fileStr = await getCompilationFileList(fileNameWithoutExt, tempFilePath)
	let cmdStr = `vlog -incr -quiet -warning error -svinputport=relaxed -lint=default -suppress 2181,7061,2254 -work ${tempWorkDir} ${fileStr}`
	console.log(cmdStr)

	child_process.exec(cmdStr, (error, stdout, stderr) => {
		if(error) {
		    console.log(stdout)
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
function getFirstErrorInfo(text) {
    let matchAll = Array.from(text.matchAll(/\*\* Error: \(.*?\) ([^(]*)\((\d+)\): (.*)/g))
    let path = matchAll[0][1]
    let line = parseInt(matchAll[0][2])-1
    let msg = matchAll[0][3]
    return {line, msg, path}
}

//----------------------------------------------------------------------------
module.exports = {
	updateDiagnostic
}