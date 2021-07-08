const vscode = require('vscode')
const utils = require('./utils')

const path = require('path')
const fs = require('fs')
const os = require("os")
const child_process = require('child_process');
//----------------------------------------------------------------------------
const collection = vscode.languages.createDiagnosticCollection('test');

async function updateDiagnostic() {
	const tempDir = os.tmpdir().replace(/\\/g,"/")
	console.log(tempDir)


	// const collection = vscode.languages.createDiagnosticCollection('test');
	await utils.getFileText()

	let fileNameWithoutExt = "qmngr_tx_arbiter_events"

	let tempFilePath = tempDir + `/${fileNameWithoutExt}.sv`
	let txt = (await utils.getFileText(fileNameWithoutExt)).text
	fs.writeFileSync(tempFilePath, txt)

	// let tempFilePath = tempDir + `/${fileNameWithoutExt}.sv`
	let importNameList = await utils.getImportNameListRecursive(fileNameWithoutExt)
	//importNameList.unshift(fileNameWithoutExt)
	importNameList.reverse()
	let fileStr = ""
	for (let fileNameWithoutExtList of importNameList)
		fileStr += await utils.getFilePath(fileNameWithoutExtList) + " "
	fileStr += tempFilePath
	let workPath = tempDir + "/work"
	let cmdStr = `vlog -quiet -warning error -svinputport=relaxed -lint=default -suppress 2181,7061,2254 -work ${workPath} ${fileStr}`
	console.log(cmdStr)

	//child_process.exec("vdel -all")
	fs.rmdirSync(workPath, { recursive: true });
	child_process.exec(cmdStr, (error, stdout, stderr) => {
		console.error(`exec error: ${error}`)
		console.log(`stdout: ${stdout}`)
		console.error(`stderr: ${stderr}`)
		if (error) {
			let matchAll = Array.from(stdout.matchAll(/\*\* Error: \(.*?\) ([^(]*)\((\d+)\): (.*)/g))
			let filePath = matchAll[0][1]
			let line = parseInt(matchAll[0][2])-1
			let msg = matchAll[0][3]

			collection.set(vscode.window.activeTextEditor.document.uri, [new vscode.Diagnostic(
				new vscode.Range(new vscode.Position(line, 0), new vscode.Position(line, 999)),
				msg,
				vscode.DiagnosticSeverity.Errore
			)])
		//console.error(`exec error: ${error}`)
		} else {
			collection.clear();
			console.log("No error");
		}
	})
}



//----------------------------------------------------------------------------
module.exports = {
	updateDiagnostic
}