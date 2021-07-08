//----------------------------------------------------------------------------
// Main
//----------------------------------------------------------------------------
console.log('Entering extension.js...')

const vscode = require('vscode')
const utils = require('./utils')
const definition = require('./definition')
const terminal = require('./terminal')
const completionItems = require('./completionItems')
const child_process = require('child_process');


const path = require('path')
const fs = require('fs');
const os = require("os");
//----------------------------------------------------------------------------
// Register all functionnality we add
let timeOut
const activate = async (context) => {
	const collection = vscode.languages.createDiagnosticCollection('test');
	const fct = async () => {
		const tempDir = os.tmpdir().replace(/\\/g,"/")
		console.log(tempDir)


		// const collection = vscode.languages.createDiagnosticCollection('test');
		await utils.getFileText()

		let fileNameWithoutExt = "qmngr_tx_arbiter_events"

		let tempFilePath = tempDir + `/${fileNameWithoutExt}.sv`
		let txt = vscode.window.activeTextEditor.document.getText()
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
	//return

	// const collection = vscode.languages.createDiagnosticCollection('test');
	// if (vscode.window.activeTextEditor) {
	// 	updateDiagnostics(vscode.window.activeTextEditor.document, collection);
	// }
	// context.subscriptions.push(vscode.window.onDidChangeActiveTextEditor(editor => {
	// 	console.log("onDidChangeActiveTextEditor");
	// 	if (editor) {
	// 		updateDiagnostics(editor.document, collection);
	// 	}
	// }));

	if (vscode.window.activeTextEditor) fct()

	vscode.window.onDidChangeActiveTextEditor(editor => {
		console.log("onDidChangeActiveTextEditor")
		if (editor) fct()
	})

	vscode.workspace.onDidChangeTextDocument(event=>{
		console.log("onDidChangeTextDocument");
		clearTimeout(timeOut)
		timeOut = setTimeout(() => {
			console.log("timeout!")
			fct()
		}, 1000)
	})


	return
	utils.getFilePath() // init all the path
    context.subscriptions.push([
		vscode.languages.registerCompletionItemProvider('systemverilog', {provideCompletionItems:completionItems.provideCompletionItems}, '.'),
		vscode.languages.registerDefinitionProvider('systemverilog', {provideDefinition:definition.provideDefinition}),
		vscode.window.registerTerminalLinkProvider({provideTerminalLinks:terminal.provideTerminalLinks, handleTerminalLink:terminal.handleTerminalLink})
	])
}

//----------------------------------------------------------------------------
const updateDiagnostics = (document, collection) => {
	// if (document && path.basename(document.uri.fsPath) === 'sample-demo.rs') {
		console.log("here 3");

	if (document) {
		console.log("here 2");

		collection.set(document.uri, [{
			code: '',
			message: 'cannot assign twice to immutable variable `x`',
			range: new vscode.Range(new vscode.Position(3, 0), new vscode.Position(3, 999)),
			severity: vscode.DiagnosticSeverity.Error,
			source: '',
			relatedInformation: [
				new vscode.DiagnosticRelatedInformation(new vscode.Location(document.uri, new vscode.Range(new vscode.Position(1, 8), new vscode.Position(1, 9))), 'first assignment to `x`')
			]
		}]);
	} else {
		collection.clear();
	}
}

//----------------------------------------------------------------------------
// this method is called when your extension is deactivated
const deactivate = ()=>{}

//----------------------------------------------------------------------------
module.exports = {
	activate,
	deactivate
}

//----------------------------------------------------------------------------
/*
let out = vscode.window.createOutputChannel("Nik")
out.show()
out.appendLine('hello Nik')
*/
/*
//		let fileName = document.fileName
		// Display a message box to the user
		vscode.window.showInformationMessage('Hello World from test Nik!')

*/


/*
		console.time('process')
		let textt =
		console.timeLog('process')
		console.timeEnd('process')
		*/

		/*
			let a = vscode.window
	let aa = vscode.window.activeTextEditor
	let bb = vscode.window.activeTextEditor.document
	let aaa = vscode.window.visibleTextEditors
	*/


//----------------------------------------------------------------------------
// const getTextAfterPosition = utils.tryCatch((document, position) => {
// 	return document.getText().substring(document.offsetAt(position))
// })
//----------------------------------------------------------------------------
// const indexToPositionStartOfLine = utils.tryCatch((document, index) => {
// 	return new vscode.Position(document.positionAt(index).line, 0)
// })