//----------------------------------------------------------------------------
// Main
//----------------------------------------------------------------------------
console.log('Entering extension.js...')

const vscode = require('vscode')
const utils = require('./utils')
const definition = require('./definition')
const terminal = require('./terminal')
const completionItems = require('./completionItems')

//----------------------------------------------------------------------------
// Register all functionnality we add
const activate = (context) => {
	utils.getFilePath() // init all the path
    context.subscriptions.push([
		vscode.languages.registerCompletionItemProvider('systemverilog', {provideCompletionItems:completionItems.provideCompletionItems}, '.'),
		vscode.languages.registerDefinitionProvider('systemverilog', {provideDefinition:definition.provideDefinition}),
		vscode.window.registerTerminalLinkProvider({provideTerminalLinks:terminal.provideTerminalLinks, handleTerminalLink:terminal.handleTerminalLink})
	])
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