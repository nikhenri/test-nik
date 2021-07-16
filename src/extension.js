//----------------------------------------------------------------------------
// Main
//----------------------------------------------------------------------------
const vscode = require('vscode')
const utils = require('./utils')
const definition = require('./definition')
const terminal = require('./terminal')
const completionItems = require('./completionItems')
const diagnostic = require('./diagnostic')
const ouputChannel = require('./ouputChannel')

//----------------------------------------------------------------------------
let extensionId = 'NikHenri.nikhenri'
ouputChannel.log(`Loading ${extensionId} v${vscode.extensions.getExtension(extensionId)['packageJSON']['version']}...`)

//----------------------------------------------------------------------------
// Register all functionnality we add
function activate(context) {
	utils.getFilePath() // init all the path

    context.subscriptions.push([
		vscode.languages.registerCompletionItemProvider('systemverilog', {provideCompletionItems: completionItems.provideCompletionItems}, '.'),
		vscode.languages.registerDefinitionProvider('systemverilog', {provideDefinition: definition.provideDefinition}),
		vscode.window.registerTerminalLinkProvider({provideTerminalLinks: terminal.provideTerminalLinks, handleTerminalLink: terminal.handleTerminalLink}),
		vscode.workspace.onDidChangeTextDocument(event => {
			if(vscode.languages.match('systemverilog', event.document))
				onDidChangeTextDocumentDebounce(diagnostic.updateDiagnostic, 500)
		}),
		vscode.window.onDidChangeActiveTextEditor(editor => {
			if(vscode.languages.match('systemverilog', editor.document))
				diagnostic.updateDiagnostic(editor)
		}),
	])

	if(vscode.window.activeTextEditor && vscode.languages.match('systemverilog', vscode.window.activeTextEditor.document))
		diagnostic.updateDiagnostic()
}

//----------------------------------------------------------------------------
function onDidChangeTextDocumentDebounce(fct, debounceMs) {
	clearTimeout(onDidChangeTextDocumentDebounce.timeOut)
	onDidChangeTextDocumentDebounce.timeOut = setTimeout(() => fct(), debounceMs)
}

//----------------------------------------------------------------------------
// this method is called when your extension is deactivated
function deactivate() {
}

//----------------------------------------------------------------------------
module.exports = {
	activate,
	deactivate
}

//----------------------------------------------------------------------------
/*
		// Display a message box to the user
		vscode.window.showInformationMessage('Hello World from test Nik!')

*/


/*
		console.time('process')
		let textt =
		console.timeLog('process')
		console.timeEnd('process')
*/
