//----------------------------------------------------------------------------
// Main
//----------------------------------------------------------------------------
const vscode = require('vscode')
const utils = require('./utils')
const definition = require('./definition')
const terminal = require('./terminal')
const completionItemsDot = require('./completionItemsDot')
const completionItemsDollar = require('./completionItemsDollar')
const completionItemsVariable = require('./completionItemsVariable')
const diagnostic = require('./diagnostic')
const ouputChannel = require('./ouputChannel')

//----------------------------------------------------------------------------
let extensionId = 'NikHenri.nikhenri'
ouputChannel.log(`Loading ${extensionId} v${vscode.extensions.getExtension(extensionId)['packageJSON']['version']}...`)

//----------------------------------------------------------------------------
// Register all functionnality we have
function activate(context) {
	return utils.tryCatch(__activate, context)
}

//----------------------------------------------------------------------------
// Register all functionnality we have
function __activate(context) {
	if (vscode.workspace.workspaceFolders) {
		utils.getFilePath() // init all the path
		context.subscriptions.push([
			vscode.languages.registerCompletionItemProvider('systemverilog', {provideCompletionItems: completionItemsDot.provideCompletionItemsDot}, '.'),
			vscode.languages.registerCompletionItemProvider('systemverilog', {provideCompletionItems: completionItemsDollar.provideCompletionItemsDollar}, '$'),
			vscode.languages.registerCompletionItemProvider('systemverilog', {provideCompletionItems: completionItemsVariable.provideCompletionItemsVariable}),
			vscode.languages.registerDefinitionProvider('systemverilog', {provideDefinition: definition.provideDefinition}),
		 	vscode.window.registerTerminalLinkProvider({provideTerminalLinks: terminal.provideTerminalLinks, handleTerminalLink: terminal.handleTerminalLink}),
		 	vscode.workspace.onDidChangeTextDocument(event => {
			if(vscode.languages.match('systemverilog', event.document))
				onDidChangeTextDocumentDebounce(diagnostic.updateDiagnostic, 2000)
			}),
			vscode.window.onDidChangeActiveTextEditor(editor => {
				if(vscode.languages.match('systemverilog', editor.document))
					diagnostic.updateDiagnostic(editor)
			}),
		])

		if(vscode.window.activeTextEditor && vscode.languages.match('systemverilog', vscode.window.activeTextEditor.document))
			diagnostic.updateDiagnostic()

		ouputChannel.log(`${extensionId} activate() done`)
	}
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
