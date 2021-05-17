const vscode = require('vscode');
const fs = require('fs')

console.log('Entering extension.js...');
// this method is called when your extension is activated
// your extension is activated the very first time the command is executed

/**
 * @param {vscode.ExtensionContext} context
*/
async function getFilePath(fileNameWithExt) {
	let path
	if(!getFilePath.listOfPath || !(path = getFilePath.listOfPath.find(x=> x.endsWith(fileNameWithExt)))) {
		console.log("Updating getFilePath.listOfPath...")
		const mapFct = (process.platform === "win32" ? (x => x.path.slice(1)) : (x => x.path))
        getFilePath.listOfPath = (await vscode.workspace.findFiles("**/*.sv")).map(mapFct)
		path = getFilePath.listOfPath.find(x=> x.endsWith(fileNameWithExt))
		if(!path) console.log(`Was not able to found '${fileNameWithExt}'`)
    }
	return path;
}

async function getFileText(fileNameWithExt) {
	let path = await getFilePath(fileNameWithExt)
	console.log(`Reading '${path}'`)
	return fs.readFileSync('c:/Users/nhenri/Desktop/tcp_ip_ip_vs_code_ext/src/common/pkg/qmngr_pkg.sv', 'utf8');
}

function getSignalName() {

}

async function activate(context) {
	console.log('Activation...');

	console.log("woof")
	//console.log(`>>1 ${await getFilePath('qmngr_tx.sv')}`)
	//console.log(`>>2 ${await getFilePath('qmngr_tx.sv')}`)
	//console.log(`>>3 ${await getFilePath('qmngr_vx.sv')}`)
	console.log(`>>4 ${await getFileText('qmngr_pkg.sv')}`)
	console.log("miawf")

	let cnt = 0

    const out = vscode.window.createOutputChannel("Nik");
    out.show();
    out.appendLine('hello Nik');

	const provider2 = vscode.languages.registerCompletionItemProvider(
		'systemverilog',
		{
			provideCompletionItems(document, position) {

				const linePrefix = document.lineAt(position).text.substr(0, position.character);
				if (!linePrefix.endsWith('.')) {
					return undefined;
				}

				// bit tot = test.
				// bit tot = test.tata.
				// bit tot = test.tata.);
				console.log("searching for signal name...")

				let match = linePrefix.match(/[\w\.]+\w*\.$/g) // start with a letter, followed by any nb of caracter
				if (match) {

                    // fileName = document.fileName
					const variableName = match[0].slice(0, -1)
					console.log(`searching for variable '${variableName}'`)
					let text = document.getText()
					// first word that is not input | output | inout
					const match_declaration = text.match(`\\b(?!input\\s|output\\s|inout\\s)[A-Za-z]+.*${variableName}`)
					const declaration_type = match_declaration[0]
					console.log(`Type is '${declaration_type}'`)

					//const struct_list =  text.match(/^[ ]*\w*[ ]*struct+[\s\S]*?}[\s\S]*?;$/gm)
					const struct_list =  text.match(/(?![ ])\w*[ ]*struct[ {]+[\s\S]*?}[\s\S]*?;$/gm)
                    const import_regexp = text.match(/(?![ ])import[ ]+[\s\S]*?;$/gm)

					cnt += 1
					return [
						new vscode.CompletionItem(`Nik ${cnt}`, vscode.CompletionItemKind.Method),
						//new vscode.CompletionItem('warn', vscode.CompletionItemKind.Method),
					];
				}
			}
		},
		'.' // triggered whenever a '.' is being typed
	);


	context.subscriptions.push(provider2);
}

// this method is called when your extension is deactivated
function deactivate() {}

module.exports = {
	activate,
	deactivate
}
//console.log(`Previous file '${fileName}', current '${document.fileName}'`)

				// const line = document.lineAt(position).text

				// const text = document.getText()
				// console.log("----------")
				// console.log(text)
				// console.log("----------")

				// let u = document.lineAt(position)
				// console.log(document.lineAt(position))
				// console.log("----------")
				// console.log(position)
				// console.log("----------")
				// console.log(document.lineAt(position).text)

					// const provider1 = vscode.languages.registerCompletionItemProvider('systemverilog', {

	// 	provideCompletionItems(document, position, token, context) {

	// 		// a simple completion item which inserts `Hello World!`
	// 		const simpleCompletion = new vscode.CompletionItem('Hello World!');

	// 		// a completion item that inserts its text as snippet,
	// 		// the `insertText`-property is a `SnippetString` which will be
	// 		// honored by the editor.
	// 		const snippetCompletion = new vscode.CompletionItem('Good part of the day');
	// 		snippetCompletion.insertText = new vscode.SnippetString('Good ${1|morning,afternoon,evening|}. It is ${1}, right?');
	// 		snippetCompletion.documentation = new vscode.MarkdownString("Inserts a snippet that lets you select the _appropriate_ part of the day for your greeting.");

	// 		// a completion item that can be accepted by a commit character,
	// 		// the `commitCharacters`-property is set which means that the completion will
	// 		// be inserted and then the character will be typed.
	// 		const commitCharacterCompletion = new vscode.CompletionItem('console');
	// 		commitCharacterCompletion.commitCharacters = ['.'];
	// 		commitCharacterCompletion.documentation = new vscode.MarkdownString('Press `.` to get `console.`');

	// 		// a completion item that retriggers IntelliSense when being accepted,
	// 		// the `command`-property is set which the editor will execute after
	// 		// completion has been inserted. Also, the `insertText` is set so that
	// 		// a space is inserted after `new`
	// 		const commandCompletion = new vscode.CompletionItem('new');
	// 		commandCompletion.kind = vscode.CompletionItemKind.Keyword;
	// 		commandCompletion.insertText = 'new ';
	// 		commandCompletion.command = { command: 'editor.action.triggerSuggest', title: 'Re-trigger completions...' };

	// 		// return all completion items as array
	// 		return [
	// 			simpleCompletion,
	// 			snippetCompletion,
	// 			commitCharacterCompletion,
	// 			commandCompletion
	// 		];
	// 	}
	// });



	// The command has been defined in the package.json file
	// Now provide the implementation of the command with  registerCommand
	// The commandId parameter must match the command field in package.json
	// let disposable = vscode.commands.registerCommand('test-nik.testNik', function () {
	// 	let a = vscode.window.activeTextEditor
	// 	let b = vscode.window.activeTextEditor.document
	// 	let c = vscode.window.activeTextEditor.selection
	// 	console.log(`Path ${b.fileName}`)
	// 	console.log(`lauggage ${b.languageId}`)
	// 	console.log(`Text ${b.getText()}`)
	// 	console.log(`Text ${c.active.line}`)
	// 	console.log(`Text ${c.active.character}`)
	// 	//console.log(`Text ${b.getWordRangeAtPosition()}`)
	// 	//console.log(`Text ${b.lineAt()}`)
	// 	// The code you place here will be executed every time your command is executed

	// 	// Display a message box to the user
	// 	vscode.window.showInformationMessage('Hello World from test Nik!');
	// });
