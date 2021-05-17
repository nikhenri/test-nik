const vscode = require('vscode');

const path = require('path');
const fs = require('fs');
// this method is called when your extension is activated
// your extension is activated the very first time the command is executed

/**
 * @param {vscode.ExtensionContext} context
 */
function activate(context) {

	// Use the console to output diagnostic information (console.log) and errors (console.error)
	// This line of code will only be executed once when your extension is activated
	console.log('Congratulations, your extension "test-nik" is now active!');


	let cnt = 0



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
				let match = linePrefix.match(/[A-Za-z\.]+\w*\.$/g) // start with a letter, followed by any nb of caracter
				if (match) {
					console.log("searching for signal name...")

					const variableName = match[0].slice(0, -1)
					console.log(`searching for variable '${variableName}'`)
					text = document.getText()
					// first word that is not input | output | inout
					let match_declaration = text.match(`\\b(?!input\\s|output\\s|inout\\s)([A-Za-z]+).*${variableName}`)
					const declaration_type = match_declaration[0]
					console.log(`Type is '${declaration_type}'`)


					let struct_list =  text.match(/^[ ]*\w*[ ]*struct+[\s\S]*?}[\s\S]*?;$/gm)
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


	function provideDefinition(document, position, token) {
		console.log("here!!")
		const fileName = document.fileName;
		const workDir = path.dirname(fileName);
		const word = document.getText(document.getWordRangeAtPosition(position));
		const line = document.lineAt(position);
		//const projectPath = util.getProjectPath(document);
	   
		console.log ('= = = = = enter provideddefinition method = = = =');
		console.log ('filename: '+ fileName); // full path of current file
		console.log ('workdir: '+ workDir); // directory of the current file
		console.log ('word: '+ word); // the word of the current cursor
		console.log ('line: ' +  line.text) // current cursor line
		//console.log ('projectpath: '+ projectpath) // current project directory
		//Processing only package.json file
		//if (/\/package\.json$/.test(fileName)) {
		console.log(word, line.text);
		const json = document.getText();
			//return new vscode.Location(vscode.Uri.file(destPath), new vscode.Position(0, 0));
		return new vscode.Location(document.uri, new vscode.Position(0, 0));

	}
	context.subscriptions.push(vscode.languages.registerDefinitionProvider(['systemverilog'], {
		provideDefinition
	}));
}

// this method is called when your extension is deactivated
function deactivate() {}

module.exports = {
	activate,
	deactivate
}

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
