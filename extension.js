const vscode = require('vscode');
const fs = require('fs')
const path = require('path');

console.log('Entering extension.js...');

//----------------------------------------------------------------------------
async function getFilePath(fileNameWithoutExt) {
	let filePath
	const search_fileNameWithoutExt = (x=> path.parse(x).name == fileNameWithoutExt)
	if(!getFilePath.listOfPath || !(filePath = getFilePath.listOfPath.find(search_fileNameWithoutExt))) {
		console.log("Updating getFilePath.listOfPath...")
        getFilePath.listOfPath = (await vscode.workspace.findFiles("**/*.sv")).map(x => x.fsPath)
		filePath = getFilePath.listOfPath.find(search_fileNameWithoutExt)
		if(!filePath) console.log(`Was not able to found '${fileNameWithoutExt}'`)
    }
	return filePath;
}

//----------------------------------------------------------------------------
async function getFileText(fileNameWithoutExt) {
	const path = await getFilePath(fileNameWithoutExt)
	console.log(`Reading '${path}'`)
	return fs.readFileSync('c:/Users/nhenri/Desktop/tcp_ip_ip_vs_code_ext/src/common/pkg/qmngr_pkg.sv', 'utf8');
}

//----------------------------------------------------------------------------
function getFullSignalName(fullLine) {
	const match = fullLine.match(/[\w\.]+\w*\.$/g) // start with a letter, followed by any nb of caracter
	if(match) return match[0].slice(0, -1)
}

//----------------------------------------------------------------------------
function getSignalTypeName(fileText, signalName) {
	// first word that is not input | output | inout
	return fileText.match(`\\b(?!input\\s|output\\s|inout\\s)[A-Za-z]+.*${signalName}`)[0]
}

//----------------------------------------------------------------------------
function getStructList(fileText) {
	return fileText.match(/(?![ ])\w*[ ]*struct[ {]+[\s\S]*?}[\s\S]*?;$/gm)
}

//----------------------------------------------------------------------------
function getStructName(structText) {
	return structText.match(/}[ ]*(\w+)[ ]*;$/m)[1]
}

//----------------------------------------------------------------------------
function getStructMemberName(structText) {
	const matches = structText.matchAll(/(\w+)[ ]*;/g);
	let group_matches = Array.from(matches).slice(0, -1).map(x => x[1])
	return group_matches;
}

//----------------------------------------------------------------------------
async function activate(context) {
	//console.log(`>>3 ${await getFilePath('qmngr_vx.sv')}`)
	//console.log(`>>4 ${await getFileText('qmngr_pkg.sv')}`)

	let cnt = 0

	const provider2 = vscode.languages.registerCompletionItemProvider(
		'systemverilog',
		{
			provideCompletionItems(document, position) {
				const linePrefix = document.lineAt(position).text.substr(0, position.character);
				if (!linePrefix.endsWith('.')) return undefined

				let fullSignalName = getFullSignalName(linePrefix)
				if(fullSignalName) {
					console.log(`searching for variable '${fullSignalName}'`)
					if(fullSignalName.split('.').length > 1) {
						console.log(`Dont support multi-member, exiting`)
						return undefined
					}

					let text = document.getText()

					const declaration_type = getSignalTypeName(text, fullSignalName)
					console.log(`Type is '${declaration_type}'`)

					//const struct_list =  text.match(/^[ ]*\w*[ ]*struct+[\s\S]*?}[\s\S]*?;$/gm)
					const struct_list =  getStructList(text)
					for (let struct of struct_list) {
						if(getStructName(struct) == declaration_type) {
							console.log(`Found struct`)
							const completionList = [];
							for (let structMember of getStructMemberName(struct)) {
								completionList.push(new vscode.CompletionItem(structMember))
							}
							return completionList
						}
					}
                    const import_regexp = text.match(/(?![ ])import[ ]+[\s\S]*?;$/gm)
				}
			}
		},
		'.' // triggered whenever a '.' is being typed
	);


	context.subscriptions.push(provider2);

	async function provideDefinition(document, position, token) {
		const word = document.getText(document.getWordRangeAtPosition(position));
		const position_start_of_line = position.with(new vscode.Position(position.line, 0))
		const text_after_cursor = document.getText().substring(document.offsetAt(position_start_of_line))

		if(text_after_cursor.match(/^[ ]*[a-zA-Z0-9_]*\s*#?\s*\(/)) {
			console.log(`Searching entity: ${word}`)
			const path = await getFilePath(word)
			console.log(`FilePath for entity= ${path}`)
			if(path) return new vscode.Location(vscode.Uri.file(path), new vscode.Position(0, 0));
		}
	}

	context.subscriptions.push(vscode.languages.registerDefinitionProvider(['systemverilog'], {
		provideDefinition
	}));

}
//----------------------------------------------------------------------------

// this method is called when your extension is deactivated
function deactivate() {}
//----------------------------------------------------------------------------

module.exports = {
	activate,
	deactivate
}
//----------------------------------------------------------------------------

/*
const out = vscode.window.createOutputChannel("Nik");
out.show();
out.appendLine('hello Nik');
*/

//		const fileName = document.fileName;
// const workDir = path.dirname(fileName);



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
