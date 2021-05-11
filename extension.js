const vscode = require('vscode');



let a = `module rand_num_generator#(
    parameter N = 3
)

(
    input wire clk, reset, 
    output wire [N:0] q
);

assign r_next = {feedback_value, r_reg[N:1]};
assign q = r_reg;

typedef struct packed {
    bit [7:0]  addr;
    bit        valid;
    bit [31:0] data;
  } mem_pkt;
   
  mem_pkt pkt;
  
pkt.
endmodule
`
let b = `balbal (woof.
 	tata <= pkt.
 	woof toto. +pkt.`
// let tt = b.match(/[A-Za-z0-9]*\.$/);
let tt = b.match(/[A-Za-z0-9]*\.$/g); //give last word
let c = 0

// this method is called when your extension is activated
// your extension is activated the very first time the command is executed

/**
 * @param {vscode.ExtensionContext} context
 */
function activate(context) {

	// Use the console to output diagnostic information (console.log) and errors (console.error)
	// This line of code will only be executed once when your extension is activated
	console.log('Congratulations, your extension "test-nik" is now active!');

	// The command has been defined in the package.json file
	// Now provide the implementation of the command with  registerCommand
	// The commandId parameter must match the command field in package.json
	let disposable = vscode.commands.registerCommand('test-nik.testNik', function () {
		let a = vscode.window.activeTextEditor
		let b = vscode.window.activeTextEditor.document
		let c = vscode.window.activeTextEditor.selection
		console.log(`Path ${b.fileName}`)
		console.log(`lauggage ${b.languageId}`)
		console.log(`Text ${b.getText()}`)
		console.log(`Text ${c.active.line}`)
		console.log(`Text ${c.active.character}`)
		//console.log(`Text ${b.getWordRangeAtPosition()}`)
		//console.log(`Text ${b.lineAt()}`)
		// The code you place here will be executed every time your command is executed

		// Display a message box to the user
		vscode.window.showInformationMessage('Hello World from test Nik!');
	});

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
	let cnt = 0







	const provider2 = vscode.languages.registerCompletionItemProvider(
		'systemverilog',
		{
			provideCompletionItems(document, position) {

				// get all text until the `position` and check if it reads `console.`
				// and if so then complete if `log`, `warn`, and `error`
				//const linePrefix = document.lineAt(position).text.substr(0, position.character);
				const line = document.lineAt(position).text
			
				if (!line.endsWith('.')) {
					return undefined;
				}

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
				let variableName = line.match(/[A-Za-z]+\w*\.$/g)[0] //get the match
				variableName = variableName.slice(0, -1) // remove the '.'
				console.log(`searching for variable ${variableName}`)
				cnt += 1
				return [
					new vscode.CompletionItem(`suck it Gui ${cnt}`, vscode.CompletionItemKind.Method),
					//new vscode.CompletionItem('warn', vscode.CompletionItemKind.Method),
					//new vscode.CompletionItem('error', vscode.CompletionItemKind.Method),
				];
			}
		},
		'.' // triggered whenever a '.' is being typed
	);


	context.subscriptions.push(disposable, provider2);
}

// this method is called when your extension is deactivated
function deactivate() {}

module.exports = {
	activate,
	deactivate
}
