try {
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
        getFilePath.listOfPath = (await vscode.workspace.findFiles("**/*.*v")).map(x => x.fsPath)
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
	const matches = fileText.matchAll(new RegExp(`^[ ]*(?:input|output|inout)?[ ]*(\\w+).*?${signalName}`, "gm"));
	let group_matches = Array.from(matches).slice(0, -1).map(x => x[1])
	return group_matches[0]
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
function getStructInFile(structName, filePath) {
	//const struct_list =  text.match(/^[ ]*\w*[ ]*struct+[\s\S]*?}[\s\S]*?;$/gm)
	let text = fs.readFileSync(filePath, 'utf8');
	const struct_list =  getStructList(text)
	for (let struct of struct_list) {
		if(getStructName(struct) == structName) {
			console.log(`Found struct`)
			const completionList = [];
			for (let structMember of getStructMemberName(struct)) {
				completionList.push(new vscode.CompletionItem(structMember))
			}
			return completionList
		}
	}
}
//----------------------------------------------------------------------------
function getImportName (text) {
	const matches = text.matchAll(/^[ ]*import[ ]*?(.*);$/gm);
	let groupMatch = Array.from(matches).slice(0, -1).map(x => x[1])
	let ImportNameList = []
	for (let match of groupMatch) {
		for (let packageStr of match.split(",")) {
			let packageName = packageStr.trim().split("::")[0]
			console.log(`Found package ${packageName}`);
			ImportNameList.push(packageName)
		}
	}
	return ImportNameList
}
//----------------------------------------------------------------------------
async function getStruct(structName, filePath) {
	let returnFromFile = getStructInFile(structName, filePath)
	if (returnFromFile) {
		console.log(`Return struct from file ${filePath}`);
		return returnFromFile
	}
	let text = fs.readFileSync(filePath, 'utf8');
	importFileNameList = getImportName(text)
	for (let importFileName of importFileNameList) {
		let path = await getFilePath(importFileName)
		let returnValue = getStruct(structName, path)
		if (returnValue) {
			return returnValue
		}
	}
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
					return getStruct(declaration_type, document.fileName)
				}
			}
		},
		'.' // triggered whenever a '.' is being typed
	);

	//----------------------------------------------------------------------------
	context.subscriptions.push(provider2);

	async function provideDefinition(document, position, token) {
		console.log("CTRL")
		const line = document.lineAt(position).text
		const word = document.getText(document.getWordRangeAtPosition(position));
		//const position_start_of_line = position.with(new vscode.Position(position.line, 0))
		//const text_after_cursor = document.getText().substring(document.offsetAt(position_start_of_line))

		if(line.match(/^[ ]*[a-zA-Z0-9_]*\s*#?\s*\(?\s*$/)) { // is this a module
		//if(text_after_cursor.match(/^[ ]*[a-zA-Z0-9_]*\s*#?\s*\(/)) { // is this a module
			console.log(`Searching entity: ${word}`)
			const path = await getFilePath(word)
			console.log(`FilePath for entity= ${path}`)
			if(path) return new vscode.Location(vscode.Uri.file(path), new vscode.Position(0, 0));
		}
		if (line.match(/^\s*import\s\w+::/)) {
			console.log(`Searching package: ${word}`)
			const path = await getFilePath(word)
			console.log(`FilePath for package= ${path}`)
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
} catch (error) {
	console.error(">> CRASH stack:\n" + error);
}
/*
const out = vscode.window.createOutputChannel("Nik");
out.show();
out.appendLine('hello Nik');
*/

//		const fileName = document.fileName;
// const workDir = path.dirname(fileName);




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
	// });.
