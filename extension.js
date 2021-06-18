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
	return fs.readFileSync(path, 'utf8');
}

//----------------------------------------------------------------------------
function getFullSignalName(fullLine) {
	const match = fullLine.match(/[\w\.]+\w*\.$/g) // start with a letter, followed by any nb of caracter
	if(match) return match[0].slice(0, -1)
}

//----------------------------------------------------------------------------
function getSignalTypeName(str, signalName) {
	// first word that is not input | output | inout
    const matchAll = Array.from(str.matchAll(new RegExp(`^[ ]*(?:input|output|inout)?[ ]*(\\w+).*?${signalName}`, "gm")));
    let signalTypeName = matchAll[0][1] //[0] get first occurance of the signal, [1] get the (match)
	return signalTypeName
}

//----------------------------------------------------------------------------
function getStructList(str) {
	// 'struct' with or without 'packed' { * } 'word';
	let structList = []
    const matchAll = Array.from(str.matchAll(/struct(?:\s+packed)?\s*{[\S\s]*?}\s*\w+\s*;/gm));
    if (matchAll) {
        structList = matchAll.map(x => x[0])
	}
	return structList
}

//----------------------------------------------------------------------------
function getStructName(str) {
	return str.match(/}\s*(\w+)\s*;$/m)[1]
}

//----------------------------------------------------------------------------
function getStructMemberName(str) {
	let structMemberName = []
    const matchAll = Array.from(str.matchAll(/(\w+)\s*;/g));
    if (matchAll)
        structMemberName = matchAll.map(x => x[1]).slice(0, -1) // get the (match) [1], throw last match (-1)
	return structMemberName
}

//----------------------------------------------------------------------------
function getStructInFile(structName, filePath) {
	//const struct_list =  text.match(/^[ ]*\w*[ ]*struct+[\s\S]*?}[\s\S]*?;$/gm)
	let text = fs.readFileSync(filePath, 'utf8');
	const struct_list =  getStructList(text)

	for (let struct of struct_list) {
		console.log(`Scanning struct '${struct}'`)
		if(getStructName(struct) == structName) {
			console.log(`Found struct`)
			const completionList = [];
			for (let structMember of getStructMemberName(struct)) {
				console.log(`Found member ${structMember}`)
				completionList.push(new vscode.CompletionItem(structMember))
			}
			return completionList
		}
	}
}
//----------------------------------------------------------------------------
function getImportName (text) {
    const matchAll = Array.from(text.matchAll(/^\s*import\s*?(.*);$/gm));
    let groupMatch = matchAll.slice(0, -1).map(x => x[1])
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
	console.log(`Searching struct in '${filePath}'`)
	let returnFromFile = getStructInFile(structName, filePath)
	if (returnFromFile) {
		return returnFromFile
	}
	let text = fs.readFileSync(filePath, 'utf8');
	let importFileNameList = getImportName(text)
	for (let importFileName of importFileNameList) {
		console.log(`Checking import '${importFileName}'`)
		let path = await getFilePath(importFileName)
		let returnValue = getStruct(structName, path)
		if (returnValue) {
			return returnValue
		}
	}
	console.log(`Cant find '${structName}'`)
}
//----------------------------------------------------------------------------
function wordIsReserved(word) {
    return word.match(new RegExp("\\b("+
        "accept_on|alias|always|always_comb|always_ff|always_latch|and|assert|assign"+
        "|assume|automatic|before|begin|bind|bins|binsof|bit|break|buf|bufif0|bufif1"+
        "|byte|case|casex|casez|cell|chandle|checker|class|clocking|cmos|config|const"+
        "|constraint|context|continue|cover|covergroup|coverpoint|cross|deassign|default"+
        "|defparam|design|disable|dist|do|edge|else|end|endcase|endchecker|endclass|endclocking"+
        "|endconfig|endfunction|endgenerate|endgroup|endinterface|endmodule|endpackage|endprimitive"+
        "|endprogram|endproperty|endspecify|endsequence|endtable|endtask|enum|event|eventually"+
        "|expect|export|extends|extern|final|first_match|for|force|foreach|forever|fork|forkjoin"+
        "|function|generate|genvar|global|highz0|highz1|if|iff|ifnone|ignore_bins|illegal_bins"+
        "|implements|implies|import|incdir|include|initial|inout|input|inside|instance|int|integer"+
        "|interconnect|interface|intersect|join|join_any|join_none|large|let|liblist|library|local"+
        "|localparam|logic|longint|macromodule|matches|medium|modport|module|nand|negedge|nettype"+
        "|new|nexttime|nmos|nor|noshowcancelled|not|notif0|notif1|null|or|output|package|packed"+
        "|parameter|pmos|posedge|primitive|priority|program|property|protected|pull0|pull1|pulldown"+
        "|pullup|pulsestyle_ondetect|pulsestyle_onevent|pure|rand|randc|randcase|randsequence"+
        "|rcmos|real|realtime|ref|reg|reject_on|release|repeat|restrict|return|rnmos|rpmos|rtran"+
        "|rtranif0|rtranif1|s_always|s_eventually|s_nexttime|s_until|s_until_with|scalared|sequence"+
        "|shortint|shortreal|showcancelled|signed|small|soft|solve|specify|specparam|static|string"+
        "|strong|strong0|strong1|struct|super|supply0|supply1|sync_accept_on|sync_reject_on|table"+
        "|tagged|task|this|throughout|time|timeprecision|timeunit|tran|tranif0|tranif1|tri|tri0|tri1"+
        "|triand|trior|trireg|type|typedef|union|unique|unique0|unsigned|until|until_with|untyped|use"+
        "|uwire|var|vectored|virtual|void|wait|wait_order|wand|weak|weak0|weak1|while|wildcard|wire|with"+
        "|within|wor|xnor|xor)\\b"))
}
//----------------------------------------------------------------------------
function flashLine(position) {
    let decoration = vscode.window.createTextEditorDecorationType({color: "#2196f3", backgroundColor: "#ffeb3b"})
    let rangeOption = {range: new vscode.Range(new vscode.Position(position.line, 0), new vscode.Position(position.line, 999))}
    vscode.window.activeTextEditor.setDecorations(decoration, [rangeOption])
    setTimeout(()=>{decoration.dispose()}, 2000)
}
//----------------------------------------------------------------------------

async function activate(context) {
    context.subscriptions.push(vscode.languages.registerCompletionItemProvider(
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
    ));

	//----------------------------------------------------------------------------
	async function provideDefinition(document, position, token) {
		console.log("CTRL")

        const word = document.getText(document.getWordRangeAtPosition(position))
        if(wordIsReserved(word)) {
            console.log("Reserved word!")
            return
        }
		const line = document.lineAt(position).text

        // is this a module / function
        if(line.match(new RegExp(`^\\s*${word}\\s*#?\\s*\\(`, "g"))) {
			console.log(`Searching entity: ${word}`)
			const path = await getFilePath(word)
			console.log(`FilePath for entity= ${path}`)
			if(path) return new vscode.Location(vscode.Uri.file(path), new vscode.Position(0, 0));
		}
        // is this import
		if (line.match(/^\s*import\s\w+::/)) {
			console.log(`Searching package: ${word}`)
			const path = await getFilePath(word)
			console.log(`FilePath for package= ${path}`)
			if(path) return new vscode.Location(vscode.Uri.file(path), new vscode.Position(0, 0));
		}
        // is this word
        console.log(`Search for 1er line of ${word}`);
        let text = document.getText()
        let matchAll = Array.from(text.matchAll(new RegExp(`.*${word}`, "g")))
        let firstLinePostition = document.positionAt(matchAll[0].index)
        if(!firstLinePostition.isEqual(new vscode.Position(position.line, 0))) {
            console.log("go to !");
            flashLine(firstLinePostition)
            return new vscode.Location(document.uri, firstLinePostition);
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
