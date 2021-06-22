const vscode = require('vscode')
const fs = require('fs')
const path = require('path')

console.log('Entering extension.js...')

//----------------------------------------------------------------------------
const tryCatch = (func) => {
	return (...restArgs) => {
		try{
			return func(...restArgs)
		} catch (error) {
			console.error(`>> CATCH:\n${error}`)
			throw("Fuck off")
		}
	}
}
//----------------------------------------------------------------------------
const removeCommentedLine = tryCatch((text) => {
	return text.replace(/\/\*[\s\S]*?\*\/|\/\/.*/g, (match) => {
		return " ".repeat(match.length)
	})
})


//----------------------------------------------------------------------------
const getFilePath = tryCatch(async (fileNameWithoutExt)=> {
	let filePath
	let search_fileNameWithoutExt = (x=> path.parse(x).name == fileNameWithoutExt)
	if(!getFilePath.listOfPath || !fileNameWithoutExt || !(filePath = getFilePath.listOfPath.find(search_fileNameWithoutExt))) {
		console.log("Updating findFiles...")
        getFilePath.listOfPath = (await vscode.workspace.findFiles("**/*.*v")).map(x => x.fsPath)
		if (!fileNameWithoutExt)
			filePath = getFilePath.listOfPath
		else
		filePath = getFilePath.listOfPath.find(search_fileNameWithoutExt)
    }
		if(!filePath) console.log(`Was not able to found '${fileNameWithoutExt}'`)
	return filePath
})

//----------------------------------------------------------------------------
// const getFileText = tryCatch(async (fileNameWithoutExt) => {
// 	let path = await getFilePath(fileNameWithoutExt)
// 	console.log(`Reading '${path}'`)
// 	return fs.readFileSync(path, 'utf8')
// })

//----------------------------------------------------------------------------
const getFullSignalName = tryCatch((fullLine) => {
	let match = fullLine.match(/[\w\.]+\w*\.$/g) // start with a letter, followed by any nb of caracter
	if(match) {
		return match[0].slice(0, -1)}
})

//----------------------------------------------------------------------------
const getSignalTypeName = tryCatch((str, signalName) => {
	// first word that is not input | output | inout
    let matchAll = Array.from(str.matchAll(new RegExp(`^[ ]*(?:input|output|inout)?[ ]*(\\w+).*?${signalName}`, "gm")))
    let signalTypeName = matchAll[0][1] //[0] get first occurance of the signal, [1] get the (match)
	return signalTypeName
})

//----------------------------------------------------------------------------
const getStructList = tryCatch((str) => {
	// 'struct' with or without 'packed' { * } 'word';
	let structList = []
    let matchAll = Array.from(str.matchAll(/struct(?:\s+packed)?\s*{[\S\s]*?}\s*\w+\s*;/gm))
    if (matchAll.length) {
        structList = matchAll.map(x => x[0])
	}
	return structList
})

//----------------------------------------------------------------------------
const getStructName = tryCatch((str) => {
	return str.match(/}\s*(\w+)\s*;/)[1]
})

//----------------------------------------------------------------------------
const getStructMemberName = tryCatch((str) => {
	let structMemberName = []
    let matchAll = Array.from(str.matchAll(/(\w+)\s*;/g))
    if (matchAll.length)
        structMemberName = matchAll.map(x => x[1]).slice(0, -1) // get the (match) [1], throw last match (-1)
	return structMemberName
})

//----------------------------------------------------------------------------
const getStructInFile = tryCatch((structName, filePath) => {
	let text = fs.readFileSync(filePath, 'utf8')
	let struct_list =  getStructList(text)

	for (let struct of struct_list) {
		console.log(`Scanning struct '${struct}'`)
		if(getStructName(struct) == structName) {
			console.log(`Found struct`)
			let completionList = []
			for (let structMember of getStructMemberName(struct)) {
				console.log(`Found member ${structMember}`)
				completionList.push(new vscode.CompletionItem(structMember))
			}
			return completionList
		}
	}
})

//----------------------------------------------------------------------------
const getImportName = tryCatch((text) => {
    let matchAll = Array.from(text.matchAll(/^\s*import\s*?(.*);$/gm))
    let groupMatch = matchAll.map(x => x[1])
	let ImportNameList = []
	for (let match of groupMatch) {
		for (let packageStr of match.split(",")) {
			let packageName = packageStr.trim().split("::")[0]
			console.log(`Found package ${packageName}`)
			ImportNameList.push(packageName)
		}
	}
	return ImportNameList
})

//----------------------------------------------------------------------------
const getStruct = tryCatch(async (structName, filePath) => {
	console.log(`Searching struct in '${filePath}'`)
	let returnFromFile = getStructInFile(structName, filePath)
	if (returnFromFile) {
		return returnFromFile
	}
	let text = fs.readFileSync(filePath, 'utf8')
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
})

//----------------------------------------------------------------------------
const wordIsReserved = tryCatch((word) => {
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
})
//----------------------------------------------------------------------------
const flashLine = tryCatch((position) => {
    let decoration = vscode.window.createTextEditorDecorationType({color: "#2196f3", backgroundColor: "#ffeb3b"})
    let rangeOption = {range: new vscode.Range(new vscode.Position(position.line, 0), new vscode.Position(position.line, 999))}
    vscode.window.activeTextEditor.setDecorations(decoration, [rangeOption])
    setTimeout(()=>{decoration.dispose()}, 2000)
})
//----------------------------------------------------------------------------
const getTextAfterPosition = tryCatch((document, position) => {
	return document.getText().substring(document.offsetAt(position))
})

//----------------------------------------------------------------------------
const isInstance = tryCatch((text, name) => {
    let matchAll = Array.from(text.matchAll(new RegExp(`^[ ]*${name}\\s*(?:#\\s*\\([\\s\\S]*?\\)\\s*)?\\w+\\s*\\([\\s\\S]+?\\)\\s*;`, "gm")))
	if (matchAll.length) return matchAll
})

//----------------------------------------------------------------------------
const isFunction = tryCatch((text, name) => {
	return text.match(new RegExp(`[\\.| ]+${name}\\s*\\([\\S\\s]*?\\)`))
})

//----------------------------------------------------------------------------
const isTypedef = tryCatch((text, name) => {
	return text.match(new RegExp(`^\\s*(?:input\\s+|output\\s+|inout\\s+)?${name}(?:\\s*\\[.*?\\])*\\s+\\w+`))
})
//----------------------------------------------------------------------------
const isModule = tryCatch((text, name) => {
	return text.match(new RegExp(`^\\s*module\\s+${name}`))
})
//----------------------------------------------------------------------------
const isImport = tryCatch((text, name) => {
	return text.match(new RegExp(`^\\s*import\\s*(?:.*\\s*,\\s*)*${name}::`))
})

//----------------------------------------------------------------------------
const getModuleLocation  = tryCatch(async (name) => {
	console.log(`Searching entity: ${name}`)
	let path = await getFilePath(name)
	console.log(`FilePath for entity= ${path}`)
	if(path) return new vscode.Location(vscode.Uri.file(path), new vscode.Position(0, 0))
	console.log(`Can't found entity: ${name}`)
})

//----------------------------------------------------------------------------
const getFunctionIndex = tryCatch((text, name) => {
    let matchAll = Array.from(text.matchAll(new RegExp(`^[ ]*function\\s+.*?${name}\\s*\\(`, "gm")))
    if (matchAll.length) return matchAll[0].index
})

//----------------------------------------------------------------------------
const indexToPositionStartOfLine = tryCatch((document, index) => {
	return new vscode.Position(document.positionAt(index).line, 0)
})

//----------------------------------------------------------------------------
const getFunctionLocation = tryCatch(async (document, text, name) => {
	console.log(`Searching function: ${name}`)
	let functionIndex = getFunctionIndex(text, name)
	if(functionIndex) return new vscode.Location(document.uri, indexToPositionStartOfLine(document, functionIndex))
	let importFileNameList = getImportName(text)
	for (let importFileName of importFileNameList) {
		console.log(`Checking import '${importFileName}'`)
		let filePath = await getFilePath(importFileName)
		let textImport = fs.readFileSync(filePath, 'utf8')
		functionIndex = getFunctionIndex(textImport, name)
		let lineNumber = textImport.substr(0, functionIndex).split(/\r\n|\n/).length - 1
		setTimeout(()=>{flashLine(new vscode.Position(lineNumber, 0))}, 100)
		if(functionIndex) return new vscode.Location(vscode.Uri.file(filePath), new vscode.Position(lineNumber, 0))
	}
	console.log(`Can't found function: ${name}`)
})

//----------------------------------------------------------------------------
const getTypeLocation = tryCatch(async (document, text, name) => {
	console.log(`Searching type: ${name}`)
	let typeIndex = getTypeIndex(text, name)
	if(typeIndex) return new vscode.Location(document.uri, indexToPositionStartOfLine(document, typeIndex))
	let importFileNameList = getImportName(text)
	for (let importFileName of importFileNameList) {
		console.log(`Checking import '${importFileName}'`)
		let filePath = await getFilePath(importFileName)
		let textImport = fs.readFileSync(filePath, 'utf8')
		typeIndex = getTypeIndex(textImport, name)
		let lineNumber = textImport.substr(0, typeIndex).split(/\r\n|\n/).length - 1
		setTimeout(()=>{flashLine(new vscode.Position(lineNumber, 0))}, 100)
		if(typeIndex) return new vscode.Location(vscode.Uri.file(filePath), new vscode.Position(lineNumber, 0))
	}
	console.log(`Can't found type: ${name}`)
})
//----------------------------------------------------------------------------
const getInstanceLocation = tryCatch(async (document, text, name) => {
	console.log(`Searching instance: ${name}`)
	let filePathList = await getFilePath()
	let locationList = []
	for (let filePath of filePathList) {
		let text = fs.readFileSync(filePath, 'utf8')
		let instanceList = isInstance(text, name)
		if (isInstance(text, name)) {
			for (let instance of instanceList) {
				let lineNumber = text.substr(0, instance.index).split(/\r\n|\n/).length - 1
				locationList.push(new vscode.Location(vscode.Uri.file(filePath), new vscode.Position(lineNumber, 0)))
			}
		}
	}
	if(locationList.length) {
		return locationList
	}
	console.log(`Can't found instance: ${name}`)
})
//----------------------------------------------------------------------------
const getTypeIndex = tryCatch((text, name) => {
    let matchAll = Array.from(text.matchAll(new RegExp(`^[ ]*typedef\\s+[^}]*?}\\s*${name}\\s*;`, "gm")))
    if (matchAll.length) return matchAll[0].index
})

//----------------------------------------------------------------------------
const provideDefinition = tryCatch(async (document, position, token) => {
	console.log("CTRL")
	let word = document.getText(document.getWordRangeAtPosition(position))
	if(wordIsReserved(word)) {
		console.log("Reserved word!")
		return
	}
	let line = document.lineAt(position).text

	let textAfterStartOfLine = getTextAfterPosition(document, new vscode.Position(position.line, 0))

	// is this a module
	if(isInstance(textAfterStartOfLine, word)) {
		// check for entity
		let moduleLocation = getModuleLocation(word)
		if(moduleLocation) return moduleLocation
	}

	if(isFunction(textAfterStartOfLine, word)) {
		// let functionLocation = getFunctionLocation(document, removeCommentedLine(document.getText()), word)
		let functionLocation = await getFunctionLocation(document, document.getText(), word)
		if(functionLocation) return functionLocation
	}

	if(isTypedef(textAfterStartOfLine, word)) {
		let typeLocation = await getTypeLocation(document, document.getText(), word)
		if(typeLocation) return typeLocation
	}

	if(isModule(textAfterStartOfLine, word)) {
		let instanceLocation = await getInstanceLocation(document, document.getText(), word)
		if(instanceLocation) return instanceLocation
	}
	// is this import
	if (isImport(line, word)) {
		console.log(`Searching package: ${word}`)
		let path = await getFilePath(word)
		console.log(`FilePath for package= ${path}`)
		if(path) return new vscode.Location(vscode.Uri.file(path), new vscode.Position(0, 0))
	}
	// is this word
	console.log(`Search for 1er line of ${word}`)
	let text = document.getText()
	let matchAll = Array.from(text.matchAll(new RegExp(`.*${word}`, "g")))
	let firstLinePostition = document.positionAt(matchAll[0].index)
	if(!firstLinePostition.isEqual(new vscode.Position(position.line, 0))) {
		console.log("go to !")
		flashLine(firstLinePostition)
		return new vscode.Location(document.uri, firstLinePostition)
	}
	console.log("Found nothing")
})

//----------------------------------------------------------------------------
const provideCompletionItems = tryCatch((document, position) => {
	console.log(".")
	let linePrefix = document.lineAt(position).text.substr(0, position.character)
	if (!linePrefix.endsWith('.')) return

	let fullSignalName = getFullSignalName(linePrefix)
	if(fullSignalName) {
		console.log(`searching for variable '${fullSignalName}'`)
		if(fullSignalName.split('.').length > 1) {
			console.log(`Dont support multi-member, exiting`)
			return
		}

		let text = document.getText()

		let declaration_type = getSignalTypeName(text, fullSignalName)
		console.log(`Type is '${declaration_type}'`)
		return getStruct(declaration_type, document.fileName)
	}
})
//----------------------------------------------------------------------------
const activate = tryCatch((context) => {
    context.subscriptions.push(vscode.languages.registerCompletionItemProvider('systemverilog', {provideCompletionItems}, '.'),
							   vscode.languages.registerDefinitionProvider(['systemverilog'], {provideDefinition}),

							   vscode.window.registerTerminalLinkProvider({
								    provideTerminalLinks:  (context, token) => {
										const startIndex = context.line.indexOf('help');
										if (startIndex === -1) return []
                                        console.log(`context.line >> ${context.line}`)
										return [{startIndex: startIndex, length: 'link'.length}]
									},
									 handleTerminalLink: async (link) => {
                                        console.log(`link >> ${JSON.stringify(link)}`)
                                        vscode.workspace.openTextDocument(vscode.Uri.file('C://Users//nhenri//Desktop//tcp_ip_ip_vs_code_ext//src//common//pkg//qmngr_pkg.sv'))
                                        vscode.window.showTextDocument(doc)
								    }
							})
	 )
})
//----------------------------------------------------------------------------

// this method is called when your extension is deactivated
const deactivate = tryCatch(() => {})

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

//		let fileName = document.fileName
// let workDir = path.dirname(fileName)

/*
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
		vscode.window.showInformationMessage('Hello World from test Nik!')
	}).
*/

/*
	const getAss = tryCatch((cnt, cnt2) => {
		console.log("woof " + cnt + ", " + cnt2)
		//throw "is too low"
		return 3
	})
	//----------------------------------------------------------------------------

	console.log(">> getAss: " +getAss(7, 2))
*/

/*
		let doc = await vscode.workspace.openTextDocument(vscode.Uri.file(filePath))
		let g = doc.positionAt(functionIndex)
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