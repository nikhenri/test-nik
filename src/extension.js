console.log('Entering extension.js...')

const vscode = require('vscode')
const fs = require('fs')
const utils = require('./utils')
const regexp = require('./regexp')
const path = require('path')

//----------------------------------------------------------------------------
const getFullSignalName = utils.tryCatch((fullLine) => {
	let match = fullLine.match(/[\w\.]+\w*\.$/g) // start with a letter, followed by any nb of caracter
	if(match) {
		return match[0].slice(0, -1)}
})

//----------------------------------------------------------------------------
const getSignalTypeName = utils.tryCatch((str, signalName) => {
	// first word that is not input | output | inout
    let matchAll = Array.from(str.matchAll(new RegExp(`^[ ]*(?:input|output|inout)?[ ]*(\\w+).*?${signalName}`, "gm")))
    let signalTypeName = matchAll[0][1] //[0] get first occurance of the signal, [1] get the (match)
	return signalTypeName
})

//----------------------------------------------------------------------------
const getStructList = utils.tryCatch((str) => {
	// 'struct' with or without 'packed' { * } 'word';
	let structList = []
    let matchAll = Array.from(str.matchAll(/struct(?:\s+packed)?\s*{[\S\s]*?}\s*\w+\s*;/gm))
    if (matchAll.length) {
        structList = matchAll.map(x => x[0])
	}
	return structList
})

//----------------------------------------------------------------------------
const getStructName = utils.tryCatch((str) => {
	return str.match(/}\s*(\w+)\s*;/)[1]
})

//----------------------------------------------------------------------------
const getStructMemberName = utils.tryCatch((str) => {
	let structMemberName = []
    let matchAll = Array.from(str.matchAll(/(\w+)\s*;/g))
    if (matchAll.length)
        structMemberName = matchAll.map(x => x[1]).slice(0, -1) // get the (match) [1], throw last match (-1)
	return structMemberName
})

//----------------------------------------------------------------------------
const getStructInFile = utils.tryCatch((structName, filePath) => {
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


//----------------------------------------------------------------------------
const getStruct = async (structName, filePath) => {
	console.log(`Searching struct in '${filePath}'`)
	let returnFromFile = getStructInFile(structName, filePath)
	if (returnFromFile) {
		return returnFromFile
	}
	let text = fs.readFileSync(filePath, 'utf8')
	let importFileNameList = getImportName(text)
	for (let importFileName of importFileNameList) {
		console.log(`Checking import '${importFileName}'`)
		let path = await utils.getFilePath(importFileName)
		let returnValue = getStruct(structName, path)
		if (returnValue) {
			return returnValue
		}
	}
	console.log(`Cant find '${structName}'`)
}

//----------------------------------------------------------------------------

//----------------------------------------------------------------------------
const flashLine = utils.tryCatch((line) => {
	let event = vscode.window.onDidChangeTextEditorSelection(() => {
		setTimeout(()=>{
			let decoration = vscode.window.createTextEditorDecorationType({color: "#2196f3", backgroundColor: "#ffeb3b"})
			let rangeOption = {range: new vscode.Range(new vscode.Position(line, 0), new vscode.Position(line, 999))}
			vscode.window.activeTextEditor.setDecorations(decoration, [rangeOption])
			setTimeout(()=>{decoration.dispose()}, 1500)
		}, 100)
		event.dispose()
	})
})
//----------------------------------------------------------------------------
// const getTextAfterPosition = utils.tryCatch((document, position) => {
// 	return document.getText().substring(document.offsetAt(position))
// })
//----------------------------------------------------------------------------
// const indexToPositionStartOfLine = utils.tryCatch((document, index) => {
// 	return new vscode.Position(document.positionAt(index).line, 0)
// })

//----------------------------------------------------------------------------
const getLocation = async (fileNameWithoutExt, funcMatch) => {
	// check current file
	let matchInFileObj = await getMatchInFile(fileNameWithoutExt, funcMatch)

	if(!matchInFileObj)
		matchInFileObj = await getMatchInImport(fileNameWithoutExt, funcMatch)

	if(matchInFileObj) {
		let position = utils.indexToPosition(matchInFileObj.text, matchInFileObj.match[0].index)
		console.log(`Found match in ${matchInFileObj.path}, line: ${position.line}, char: ${position.character}`)
		return new vscode.Location(vscode.Uri.file(matchInFileObj.path), position)
	}
}
//----------------------------------------------------------------------------
// get: nameFile, name, matchFunction
// return Object:
// .path = file path
// .text = fileText
// .match = MatchAll object from regEx
const getMatchInImport = async (fileNameWithoutExt, funcMatch) => {
	let fileTextObj = await utils.getFileText(fileNameWithoutExt)
	for (let importfileNameWithoutExt of getImportNameList(fileTextObj.text)) {
		let matchInFileObj = await getMatchInFile(importfileNameWithoutExt, funcMatch)
		if(matchInFileObj) return matchInFileObj
	}
}
//----------------------------------------------------------------------------
// get: nameFile, name, matchFunction
// .path = file path
// .text = fileText
// .match = MatchAll object from regEx
const getMatchInFile = async (fileNameWithoutExt, funcMatch) => {
	//console.log(`Scanning ${fileNameWithoutExt}`)
	let fileTextObj = await utils.getFileText(fileNameWithoutExt)
	fileTextObj.match = funcMatch(fileTextObj.text)
	if(fileTextObj.match.length)
		return fileTextObj
}
//----------------------------------------------------------------------------
const getImportNameList = utils.tryCatch((text) => {
	let matchAll = Array.from(text.matchAll(/^\s*import\s*?(.*);$/gm))
	let groupMatch = matchAll.map(x => x[1])
	let ImportNameList = []
	for (let match of groupMatch) {
		for (let packageStr of match.split(",")) {
			let packageName = packageStr.trim().split("::")[0]
			// console.log(`Found package ${packageName}`)
			ImportNameList.push(packageName)
		}
	}
	return ImportNameList
})
//----------------------------------------------------------------------------
const getMatchInAllFile = async (name, funcMatch) => {
	let filePathList = await utils.getFilePath()
	let locationList = []
	for (let filePath of filePathList) {
		let matchInFileObj = await getMatchInFile(utils.filePathToFileNameWithoutExt(filePath), funcMatch)
		if(matchInFileObj) {
			for (let match of matchInFileObj.match) {
				let position = utils.indexToPosition(matchInFileObj.text, match.index)
				locationList.push(new vscode.Location(vscode.Uri.file(matchInFileObj.path), position))
			}
		}
	}
	if(locationList.length) {
		return locationList
	}
	console.log(`Can't found instance: ${name}`)
}

//----------------------------------------------------------------------------
const provideDefinition = async (document, position, token) => {
	console.log("CTRL")
	utils.getFileText() // init

	let location = await searchLocation(document, position)
	if(location) {
		if(!Array.isArray(location)) flashLine(location.range.start.line)
		return location
	}
	
	console.log("Found nothing")
}

//----------------------------------------------------------------------------
const searchLocation = async (document, position) => {
	let word = document.getText(document.getWordRangeAtPosition(position))
	if(regexp.wordIsNumber(word) || regexp.wordIsReserved(word)) return
	// console.log(`Word: ${word}`)

	let lineOfWordAndTextAfter = document.getText().substring(document.offsetAt(new vscode.Position(position.line, 0))) // @ TODO
	let fileNameWithoutExt = utils.uriToFileNameWithoutExt(document.uri)
	let location

	// Module instance ?
	if(regexp.isModuleInstance(lineOfWordAndTextAfter, word)) {
		console.log(`Searching module: ${word}`)
		location = getLocation(fileNameWithoutExt, (text) => {return regexp.getModuleMatch(text)})
		if(location) return location
	}
	// Function ?
	if(regexp.isFunction(lineOfWordAndTextAfter, word)) {
		console.log(`Searching function: ${word}`)
		location = await getLocation(fileNameWithoutExt, (text)=>{return regexp.getFunctionMatch(text, word)})
		if(location) return location
	}
	// Typedef (struct, enum) ?
	if(regexp.isTypedef(lineOfWordAndTextAfter, word)) {
		console.log(`Searching typeDef: ${word}`)
		location = await getLocation(fileNameWithoutExt, (text)=>{return regexp.getTypeMatch(text, word)})
		if(location) return location
	}
	// Module decalaration ?
	if(regexp.isModuleDeclaration(lineOfWordAndTextAfter, word)) {
		console.log(`Searching instance: ${word}`)
		location = await getMatchInAllFile(word, (text)=>{return regexp.getInstanceMatch(text, word)})
		if(location) return location
	}
	// Import ?
	if (regexp.isImport(lineOfWordAndTextAfter, word)) {
		console.log(`Searching package: ${word}`)
		location = await getLocation(fileNameWithoutExt, (text) => {return regexp.getPackageMatch(text)})
		if(location) return location
	}

	// is this word
	console.log(`Searching 1er line of ${word}`)
	location = await getLocation(fileNameWithoutExt, (text) => {return regexp.getWordOccuranceMatch(text, word)})

	return location
}
//----------------------------------------------------------------------------
const provideCompletionItems = utils.tryCatch((document, position) => {
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
const provideTerminalLinks = utils.tryCatch((context, token) => {
    const startIndex = context.line.indexOf('help');
    if (startIndex === -1) return []
    console.log(`context.line >> ${context.line}`)
    return [{startIndex: startIndex, length: 'link'.length}]
})
//----------------------------------------------------------------------------
const handleTerminalLink = utils.tryCatch((link) => {
    console.log(`link >> ${JSON.stringify(link)}`)
    vscode.workspace.openTextDocument(vscode.Uri.file('C://Users//nhenri//Desktop//tcp_ip_ip_vs_code_ext//src//common//pkg//qmngr_pkg.sv')).then(
        (doc) => vscode.window.showTextDocument(doc)
    )
})
//----------------------------------------------------------------------------
const activate = utils.tryCatch((context) => {
    context.subscriptions.push([
		vscode.languages.registerCompletionItemProvider('systemverilog', {provideCompletionItems}, '.'),
		vscode.languages.registerDefinitionProvider('systemverilog', {provideDefinition}),
		vscode.window.registerTerminalLinkProvider({provideTerminalLinks, handleTerminalLink})
	])
})
//----------------------------------------------------------------------------

// this method is called when your extension is deactivated
const deactivate = utils.tryCatch(() => {})

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
	const getAss = utils.tryCatch((cnt, cnt2) => {
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