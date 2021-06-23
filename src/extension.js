console.log('Entering extension.js...')

const vscode = require('vscode')
const fs = require('fs')
const utils = require('./utils')
const regexp = require('./regexp')

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
const flashLine = utils.tryCatch((position) => {
    let decoration = vscode.window.createTextEditorDecorationType({color: "#2196f3", backgroundColor: "#ffeb3b"})
    let rangeOption = {range: new vscode.Range(new vscode.Position(position.line, 0), new vscode.Position(position.line, 999))}
    vscode.window.activeTextEditor.setDecorations(decoration, [rangeOption])
    setTimeout(()=>{decoration.dispose()}, 2000)
})
//----------------------------------------------------------------------------
// const getTextAfterPosition = utils.tryCatch((document, position) => {
// 	return document.getText().substring(document.offsetAt(position))
// })



//----------------------------------------------------------------------------
const getModuleLocation  = async (name) => {
	console.log(`Searching entity: ${name}`)
	let path = await utils.getFilePath(name)
	console.log(`FilePath for entity= ${path}`)
	if(path) return new vscode.Location(vscode.Uri.file(path), new vscode.Position(0, 0))
	console.log(`Can't found entity: ${name}`)
}

//----------------------------------------------------------------------------
const getFunctionIndex = utils.tryCatch((text, name) => {
    let matchAll = Array.from(text.matchAll(new RegExp(`^[ ]*function\\s+.*?${name}\\s*\\(`, "gm")))
    if (matchAll.length) return matchAll[0].index
})

//----------------------------------------------------------------------------
const indexToPositionStartOfLine = utils.tryCatch((document, index) => {
	return new vscode.Position(document.positionAt(index).line, 0)
})

//----------------------------------------------------------------------------
const getFunctionLocation = async (document, textt, name) => {

	console.log(`Searching function: ${name}`)

	let fileNameWithoutExt = utils.uriToFileNameWithoutExt(document.uri)
	let {text, path} = await utils.getFileText(fileNameWithoutExt)
	let scanLileNameWithoutExtList = [fileNameWithoutExt, ...regexp.getImportNameList(text)]
	for (let scanLileNameWithoutExt of scanLileNameWithoutExtList) {
		console.log(`Scanning ${scanLileNameWithoutExt}`)
		let {text, path} = await utils.getFileText(scanLileNameWithoutExt)
		let functionIndex = getFunctionIndex(text, name)
		if(functionIndex) {
			let position = utils.indexToPosition(text, functionIndex)
			console.log(`Found match in ${path}, line: ${position.line}, char: ${position.character}`)
			return new vscode.Location(vscode.Uri.file(path), position)
		}
	}
	console.log(`Can't found function: ${name}`)
}

//----------------------------------------------------------------------------
const getTypeLocation = async (document, text, name) => {
	console.log(`Searching type: ${name}`)
	let typeIndex = getTypeIndex(text, name)
	if(typeIndex) return new vscode.Location(document.uri, indexToPositionStartOfLine(document, typeIndex))
	let importFileNameList = getImportName(text)
	for (let importFileName of importFileNameList) {
		console.log(`Checking import '${importFileName}'`)
		let filePath = await utils.getFilePath(importFileName)
		let textImport = fs.readFileSync(filePath, 'utf8')
		typeIndex = getTypeIndex(textImport, name)
		let lineNumber = textImport.substr(0, typeIndex).split(/\r\n|\n/).length - 1
		setTimeout(()=>{flashLine(new vscode.Position(lineNumber, 0))}, 100)
		if(typeIndex) return new vscode.Location(vscode.Uri.file(filePath), new vscode.Position(lineNumber, 0))
	}
	console.log(`Can't found type: ${name}`)
}
//----------------------------------------------------------------------------
const getInstanceLocation = async (document, text, name) => {
	console.log(`Searching instance: ${name}`)
	let filePathList = await utils.getFilePath()
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
}
//----------------------------------------------------------------------------
const getTypeIndex = utils.tryCatch((text, name) => {
    let matchAll = Array.from(text.matchAll(new RegExp(`^[ ]*typedef\\s+[^}]*?}\\s*${name}\\s*;`, "gm")))
    if (matchAll.length) return matchAll[0].index
})

//----------------------------------------------------------------------------
const provideDefinition = async (document, position, token) => {
	console.log("CTRL")
	utils.getFileText()

	let word = document.getText(document.getWordRangeAtPosition(position))
	if(regexp.wordIsNumber(word) || regexp.wordIsReserved(word)) return
	// console.log(`Word: ${word}`)

	// @ TODO
	let lineOfWordAndTextAfter = document.getText().substring(document.offsetAt(new vscode.Position(position.line, 0)))

	// is this a module
	if(regexp.isInstance(lineOfWordAndTextAfter, word)) {
		let moduleLocation = getModuleLocation(word)
		if(moduleLocation) return moduleLocation
	}

	if(regexp.isFunction(lineOfWordAndTextAfter, word)) {
		let functionLocation = await getFunctionLocation(document, document.getText(), word)
		if(functionLocation) return functionLocation
	}

	if(regexp.isTypedef(lineOfWordAndTextAfter, word)) {
		let typeLocation = await getTypeLocation(document, document.getText(), word)
		if(typeLocation) return typeLocation
	}

	if(regexp.isModule(lineOfWordAndTextAfter, word)) {
		let instanceLocation = await getInstanceLocation(document, document.getText(), word)
		if(instanceLocation) return instanceLocation
	}
	// is this import
	if (regexp.isImport(lineOfWordAndTextAfter, word)) {
		console.log(`Searching package: ${word}`)
		let path = await utils.getFilePath(word)
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
    let subscriptions = [
                        vscode.languages.registerCompletionItemProvider('systemverilog', {provideCompletionItems}, '.'),
						vscode.languages.registerDefinitionProvider('systemverilog', {provideDefinition}),
                        vscode.window.registerTerminalLinkProvider({provideTerminalLinks, handleTerminalLink})
                        ]
    context.subscriptions.push(subscriptions )
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