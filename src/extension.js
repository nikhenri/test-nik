console.log('Entering extension.js...')

const vscode = require('vscode')
const fs = require('fs')

const utils = require('./utils')
const definition = require('./definition')

//----------------------------------------------------------------------------
const activate = utils.tryCatch((context) => {
    context.subscriptions.push([
		vscode.languages.registerCompletionItemProvider('systemverilog', {provideCompletionItems}, '.'),
		vscode.languages.registerDefinitionProvider('systemverilog', {provideDefinition: definition.provideDefinition}),
		vscode.window.registerTerminalLinkProvider({provideTerminalLinks, handleTerminalLink})
	])
})

//----------------------------------------------------------------------------
//----------------------------------------------------------------------------
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

const getFullSignalName = utils.tryCatch((fullLine) => {
	let match = fullLine.match(/[\w\.\[\]]+\.$/g) // start with a letter, followed by any nb of caracter
	if(match) {
		return (match[0].slice(0, -1).split("["))[0]
	}
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
		// console.log(`Scanning struct '${struct}'`)
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
// @TODO need to add an object of 'scanned' to avoid recursive scan
const getStruct = async (structName, filePath) => {
	let filePathToFileNameWithoutExt = utils.filePathToFileNameWithoutExt(filePath)
	console.log(`Searching struct in '${filePathToFileNameWithoutExt}'`)
	let returnFromFile = getStructInFile(structName, filePath)
	if (returnFromFile) {
		return returnFromFile
	}
	let text = fs.readFileSync(filePath, 'utf8')
	let importFileNameList = utils.getImportNameList(text)
	for (let importFileName of importFileNameList) {

		if(filePathToFileNameWithoutExt != importFileName) {
			console.log(`Checking import '${importFileName}'`)
			let path = await utils.getFilePath(importFileName)
			let returnValue = await getStruct(structName, path)
			if (returnValue) {
				return returnValue
			}
		}
	}
	console.log(`Cant find '${structName}'`)
}

//----------------------------------------------------------------------------
//----------------------------------------------------------------------------
//----------------------------------------------------------------------------
const provideTerminalLinks = utils.tryCatch((context, token) => {
    console.log(`Terminal line: ${context.line}`)
	// #    Time: 0 fs  Iteration: 0  Instance: /tcp_dma_tb/DUT/qmngr_top/local_pointers_if File: C:/src/queue_manager/src/qmngr_top.sv Line: 451
	let matchArray = Array.from(context.line.matchAll(new RegExp(`([^ ]+) Line: (\\d+)`, "g")))
	if (matchArray.length) {
		return [{startIndex: matchArray[0].index,
			     length: matchArray[0][0].length, // + " Line: "
				 uri: vscode.Uri.file(matchArray[0][1]),
				 line: matchArray[0][2]}]
	}
})
//----------------------------------------------------------------------------
const handleTerminalLink = utils.tryCatch((link) => {
    console.log(`link: ${JSON.stringify(link)}`)
	let pos = new vscode.Position(parseInt(link.line) - 1, 0)
    vscode.workspace.openTextDocument(link.uri)
	.then((doc) => vscode.window.showTextDocument(doc, {selection: new vscode.Range(pos, pos)}))
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


//----------------------------------------------------------------------------
// const getTextAfterPosition = utils.tryCatch((document, position) => {
// 	return document.getText().substring(document.offsetAt(position))
// })
//----------------------------------------------------------------------------
// const indexToPositionStartOfLine = utils.tryCatch((document, index) => {
// 	return new vscode.Position(document.positionAt(index).line, 0)
// })