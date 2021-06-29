const vscode = require('vscode')
const fs = require('fs')
const utils = require('./utils')

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
module.exports = {
	provideCompletionItems,
}