const vscode = require('vscode')
const utils = require('./utils')

//----------------------------------------------------------------------------
const provideCompletionItems = async (document, position) => {
	console.log(".")
	utils.getFileText() // init

	let linePrefix = document.lineAt(position).text.substr(0, position.character)
	if (linePrefix.endsWith('.') && isStructAccess(linePrefix)) {

		let fileNameWithoutExt = utils.uriToFileNameWithoutExt(document.uri)
        let textToSearchTypeName = (await utils.getFileText(fileNameWithoutExt)).text
		let groupMatch = getStructSectionWithoutIndex(linePrefix)

		for (let signalName of groupMatch) {
			let structTypeName = getTypeName(textToSearchTypeName, signalName)
			if(utils.wordIsReserved(structTypeName)) return // logic toto;
			let structDeclaration = await searchStruct(structTypeName, fileNameWithoutExt)
            if(groupMatch[groupMatch.length-1] == signalName) { // last element
				let structMemberList = getStructMemberList(structDeclaration.struct)
                let completionList = structMemberList.map(x=>new vscode.CompletionItem(x))
                return completionList
            } else {
                textToSearchTypeName = structDeclaration.struct
                fileNameWithoutExt = structDeclaration.fileNameWithoutExt
            }
		}
	}
	console.log("Not able to Complete");
}

//----------------------------------------------------------------------------
const isStructAccess = utils.tryCatch((text) => {
	return text.match(/[\w\.\[\]]+\.$/g)
})
//----------------------------------------------------------------------------
const getStructSectionWithoutIndex = utils.tryCatch((text) => {
	let matchAll = Array.from(text.matchAll(/(\w+)(?:\[.*?\])?\./g))
	let groupMatch = matchAll.map(x => x[1])
	return groupMatch
})

//----------------------------------------------------------------------------
const getTypeName = utils.tryCatch((str, signalName) => {
	// first word that is not input | output | inout
    let matchAll = Array.from(str.matchAll(new RegExp(`^[ ]*(?:input|output|inout)?[ ]*(\\w+).*?${signalName}`, "gm")))
	if (matchAll.length) return matchAll[0][1] //[0] get first occurance of the signal, [1] get the (match)
})

//----------------------------------------------------------------------------
// @TODO need to add an object of 'scanned' to avoid recursive scan
const searchStruct = async (structTypeName, fileNameWithoutExt) => {
	// getMatchInFile
    let fileTextObj = await utils.getFileText(fileNameWithoutExt)
	let struct = searchStructInText(fileTextObj.text, structTypeName)
	// getMatchInFile

	if (struct) {
		return {struct, fileNameWithoutExt:fileNameWithoutExt}
	}
	let importFileNameList = utils.getImportNameList(fileTextObj.text)
	for (let importFileName of importFileNameList) {
		if(fileNameWithoutExt != importFileName) {
			console.log(`Checking import '${importFileName}'`)
			fileTextObj = await utils.getFileText(importFileName)
			struct = searchStructInText(fileTextObj.text, structTypeName)
			if (struct) {
				return {struct, fileNameWithoutExt:importFileName}
			}
		}
	}
	console.log(`Cant find '${structTypeName}'`)
}

//----------------------------------------------------------------------------
const searchStructInText = utils.tryCatch((text, structTypeName) => {
	let matchAll = Array.from(text.matchAll(new RegExp(`struct(?:\\s+packed)?\\s*{[^}]*}\\s*${structTypeName}\\s*;`, "g")))
	if (matchAll.length) return matchAll[0][0]
})

//----------------------------------------------------------------------------
const getStructMemberList = utils.tryCatch((str) => {
    let matchAll = Array.from(str.matchAll(/(\w+)\s*;/g))
    if (matchAll.length) return matchAll.map(x => x[1]).slice(0, -1) // get the (match) [1], throw last match (-1)
	return matchAll
})

//----------------------------------------------------------------------------
module.exports = {
	provideCompletionItems,
}
