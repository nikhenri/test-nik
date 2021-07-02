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
			let matchInFileObj = await searchStruct(structTypeName, fileNameWithoutExt)
            if(groupMatch[groupMatch.length-1] == signalName) { // last element
				let structMemberList = getStructMemberList(matchInFileObj.match[0][0])
                let completionList = structMemberList.map(x=>new vscode.CompletionItem(x))
                return completionList
            } else {
                textToSearchTypeName = matchInFileObj.match[0][0]
                fileNameWithoutExt = matchInFileObj.fileNameWithoutExt
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
	let matchInFileObj = await utils.getMatchInFileOrImport(fileNameWithoutExt, text=> searchStructInText(text, structTypeName))
	if(matchInFileObj) return matchInFileObj
}

//----------------------------------------------------------------------------
const searchStructInText = utils.tryCatch((text, structTypeName) => {
	return Array.from(text.matchAll(new RegExp(`struct(?:\\s+packed)?\\s*{[^}]*}\\s*${structTypeName}\\s*;`, "g")))
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
