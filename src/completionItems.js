const vscode = require('vscode')
const fs = require('fs')
const utils = require('./utils')

//----------------------------------------------------------------------------
const provideCompletionItems = async (document, position) => {
	console.log(".")
	utils.getFileText() // init

	let linePrefix = document.lineAt(position).text.substr(0, position.character)
	if (linePrefix.endsWith('.') && isStructAccess(linePrefix)) {
		let fileNameWithoutExt = utils.uriToFileNameWithoutExt(document.uri)
		let groupMatch = getStructSectionWithoutIndex(linePrefix)
        let text = document.getText()
		for (let signalName of groupMatch) {
			console.log(`>> ${signalName}`)

			let structTypeName = getStructTypeName(text, signalName)
			console.log(`** ${structTypeName}`)
			let structDeclaration = await searchStruct(structTypeName, fileNameWithoutExt)
			console.log(`++ ${JSON.stringify(structDeclaration)}`)
            if(groupMatch[groupMatch.length-1] == signalName) { // last element
                let completionList = []
                for (let structMember of getStructMemberName(structDeclaration.struct)) {
                    console.log(`Found member ${structMember}`)
                    completionList.push(new vscode.CompletionItem(structMember))
                }
                return completionList
            } else {
                console.log("here");
                text = structDeclaration.struct
                fileNameWithoutExt = structDeclaration.fileNameWithoutExt
            }
		}
	}
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
const getStructTypeName = utils.tryCatch((str, signalName) => {
	// first word that is not input | output | inout
    let matchAll = Array.from(str.matchAll(new RegExp(`^[ ]*(?:input|output|inout)?[ ]*(\\w+).*?${signalName}`, "gm")))
	if (matchAll.length) return matchAll[0][1] //[0] get first occurance of the signal, [1] get the (match)
})

//----------------------------------------------------------------------------
// @TODO need to add an object of 'scanned' to avoid recursive scan
const searchStruct = async (structTypeName, fileNameWithoutExt) => {
	// let filePathToFileNameWithoutExt = utils.filePathToFileNameWithoutExt(filePath)
	// console.log(`Searching struct in '${filePathToFileNameWithoutExt}'`)
    let fileTextObj = await utils.getFileText(fileNameWithoutExt)
	let struct = searchStructInText(fileTextObj.text, structTypeName)
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
	let struct_list =  getStructList(text)

	for (let struct of struct_list) {
		// console.log(`Scanning struct '${struct}'`)
		if(getStructName(struct) == structTypeName) {
			console.log(`Found struct`)
			return struct
		}
	}
})
//----------------------------------------------------------------------------
const getStructName = utils.tryCatch((str) => {
	return str.match(/}\s*(\w+)\s*;/)[1]
})

//----------------------------------------------------------------------------
//----------------------------------------------------------------------------
//----------------------------------------------------------------------------

//----------------------------------------------------------------------------
const getStructList = utils.tryCatch((str) => {
	// 'struct' with or without 'packed' { * } 'word';
    let matchAll = Array.from(str.matchAll(/struct(?:\s+packed)?\s*{[\S\s]*?}\s*\w+\s*;/gm))
    if (matchAll.length) return matchAll.map(x => x[0])
	return matchAll
})



//----------------------------------------------------------------------------
const getStructMemberName = utils.tryCatch((str) => {
    let matchAll = Array.from(str.matchAll(/(\w+)\s*;/g))
    if (matchAll.length) return matchAll.map(x => x[1]).slice(0, -1) // get the (match) [1], throw last match (-1)
	return matchAll
})

module.exports = {
	provideCompletionItems,
}

/*


for (let structMember of getStructMemberName(struct)) {
				console.log(`Found member ${structMember}`)
				completionList.push(new vscode.CompletionItem(structMember))
			}
			return completionList

*/