//----------------------------------------------------------------------------
// Function to do the completion after the '.'
//----------------------------------------------------------------------------
const vscode = require('vscode')
const utils = require('./utils')
const ouputChannel = require('./ouputChannel')

//----------------------------------------------------------------------------
function provideCompletionItemsDot(document, position){
	return utils.tryCatch(__provideCompletionItemsDot, document, position)
}

//----------------------------------------------------------------------------
function __provideCompletionItemsDot(document, position){
	// get line to see if in comment
	// let fileNameWithoutExt = utils.uriToFileNameWithoutExt(document.uri)
	// utils.getFileText() // init
	// let fileTextObj = utils.getFileText(fileNameWithoutExt)
	// let lines = fileTextObj.text.split(/\r?\n|\r|\n/g);
	// let linePrefix_no_comment = lines[position.line].substr(0, position.character-1)

	let linePrefix = document.lineAt(position).text.substr(0, position.character)
	// if (!linePrefix.endsWith('.') || !isStructAccess(linePrefix) || linePrefix_no_comment != linePrefix.slice(0,-1))
	if (!linePrefix.endsWith('.') || !isStructAccess(linePrefix))
		return //avoid trig for nothing
	ouputChannel.log(".")
	utils.getFileText() // init

	let fileNameWithoutExt = utils.uriToFileNameWithoutExt(document.uri)
	let fileTextObj = utils.getFileText(fileNameWithoutExt)

	if(fileTextObj) {
		let textToSearchTypeName = fileTextObj.text
		let groupMatch = getStructSectionWithoutIndex(linePrefix) //split the string in section

		for (let signalName of groupMatch) {
			let structTypeName = getTypeName(textToSearchTypeName, signalName)
			if(!structTypeName || utils.wordIsReserved(structTypeName)) return // ex: not found or logic toto;
			let matchInFileObj = utils.getMatchInFileOrImport(fileNameWithoutExt, (text)=> searchStructInText(text, structTypeName))
			if(matchInFileObj) {
				if(groupMatch[groupMatch.length-1] == signalName) { // last element, add member
					let structMemberList = getStructMemberList(matchInFileObj.match[0][0])
					let completionList = structMemberList.map(x=>new vscode.CompletionItem(x))
					ouputChannel.log("Found struct members")
					return completionList
				} else { // if we are not the last section, init search text and filename
					textToSearchTypeName = matchInFileObj.match[0][0]
					fileNameWithoutExt = matchInFileObj.fileNameWithoutExt
				}
			}
		}
	}
	ouputChannel.log("Not able to Complete")
}

//----------------------------------------------------------------------------
function isStructAccess(text){
	return text.match(/[\w\.\[\]]+\.$/g)
}
//----------------------------------------------------------------------------
// split the string in section, toto[7:0].tata => [toto, tata]
function getStructSectionWithoutIndex(text){
	let match = text.match(/[\w\.\[\]]+$/g) //match end of line something[666].
	let matchAll = Array.from(match[0].matchAll(/(\w+)(?:\[.*?\])?\./g)) //extract word
	let groupMatch = matchAll.map(x => x[1])
	return groupMatch
}

//----------------------------------------------------------------------------
function getTypeName(str, signalName){
	// type(os_txOut_events_p) s_events_ptrWr_s;
	// input ts_bufferHandler_cbdma_ptrWr_in is_txIn_ptrWr_p,
	// ts_bufferHandler_cbdma_ptrWr_in [2:0] vg_byte_size_s
  let matchAll = Array.from(str.matchAll(new RegExp(`^[ ]*(?:input|output|inout|localparam|parameter|var)?[ ]*(\\w+)(\\(\\w+\\))?.*?\\b${signalName}\\b`, "gm")))
	if(!matchAll.length) return
	let typeName = matchAll[0][1]
	if(typeName != "type") return typeName
	return getTypeName(str, matchAll[0][2].slice(1,-1))
}

//----------------------------------------------------------------------------
function searchStructInText(text, structTypeName){
	return Array.from(text.matchAll(new RegExp(`struct(?:\\s+packed)?\\s*{[^}]*}\\s*${structTypeName}\\s*;`, "g")))
}

//----------------------------------------------------------------------------
function getStructMemberList(str){
    let matchAll = Array.from(str.matchAll(/(.*?)(\w+)\s*;/g))
    if (matchAll.length)
		return matchAll.map(x => {return {label:x[2], description:x[1].trim().replace(/\s+/, ' ')}}).slice(0, -1) // throw last match (-1), it is the name
	return []
}

//----------------------------------------------------------------------------
module.exports = {
	provideCompletionItemsDot,
}
