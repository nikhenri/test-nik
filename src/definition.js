//----------------------------------------------------------------------------
// Function to do the CTRL + Click
//----------------------------------------------------------------------------
const vscode = require('vscode')
const utils = require('./utils')
const ouputChannel = require('./ouputChannel')

//----------------------------------------------------------------------------
// Return a vscode location
function provideDefinition (document, position) {
	ouputChannel.log("CTRL")

	utils.getFileText() // init

	let locationList = searchLocation(document, position)
	if(locationList) return locationList

	ouputChannel.log("Not able to Provide definition")
}

//----------------------------------------------------------------------------
// Based on the word and text following the word, return a goto vscode position
function searchLocation(document, position) {
	let word = document.getText(document.getWordRangeAtPosition(position))
	if(utils.wordIsNumber(word) || utils.wordIsReserved(word)) return
	// console.log(`Word: ${word}`)

	let offsetStartOfLine = document.offsetAt(new vscode.Position(position.line, 0))
	let lineOfWordAndTextAfter = utils.replaceCommentWithSpace(document.getText().substring(offsetStartOfLine))
	let fileNameWithoutExt = utils.uriToFileNameWithoutExt(document.uri)
	let location

	// Module instance ?
	if(isModuleInstance(lineOfWordAndTextAfter, word)) { // ipv4 # (
		ouputChannel.log(`Searching module: ${word}`)
		location = getLocation(word, (text) => getModuleDeclarationMatch(text))
		if(location) return location
	}

	// Typedef (struct, enum) ?
	if(isTypedef(lineOfWordAndTextAfter, word)) { // aType_t my_signal;
		ouputChannel.log(`Searching typeDef: ${word}`)
		location = getLocation(fileNameWithoutExt, (text) => getTypedefDeclarationMatch(text, word))
		if(location) return location
	}

	// Module decalaration ?
	if(isModuleDeclaration(lineOfWordAndTextAfter, word)) { // module ipv4 #(
		ouputChannel.log(`Searching instance: ${word}`)
		location = getLocation(null, (text) => getModuleInstanceMatch(text, word))
		if(location) return location
	}

	// Module decalaration ?
	if(isModulePort(lineOfWordAndTextAfter, word)) { // input logic i_clock_p,
		ouputChannel.log(`Searching pin: ${word}`)
		location = getLocation(null, (text) => getPinInstanceMatch(text, word, fileNameWithoutExt))
		if(location) return location
	}

	// Import ?
	if (isImport(lineOfWordAndTextAfter, word)) { // import pkg::*;
		ouputChannel.log(`Searching package: ${word}`)
		location = getLocation(word, (text) => getPackageMatch(text))
		if(location) return location
	}

	// Pin ?
	let wordWithLinePrefix = document.lineAt(position).text.substr(0, document.getWordRangeAtPosition(position).end.character)
	if (isInstancePin(wordWithLinePrefix, word)) { // .toto (),
		ouputChannel.log(`Searching port: ${word}`)
		let instanceName = getInstanceAtLine(fileNameWithoutExt, position.line)
		location = getLocation(instanceName, (text) => getWordFirstOccuranceMatch(text, word))
		if(location) return location
	}

	// Function ?
	let wordWithLineSuffix = document.lineAt(position).text.substr(document.getWordRangeAtPosition(position).start.character)
	if(isFunction(wordWithLineSuffix, word)) { // something(arg)
		ouputChannel.log(`Searching function: ${word}`)
		location = getLocation(fileNameWithoutExt, (text) => getFunctionDeclarationMatch(text, word))
		if(location) return location
	}
	// If we found nothing, try to get the first occurance
	ouputChannel.log(`Searching 1er line of ${word}`)
	location = getLocation(fileNameWithoutExt, (text) => getWordFirstOccuranceMatch(text, word))
	if(location[0].targetRange.start.line != position.line) return location // dont move if already 1er line
}

//----------------------------------------------------------------------------
// Will try the match function on the file 'fileNameWithoutExt'
// If no match, try the import of the file
// If fileNameWithoutExt is FALSE try match on all files instead
function getLocation(fileNameWithoutExt, funcMatch) {
	let matchInFileObjList
	if(fileNameWithoutExt) // single files
		matchInFileObjList = [utils.getMatchInFileOrImport(fileNameWithoutExt, funcMatch)]
	else // all files
		matchInFileObjList = utils.getMatchInAllFile(funcMatch)

	let locationList = []
    for (let matchInFile of matchInFileObjList) { //for files that have a match
		for (let match of matchInFile.match) { //for all match in that file
			let position_start = utils.indexToPosition(matchInFile.text, match.index)
			let position_end = utils.indexToPosition(matchInFile.text, match.index + match[0].length)
			ouputChannel.log(`Found match in ${matchInFile.path}=> line:${position_start.line}, char:${position_start.character} to line:${position_end.line}, char:${position_end.character}`)
			// locationList.push(new vscode.Location(vscode.Uri.file(matchInFile.path), position))

			locationList.push({targetRange: new vscode.Range(new vscode.Position(position_start.line, 0), new vscode.Position(position_end.line, 999)),
							   targetSelectionRange: new vscode.Range(new vscode.Position(position_start.line, 0), new vscode.Position(position_start.line, 999)),
							   targetUri: vscode.Uri.file(matchInFile.path)
			})
		}
    }

    if(locationList.length) return locationList
}

//----------------------------------------------------------------------------
function isModuleInstance(text, name) {
    return text.match(new RegExp(`^[ ]*\\b${name}\\b\\s*(?:#\\s*\\([\\s\\S]*?\\)\\s*)?\\w+\\s*\\([\\s\\S]+?\\)\\s*;`, "g"))
}

//----------------------------------------------------------------------------
function getModuleDeclarationMatch(text) {
    return Array.from(text.matchAll(/^[ ]*module\s+\w+\s*/gm))
}
//----------------------------------------------------------------------------
function isFunction(text, name) {
	return text.match(new RegExp(`^\\b${name}\\b\\s*\\([\\S\\s]*?\\)`))
}

//----------------------------------------------------------------------------
function getFunctionDeclarationMatch(text, name) {
    return Array.from(text.matchAll(new RegExp(`^[ ]*function\\s+.*?${name}\\s*\\(`, "gm")))
}

//----------------------------------------------------------------------------
function isTypedef(text, name) {
	return text.match(new RegExp(`^[ ]*(?:input\\s+|output\\s+|inout\\s+)?\\b${name}\\b(?:\\s*\\[.*?\\])*\\s+\\w+`))
}

//----------------------------------------------------------------------------
function getTypedefDeclarationMatch(text, name) {
    return Array.from(text.matchAll(new RegExp(`^[ ]*typedef\\s+[^}]*?}\\s*${name}\\s*;`, "gm")))
}

//----------------------------------------------------------------------------
function isModuleDeclaration(text, name) {
	return text.match(new RegExp(`^[ ]*module\\s+\\b${name}\\b`))
}

//----------------------------------------------------------------------------
function getModuleInstanceMatch(text, name) {
	return Array.from(text.matchAll(new RegExp(`^[ ]*\\b${name}\\b\\s*(?:#\\s*\\([\\s\\S]*?\\)\\s*)?\\w+\\s*\\([\\s\\S]+?\\)\\s*;`, "gm")))
}

//----------------------------------------------------------------------------
function isModulePort(text, name) {
	return text.match(new RegExp(`^\\s*(?:input|output|inout|parameter)\\s+.*\\b${name}\\b`))
}

//----------------------------------------------------------------------------
function getPinInstanceMatch(text, name, fileNameWithoutExt) {
	// get the Instance Match
	let matchAll = getModuleInstanceMatch(text, fileNameWithoutExt)
	let regExp = new RegExp(`^[ ]*\\.${name}\\b`, "gm")
	if(matchAll.length) {
		for (let match of matchAll) { // find the pin (.name) in the match and add the offset to overall match
			let matchPin = Array.from(match[0].matchAll(regExp))
			if(matchPin.length)	match.index += matchPin[0].index // might be possible the pin is not connected
		}
	}
	return []
}

//----------------------------------------------------------------------------
function isImport(text, name) {
	return text.match(new RegExp(`^[ ]*import\\s*(?:.*\\s*,\\s*)*\\b${name}\\b::`))
}

//----------------------------------------------------------------------------
function getPackageMatch(text) {
    return Array.from(text.matchAll(/^[ ]*package\s+\w+\s*;/gm))
}

//----------------------------------------------------------------------------
function isInstancePin(text, name) {
	return text.match(new RegExp(`^[ ]*\\.\\s*${name}\\b$`))
}

//----------------------------------------------------------------------------
function getInstanceMatch(text) {
	//let matchAll = Array.from(text.matchAll(/^[ ]*(\w+)\s*(?:#\s*\([\s\S]*?\)\s*)?\w+\s*\(/gm))
	return Array.from(text.matchAll(/^[ ]*(\w+)\s*(?:#\s*\([^;]*\)\s*)?\w+\s*\(\s*\./gm))
}
//----------------------------------------------------------------------------
// function getPortMatch(text, name) {
// 	return Array.from(text.matchAll(new RegExp(`^[ ].*?\\b${name}\\b\\s*(?:\\[.*?\\]\\s*)*`, "gm")))
// }

//----------------------------------------------------------------------------
function getWordOccuranceMatch(text, name) {
	return Array.from(text.matchAll(new RegExp(`.*\\b${name}\\b`, "g")))
}

//----------------------------------------------------------------------------
function getWordFirstOccuranceMatch(text, name) {
    let match = getWordOccuranceMatch(text, name)
    if (match.length) return [match[0]] //only the first one
    return []
}

//----------------------------------------------------------------------------
function getInstanceAtLine(fileNameWithoutExt, line) {
	let text = (utils.getFileText(fileNameWithoutExt)).text
	let allInstanceName = getInstanceMatch(text)
	let instanceName
	for (let inst of allInstanceName) {
		let currentLine = utils.indexToPosition(text, inst.index).line
		if (currentLine > line) break
		instanceName = inst[1]
	}
	return instanceName
}
//----------------------------------------------------------------------------
module.exports = {
	provideDefinition,
}