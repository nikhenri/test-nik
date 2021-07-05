//----------------------------------------------------------------------------
// Function to do the CTRL + Click
//----------------------------------------------------------------------------
const vscode = require('vscode')
const utils = require('./utils')

//----------------------------------------------------------------------------
// Return a vscode location
const provideDefinition = async (document, position, token) => {
	console.log("CTRL")
	utils.getFileText() // init

	let locationList = await searchLocation(document, position)
	if(locationList && locationList.length) {
        flashLine(locationList)
		return locationList
	}

	console.log("Not able to Provide");
}

//----------------------------------------------------------------------------
const flashLine = (locationList) => {
	let onDidChangeTextEditorSelectioEvent = vscode.window.onDidChangeTextEditorSelection((event) => {
		if(locationList.length == 1) {
			// if we have move to the programmed location
			if(locationList[0].uri.fsPath == event.textEditor.document.uri.fsPath && locationList[0].range.start.line == event.selections[0].start.line) {
				setTimeout(() => {
					let line = locationList[0].range.start.line
					let decoration = vscode.window.createTextEditorDecorationType({color: "#2196f3", backgroundColor: "#ffeb3b"})
					let rangeOption = {range: new vscode.Range(new vscode.Position(line, 0), new vscode.Position(line, 999))}
					event.textEditor.setDecorations(decoration, [rangeOption])
					// event.textEditor.revealRange(new vscode.Range(line, 0, line, 0), vscode.TextEditorRevealType.AtTop)
					setTimeout(()=>{decoration.dispose()}, 1500) //remove decoration
				}, 250)
			}
		}
		onDidChangeTextEditorSelectioEvent.dispose()
	})
}

//----------------------------------------------------------------------------
// Based on the word and text following the word, return a goto vscode position
const searchLocation = async (document, position) => {
	let word = document.getText(document.getWordRangeAtPosition(position))
	if(utils.wordIsNumber(word) || utils.wordIsReserved(word)) return
	console.log(`Word: ${word}`)

	let offsetStartOfLine = document.offsetAt(new vscode.Position(position.line, 0))
	let lineOfWordAndTextAfter = utils.replaceCommentWithSpace(document.getText().substring(offsetStartOfLine))
	let fileNameWithoutExt = utils.uriToFileNameWithoutExt(document.uri)
	let location

	// Module instance ?
	if(isModuleInstance(lineOfWordAndTextAfter, word)) { // ipv4 # (
		console.log(`Searching module: ${word}`)
		location = getLocation(word, (text) => {return getModuleDeclarationMatch(text)})
		if(location) return location
	}
	// Function ?
	if(isFunction(lineOfWordAndTextAfter, word)) { // something(arg)
		console.log(`Searching function: ${word}`)
		location = await getLocation(fileNameWithoutExt, (text)=>{return getFunctionDeclarationMatch(text, word)})
		if(location) return location
	}
	// Typedef (struct, enum) ?
	if(isTypedef(lineOfWordAndTextAfter, word)) { // aType_t my_signal;
		console.log(`Searching typeDef: ${word}`)
		location = await getLocation(fileNameWithoutExt, (text)=>{return getTypedefDeclarationMatch(text, word)})
		if(location) return location
	}
	// Module decalaration ?
	if(isModuleDeclaration(lineOfWordAndTextAfter, word)) { // module ipv4 #(
		console.log(`Searching instance: ${word}`)
		location = await getLocation(null, (text)=>{return getModuleInstanceMatch(text, word)})
		if(location) return location
	}
	// Import ?
	if (isImport(lineOfWordAndTextAfter, word)) { // import pkg::*;
		console.log(`Searching package: ${word}`)
		location = await getLocation(word, (text) => {return getPackageMatch(text)})
		if(location) return location
	}

	// If we found nothing, try to get the first occurance
	console.log(`Searching 1er line of ${word}`)
	location = await getLocation(fileNameWithoutExt, (text) => {return getWordFirstOccuranceMatch(text, word)})
	if(location[0].range.start.line != position.line) return location // dont move if already 1er line
}

//----------------------------------------------------------------------------
// Will try the match function on the file 'fileNameWithoutExt'
// If no match, try the import of the file
// If fileNameWithoutExt is FALSE try match on all files instead
const getLocation = async (fileNameWithoutExt, funcMatch) => {
	let matchInFileObjList
	if(fileNameWithoutExt) // single files
		matchInFileObjList = [await utils.getMatchInFileOrImport(fileNameWithoutExt, funcMatch)]
	else // all files
		matchInFileObjList = await utils.getMatchInAllFile(funcMatch)

	let locationList = []
    for (let matchInFile of matchInFileObjList) { //for files that have a match
		for (let match of matchInFile.match) { //for all match in that file
			let position = utils.indexToPosition(matchInFile.text, match.index)
			console.log(`Found match in ${matchInFile.path}, line: ${position.line}, char: ${position.character}`)
			locationList.push(new vscode.Location(vscode.Uri.file(matchInFile.path), position))
		}
    }

    if(locationList.length) return locationList
}

//----------------------------------------------------------------------------
const isModuleInstance = (text, name) => {
    return text.match(new RegExp(`^[ ]*\\b${name}\\b\\s*(?:#\\s*\\([\\s\\S]*?\\)\\s*)?\\w+\\s*\\([\\s\\S]+?\\)\\s*;`, "g"))
}

//----------------------------------------------------------------------------
const getModuleDeclarationMatch = (text) => {
    return Array.from(text.matchAll(/^[ ]*module\s+\w+\s*/gm))
}
//----------------------------------------------------------------------------
const isFunction = (text, name) => {
	return text.match(new RegExp(`(?<!\\s\\.)\\b${name}\\b\\s*\\([\\S\\s]*?\\)`))
}

//----------------------------------------------------------------------------
const getFunctionDeclarationMatch = (text, name) => {
    return Array.from(text.matchAll(new RegExp(`^[ ]*function\\s+.*?${name}\\s*\\(`, "gm")))
}

//----------------------------------------------------------------------------
const isTypedef = (text, name) => {
	return text.match(new RegExp(`^[ ]*(?:input\\s+|output\\s+|inout\\s+)?\\b${name}\\b(?:\\s*\\[.*?\\])*\\s+\\w+`))
}

//----------------------------------------------------------------------------
const getTypedefDeclarationMatch = (text, name) => {
    return Array.from(text.matchAll(new RegExp(`^[ ]*typedef\\s+[^}]*?}\\s*${name}\\s*;`, "gm")))
}

//----------------------------------------------------------------------------
const isModuleDeclaration = (text, name) => {
	return text.match(new RegExp(`^[ ]*module\\s+\\b${name}\\b`))
}

//----------------------------------------------------------------------------
const getModuleInstanceMatch = (text, name) => {
	return Array.from(text.matchAll(new RegExp(`^[ ]*\\b${name}\\b\\s*(?:#\\s*\\([\\s\\S]*?\\)\\s*)?\\w+\\s*\\([\\s\\S]+?\\)\\s*;`, "gm")))
}

//----------------------------------------------------------------------------
const isImport = (text, name) => {
	return text.match(new RegExp(`^[ ]*import\\s*(?:.*\\s*,\\s*)*\\b${name}\\b::`))
}

//----------------------------------------------------------------------------
const getPackageMatch = (text) => {
    return Array.from(text.matchAll(/^[ ]*package\s+\w+\s*;/gm))
}

//----------------------------------------------------------------------------
const getWordOccuranceMatch = (text, name) => {
	return Array.from(text.matchAll(new RegExp(`.*\\b${name}\\b`, "g")))
}

//----------------------------------------------------------------------------
const getWordFirstOccuranceMatch = (text, name) => {
    let match = getWordOccuranceMatch(text, name)
    if (match.length) return [match[0]] //only the first one
    return match
}

//----------------------------------------------------------------------------
module.exports = {
	provideDefinition,
}