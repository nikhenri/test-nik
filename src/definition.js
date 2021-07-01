const vscode = require('vscode')
const utils = require('./utils')
const regexp = require('./regexp')

//----------------------------------------------------------------------------
const provideDefinition = async (document, position, token) => {
	console.log("CTRL")
	utils.getFileText() // init

	let locationList = await searchLocation(document, position)
	if(locationList && locationList.length) {
        flashLine(locationList)
		return locationList
	}

	console.log("Found nothing")
}

//----------------------------------------------------------------------------
const flashLine = utils.tryCatch((locationList) => {

	let onDidChangeTextEditorSelectioEvent = vscode.window.onDidChangeTextEditorSelection((event) => {
		if(locationList.length == 1) {
			if(locationList[0].uri.fsPath != event.textEditor.document.uri.fsPath || locationList[0].range.start.line == event.selections[0].start.line) {
				let line = locationList[0].range.start.line
				let decoration = vscode.window.createTextEditorDecorationType({color: "#2196f3", backgroundColor: "#ffeb3b"})
				let rangeOption = {range: new vscode.Range(new vscode.Position(line, 0), new vscode.Position(line, 999))}
				event.textEditor.setDecorations(decoration, [rangeOption])
				// event.textEditor.revealRange(new vscode.Range(line, 0, line, 0), vscode.TextEditorRevealType.AtTop)
				setTimeout(()=>{decoration.dispose()}, 1500)
			}
		}
		onDidChangeTextEditorSelectioEvent.dispose()
	})
})

//----------------------------------------------------------------------------
const searchLocation = async (document, position) => {
	let word = document.getText(document.getWordRangeAtPosition(position))
	if(regexp.wordIsNumber(word) || regexp.wordIsReserved(word)) return
	console.log(`Word: ${word}`)

	let lineOfWordAndTextAfter = document.getText().substring(document.offsetAt(new vscode.Position(position.line, 0))) // @ TODO
	let fileNameWithoutExt = utils.uriToFileNameWithoutExt(document.uri)
	let location


	// Module instance ?
	if(regexp.isModuleInstance(lineOfWordAndTextAfter, word)) {
		console.log(`Searching module: ${word}`)
		location = getLocation(word, (text) => {return regexp.getModuleMatch(text)})
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
		location = await getLocation(null, (text)=>{return regexp.getInstanceMatch(text, word)})
		if(location) return location
	}
	// Import ?
	if (regexp.isImport(lineOfWordAndTextAfter, word)) {
		console.log(`Searching package: ${word}`)
		location = await getLocation(word, (text) => {return regexp.getPackageMatch(text)})
		if(location) return location
	}

	// is this word
	console.log(`Searching 1er line of ${word}`)
	location = await getLocation(fileNameWithoutExt, (text) => {return regexp.getWordFirstOccuranceMatch(text, word)})
	if(location[0].range.start.line != position.line)
		return location
}

//----------------------------------------------------------------------------
const getLocation = async (fileNameWithoutExt, funcMatch) => {
	// check current file
    let locationList = []

    let fileNameWithoutExtList
    if(fileNameWithoutExt)
        fileNameWithoutExtList = [fileNameWithoutExt]
    else {
		let filePathList = await utils.getFilePath()
        fileNameWithoutExtList = filePathList.map(x => utils.filePathToFileNameWithoutExt(x))
	}

    for (let name of fileNameWithoutExtList) {
        let matchInFileObj = await getMatchInFile(name, funcMatch)

	    if(!matchInFileObj && fileNameWithoutExt)
		    matchInFileObj = await getMatchInImport(name, funcMatch)

        if(matchInFileObj) {
            for (let match of matchInFileObj.match) {
                let position = utils.indexToPosition(matchInFileObj.text, match.index)
		        console.log(`Found match in ${matchInFileObj.path}, line: ${position.line}, char: ${position.character}`)
                locationList.push(new vscode.Location(vscode.Uri.file(matchInFileObj.path), position))
            }
        }
    }

    if(locationList.length) return locationList
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
// get: nameFile, name, matchFunction
// return Object:
// .path = file path
// .text = fileText
// .match = MatchAll object from regEx
const getMatchInImport = async (fileNameWithoutExt, funcMatch) => {
	let fileTextObj = await utils.getFileText(fileNameWithoutExt)
	for (let importfileNameWithoutExt of utils.getImportNameList(fileTextObj.text)) {
		let matchInFileObj = await getMatchInFile(importfileNameWithoutExt, funcMatch)
		if(matchInFileObj) return matchInFileObj
	}
}

//----------------------------------------------------------------------------


//----------------------------------------------------------------------------

module.exports = {
	provideDefinition,
}