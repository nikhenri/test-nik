const vscode = require('vscode')
const utils = require('./utils')
const regexp = require('./regexp')

//----------------------------------------------------------------------------
const provideDefinition = async (document, position, token) => {
	console.log("CTRL")
	utils.getFileText() // init

	let location = await searchLocation(document, position)
	if(location) {
		if(!Array.isArray(location)) flashLine(location.range.start.line)
		return location
	}
	
	console.log("Found nothing")
}

//----------------------------------------------------------------------------
const flashLine = utils.tryCatch((line) => {
	let event = vscode.window.onDidChangeTextEditorSelection(() => {
		setTimeout(()=>{
			let decoration = vscode.window.createTextEditorDecorationType({color: "#2196f3", backgroundColor: "#ffeb3b"})
			let rangeOption = {range: new vscode.Range(new vscode.Position(line, 0), new vscode.Position(line, 999))}
			vscode.window.activeTextEditor.setDecorations(decoration, [rangeOption])
			setTimeout(()=>{decoration.dispose()}, 1500)
		}, 100)
		event.dispose()
	})
})

//----------------------------------------------------------------------------
const searchLocation = async (document, position) => {
	let word = document.getText(document.getWordRangeAtPosition(position))
	if(regexp.wordIsNumber(word) || regexp.wordIsReserved(word)) return
	// console.log(`Word: ${word}`)

	let lineOfWordAndTextAfter = document.getText().substring(document.offsetAt(new vscode.Position(position.line, 0))) // @ TODO
	let fileNameWithoutExt = utils.uriToFileNameWithoutExt(document.uri)
	let location

	// Module instance ?
	if(regexp.isModuleInstance(lineOfWordAndTextAfter, word)) {
		console.log(`Searching module: ${word}`)
		location = getLocation(fileNameWithoutExt, (text) => {return regexp.getModuleMatch(text)})
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
		location = await getMatchInAllFile(word, (text)=>{return regexp.getInstanceMatch(text, word)})
		if(location) return location
	}
	// Import ?
	if (regexp.isImport(lineOfWordAndTextAfter, word)) {
		console.log(`Searching package: ${word}`)
		location = await getLocation(fileNameWithoutExt, (text) => {return regexp.getPackageMatch(text)})
		if(location) return location
	}

	// is this word
	console.log(`Searching 1er line of ${word}`)
	location = await getLocation(fileNameWithoutExt, (text) => {return regexp.getWordOccuranceMatch(text, word)})

	return location
}
//----------------------------------------------------------------------------
const getMatchInAllFile = async (name, funcMatch) => {
	let filePathList = await utils.getFilePath()
	let locationList = []
	for (let filePath of filePathList) {
		let matchInFileObj = await getMatchInFile(utils.filePathToFileNameWithoutExt(filePath), funcMatch)
		if(matchInFileObj) {
			for (let match of matchInFileObj.match) {
				let position = utils.indexToPosition(matchInFileObj.text, match.index)
				locationList.push(new vscode.Location(vscode.Uri.file(matchInFileObj.path), position))
			}
		}
	}
	if(locationList.length) {
		return locationList
	}
	console.log(`Can't found instance: ${name}`)
}

//----------------------------------------------------------------------------
const getLocation = async (fileNameWithoutExt, funcMatch) => {
	// check current file
	let matchInFileObj = await getMatchInFile(fileNameWithoutExt, funcMatch)

	if(!matchInFileObj)
		matchInFileObj = await getMatchInImport(fileNameWithoutExt, funcMatch)

	if(matchInFileObj) {
		let position = utils.indexToPosition(matchInFileObj.text, matchInFileObj.match[0].index)
		console.log(`Found match in ${matchInFileObj.path}, line: ${position.line}, char: ${position.character}`)
		return new vscode.Location(vscode.Uri.file(matchInFileObj.path), position)
	}
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
	for (let importfileNameWithoutExt of getImportNameList(fileTextObj.text)) {
		let matchInFileObj = await getMatchInFile(importfileNameWithoutExt, funcMatch)
		if(matchInFileObj) return matchInFileObj
	}
}

//----------------------------------------------------------------------------
const getImportNameList = utils.tryCatch((text) => {
	let matchAll = Array.from(text.matchAll(/^\s*import\s*?(.*);$/gm))
	let groupMatch = matchAll.map(x => x[1])
	let ImportNameList = []
	for (let match of groupMatch) {
		for (let packageStr of match.split(",")) {
			let packageName = packageStr.trim().split("::")[0]
			// console.log(`Found package ${packageName}`)
			ImportNameList.push(packageName)
		}
	}
	return ImportNameList
})

//----------------------------------------------------------------------------

module.exports = {
	provideDefinition,
}