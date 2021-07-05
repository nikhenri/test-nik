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

	let lineOfWordAndTextAfter = utils.replaceCommentWithSpace(document.getText().substring(document.offsetAt(new vscode.Position(position.line, 0)))) // @ TODO
	let fileNameWithoutExt = utils.uriToFileNameWithoutExt(document.uri)
	let location


	// Module instance ?
	if(isModuleInstance(lineOfWordAndTextAfter, word)) {
		console.log(`Searching module: ${word}`)
		location = getLocation(word, (text) => {return getModuleMatch(text)})
		if(location) return location
	}
	// Function ?
	if(isFunction(lineOfWordAndTextAfter, word)) {
		console.log(`Searching function: ${word}`)
		location = await getLocation(fileNameWithoutExt, (text)=>{return getFunctionMatch(text, word)})
		if(location) return location
	}
	// Typedef (struct, enum) ?
	if(isTypedef(lineOfWordAndTextAfter, word)) {
		console.log(`Searching typeDef: ${word}`)
		location = await getLocation(fileNameWithoutExt, (text)=>{return getTypeMatch(text, word)})
		if(location) return location
	}
	// Module decalaration ?
	if(isModuleDeclaration(lineOfWordAndTextAfter, word)) {
		console.log(`Searching instance: ${word}`)
		location = await getLocation(null, (text)=>{return getInstanceMatch(text, word)})
		if(location) return location
	}
	// Import ?
	if (isImport(lineOfWordAndTextAfter, word)) {
		console.log(`Searching package: ${word}`)
		location = await getLocation(word, (text) => {return getPackageMatch(text)})
		if(location) return location
	}

	// is this word
	console.log(`Searching 1er line of ${word}`)
	location = await getLocation(fileNameWithoutExt, (text) => {return getWordFirstOccuranceMatch(text, word)})
	if(location[0].range.start.line != position.line)
		return location
}

//----------------------------------------------------------------------------
const getLocation = async (fileNameWithoutExt, funcMatch) => {
	let matchInFileObjList
	if(fileNameWithoutExt)
		matchInFileObjList = [await utils.getMatchInFileOrImport(fileNameWithoutExt, funcMatch)]
	else 
		matchInFileObjList = await utils.getMatchInAllFile(funcMatch)

	let locationList = []
    for (let matchInFile of matchInFileObjList) {
		for (let match of matchInFile.match) {
			let position = utils.indexToPosition(matchInFile.text, match.index)
			console.log(`Found match in ${matchInFile.path}, line: ${position.line}, char: ${position.character}`)
			locationList.push(new vscode.Location(vscode.Uri.file(matchInFile.path), position))
		}
    }

    if(locationList.length) return locationList
}

//----------------------------------------------------------------------------
const isModuleInstance = utils.tryCatch((text, name) => {
    return text.match(new RegExp(`^[ ]*\\b${name}\\b\\s*(?:#\\s*\\([\\s\\S]*?\\)\\s*)?\\w+\\s*\\([\\s\\S]+?\\)\\s*;`, "g"))
})

//----------------------------------------------------------------------------
const isFunction = utils.tryCatch((text, name) => {
	// return text.match(new RegExp(`[\\.| ]+\\b${name}\\b\\s*\\([\\S\\s]*?\\)`))
	return text.match(new RegExp(`(?<!\\s\\.)\\b${name}\\b\\s*\\([\\S\\s]*?\\)`))
})

//----------------------------------------------------------------------------
const isTypedef = utils.tryCatch((text, name) => {
	return text.match(new RegExp(`^[ ]*(?:input\\s+|output\\s+|inout\\s+)?\\b${name}\\b(?:\\s*\\[.*?\\])*\\s+\\w+`))
})

//----------------------------------------------------------------------------
const isModuleDeclaration = utils.tryCatch((text, name) => {
	return text.match(new RegExp(`^[ ]*module\\s+\\b${name}\\b`))
})

//----------------------------------------------------------------------------
const isImport = utils.tryCatch((text, name) => {
	return text.match(new RegExp(`^[ ]*import\\s*(?:.*\\s*,\\s*)*\\b${name}\\b::`))
})
//============================================================================
const getModuleMatch = utils.tryCatch((text) => {
    // return Array.from(text.matchAll(new RegExp(`^[ ]*module\\s+\\b${name}\\b`, "gm")))
    return Array.from(text.matchAll(/^[ ]*module\s+\w+\s*/gm))
})

//----------------------------------------------------------------------------
const getFunctionMatch = utils.tryCatch((text, name) => {
    return Array.from(text.matchAll(new RegExp(`^[ ]*function\\s+.*?${name}\\s*\\(`, "gm")))
})

//----------------------------------------------------------------------------
const getInstanceMatch = utils.tryCatch((text, name) => {
	return Array.from(text.matchAll(new RegExp(`^[ ]*\\b${name}\\b\\s*(?:#\\s*\\([\\s\\S]*?\\)\\s*)?\\w+\\s*\\([\\s\\S]+?\\)\\s*;`, "gm")))
})

//----------------------------------------------------------------------------
const getTypeMatch = utils.tryCatch((text, name) => {
    return Array.from(text.matchAll(new RegExp(`^[ ]*typedef\\s+[^}]*?}\\s*${name}\\s*;`, "gm")))
})
//----------------------------------------------------------------------------
// const getImportMatch = utils.tryCatch((text) => {
//     return Array.from(text.matchAll(/^[ ]*import\s+[^;]*/gm))
// })
//----------------------------------------------------------------------------
const getPackageMatch = utils.tryCatch((text) => {
    return Array.from(text.matchAll(/^[ ]*package\s+\w+\s*;/gm))
})
//----------------------------------------------------------------------------
const getWordOccuranceMatch = utils.tryCatch((text, name) => {
	return Array.from(text.matchAll(new RegExp(`.*\\b${name}\\b`, "g")))
})
//----------------------------------------------------------------------------
const getWordFirstOccuranceMatch = utils.tryCatch((text, name) => {
    let match = getWordOccuranceMatch(text, name)
    if (match.length) return [match[0]]
    return match
})
//----------------------------------------------------------------------------

module.exports = {
	provideDefinition,
}