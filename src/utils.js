const vscode = require('vscode')
const path = require('path')
const fs = require('fs')

//----------------------------------------------------------------------------
const tryCatch = (func) => {
	return (...restArgs) => {
		try{
			return func(...restArgs)
		} catch (error) {
			console.error(`>> ${error}`)
			// console.trace()
			throw("Fuck off")
		}
	}
}

//----------------------------------------------------------------------------
const tryCatchAsync = (func) => {
	return (...restArgs) => {
		func(...restArgs).
		then((ret)=>{
			console.log(ret)
			return ret
		}).catch((error) => {
			console.error(`>> ${error}`)
			// console.trace()
			throw("Fuck off")
		})
	}
}

//----------------------------------------------------------------------------
const replaceCommentWithSpace = tryCatch((text) => {
	return text.replace(/\/\*[\s\S]*?\*\/|\/\/.*|/g, (match) => {
		return " ".repeat(match.length)
	})
})

//----------------------------------------------------------------------------
const getFilePath = async (fileNameWithoutExt)=> {
	let filePath
	let search_fileNameWithoutExt = (x=> path.parse(x).name == fileNameWithoutExt)
	if(!getFilePath.listOfPath || !fileNameWithoutExt || !(filePath = getFilePath.listOfPath.find(search_fileNameWithoutExt))) {
		console.log("Updating findFiles...")
        let finFiles = await vscode.workspace.findFiles("**/*.*v")
		getFilePath.listOfPath = finFiles.map(x => x.fsPath)
		console.log("Done")

		if (!fileNameWithoutExt)
			filePath = getFilePath.listOfPath
		else
		filePath = getFilePath.listOfPath.find(search_fileNameWithoutExt)
    }
		if(!filePath) console.log(`Was not able to found '${fileNameWithoutExt}'`)
	return filePath
}

//----------------------------------------------------------------------------
const getFileText = async (fileNameWithoutExt) => {
	if(!fileNameWithoutExt) {
		getFileText.textObj = {}
		return
	}
	if(!(fileNameWithoutExt in getFileText.textObj)) {
		let path = await getFilePath(fileNameWithoutExt)
		console.log(`Reading '${path}'`)
    	let text = replaceCommentWithSpace(fs.readFileSync(path, 'utf8'))
		getFileText.textObj[fileNameWithoutExt] = { path, text }
	}

	return getFileText.textObj[fileNameWithoutExt];
}

//----------------------------------------------------------------------------
const uriToFileNameWithoutExt = tryCatch((uri) => {
	return path.parse(uri.fsPath).name
})

//----------------------------------------------------------------------------
const indexToPosition = tryCatch((text, index) => {
	let lineSplit = text.substr(0, index).split(/\r\n|\n/)
	let line = lineSplit.length - 1
	let char = lineSplit[lineSplit.length - 1].length
	return new vscode.Position(line, char)
})
//----------------------------------------------------------------------------
module.exports = {
    tryCatch,
	tryCatchAsync,
    replaceCommentWithSpace,
    getFilePath,
    getFileText,
	uriToFileNameWithoutExt,
	indexToPosition,
};