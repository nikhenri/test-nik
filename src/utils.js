const vscode = require('vscode')
const path = require('path')
const fs = require('fs')

//----------------------------------------------------------------------------
const tryCatch = (func) => {
	return (...restArgs) => {
		try{
			return func(...restArgs)
		} catch (error) {
			console.error(`>> CATCH:\n${error}`)
			throw("Fuck off")
		}
	}
}

//----------------------------------------------------------------------------
// module.exports = func => {
//     return (req, res, next) => {
//         func(req, res, next).catch(next)
//     }

// }

//----------------------------------------------------------------------------
const replaceCommentWithSpace = tryCatch((text) => {
	return text.replace(/\/\*[\s\S]*?\*\/|\/\/.*|\r/g, (match) => {
		return " ".repeat(match.length)
	})
})

//----------------------------------------------------------------------------
const getFilePath = async (fileNameWithoutExt)=> {
	let filePath
	let search_fileNameWithoutExt = (x=> path.parse(x).name == fileNameWithoutExt)
	if(!getFilePath.listOfPath || !fileNameWithoutExt || !(filePath = getFilePath.listOfPath.find(search_fileNameWithoutExt))) {
		console.log("Updating findFiles...")
        getFilePath.listOfPath = (await vscode.workspace.findFiles("**/*.*v")).map(x => x.fsPath)
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
	let path = await getFilePath(fileNameWithoutExt)
	console.log(`Reading '${path}'`)
    let text = fs.readFileSync(path, 'utf8')
	return {text, path};
}

//----------------------------------------------------------------------------
module.exports = {
    tryCatch,
    replaceCommentWithSpace,
    getFilePath,
    getFileText,
};