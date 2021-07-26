//----------------------------------------------------------------------------
// Contains function that need to be share accross multiple files
//----------------------------------------------------------------------------
const vscode = require('vscode')
const path = require('path')
const fs = require('fs')
const glob = require('glob')

const ouputChannel = require('./ouputChannel')

//----------------------------------------------------------------------------
// Remplace all comment by space so regex are easier to do
function replaceCommentWithSpace(text) {
	let textWithoutComment = text.replace(/\/\*[\s\S]*?\*\/|\/\/.*/g, (match) => {
		return match.replace(/[^\n\r]*/g, submatch => {
			return " ".repeat(submatch.length)})
	})
	return textWithoutComment
}

//----------------------------------------------------------------------------
// Will search all file that have the name 'fileNameWithoutExt' with extension .sv or .v
// Ex: toto => return C:/something/toto.sv
// If 'fileNameWithoutExt' is false, will return a list of all the file with extension .sv or .v
function getFilePath(fileNameWithoutExt) {
	let filePath
	let search_fileNameWithoutExt = (x=> path.parse(x).name == fileNameWithoutExt) // find function
	// If the list is not initialized OR we want all file OR the file is not found in list
	if(!getFilePath.listOfPath || !fileNameWithoutExt || !(filePath = getFilePath.listOfPath.find(search_fileNameWithoutExt))) {
		ouputChannel.log(`Updating findFiles for ${fileNameWithoutExt}...`)
		//let finFiles = await vscode.workspace.findFiles("**/*.{v,sv}") //get URI of all file
		//getFilePath.listOfPath = finFiles.map(x => x.fsPath.replace(/\\/g,"/")) //keep only the path
		const workspaceFolder = vscode.workspace.workspaceFolders[0].uri.fsPath.replace(/\\/g,"/")
		getFilePath.listOfPath = glob.sync(`${workspaceFolder}/**/*.{v,sv}`) //get URI of all file
		if (fileNameWithoutExt) //if we want a specific file
			filePath = getFilePath.listOfPath.find(search_fileNameWithoutExt)
		else // if we want all file
			filePath = getFilePath.listOfPath
		ouputChannel.log("Update done")
	}
	if(!filePath) {
		let str = `Was not able to found file '${fileNameWithoutExt}.{v|sv}'`
		ouputChannel.log(str)
		vscode.window.showErrorMessage(str)
	}
	return filePath
}
// let a = ['aaa/nnn', 'ccc/bbb']
// let b = a.reduce((result, item, index) => {
//   result[item.substring(4)] = item
//   return result
// }, {})
// console.log(b)
//----------------------------------------------------------------------------
// Get the text comment removed in a file, based on the fileNameWithoutExt
// This function will save the text in memory
// So the next call for same file will return the previous read value
// Calling the fct without parameter clear the memory
function getFileText(fileNameWithoutExt) {
	if(!fileNameWithoutExt) { // clear memory
		getFileText.textObj = {}
		return
	} else if (!getFileText.textObj)
		throw("getFileText need to be init")

	if(!(fileNameWithoutExt in getFileText.textObj)) { // not already read
		let path = getFilePath(fileNameWithoutExt)
		let text
		if(!path) return
		if(uriToFileNameWithoutExt(vscode.window.activeTextEditor.document.uri) == fileNameWithoutExt) //file currently open
			text = replaceCommentWithSpace(vscode.window.activeTextEditor.document.getText())
		else
			text = replaceCommentWithSpace(fs.readFileSync(path, 'utf8'))

		getFileText.textObj[fileNameWithoutExt] = {path, text, fileNameWithoutExt} //save for future call
	}

	return getFileText.textObj[fileNameWithoutExt]
}

//----------------------------------------------------------------------------
function uriToFileNameWithoutExt(uri) {
	return filePathToFileNameWithoutExt(uri.fsPath)
}
//----------------------------------------------------------------------------
function filePathToFileNameWithoutExt(filePath) {
	return path.parse(filePath).name
}
//----------------------------------------------------------------------------
// Get a index/offset caracter, convert into line/char
function indexToPosition (text, index) {
	let lineSplit = text.substr(0, index).split(/\r\n|\n/)
	let line = lineSplit.length - 1
	let char = lineSplit[lineSplit.length - 1].length
	return new vscode.Position(line, char)
}
//----------------------------------------------------------------------------
// return a name of import use in file (import oti_header_pkg::*; => return oti_header_pkg)
function getImportNameList(fileNameWithoutExt) {
	let text = getFileText(fileNameWithoutExt).text
	let matchAll = Array.from(text.matchAll(/(\w+)::\*/gm))
	if (matchAll.length) {
		return  matchAll.map(x => x[1]).filter(x=> x != fileNameWithoutExt)
	}
	return matchAll
}
//----------------------------------------------------------------------------
function getImportNameListInOrder(fileNameWithoutExt) {
	let importNameListRecursive = getImportNameListRecursive(fileNameWithoutExt)
	let importNameListInOrder = []
	for (let importName of importNameListRecursive.reverse()) {
		if(!importNameListInOrder.includes(importName))
			importNameListInOrder.push(importName)
	}
	return importNameListInOrder
}
//----------------------------------------------------------------------------
function getImportNameListRecursive(fileNameWithoutExt, importList = []) {
	// console.log(`Inspecting ${fileNameWithoutExt}`)
	let importListOfFile = getImportNameList(fileNameWithoutExt)
	for (let importName of importListOfFile) {
		importList.push(importName) // add to the end
		importList = getImportNameListRecursive(importName, importList)
	}
	return importList
}
//----------------------------------------------------------------------------
function wordIsReserved(word) {
    return word.match(new RegExp("\\b("+
        "accept_on|alias|always|always_comb|always_ff|always_latch|and|assert|assign"+
        "|assume|automatic|before|begin|bind|bins|binsof|bit|break|buf|bufif0|bufif1"+
        "|byte|case|casex|casez|cell|chandle|checker|class|clocking|cmos|config|const"+
        "|constraint|context|continue|cover|covergroup|coverpoint|cross|deassign|default"+
        "|defparam|design|disable|dist|do|edge|else|end|endcase|endchecker|endclass|endclocking"+
        "|endconfig|endfunction|endgenerate|endgroup|endinterface|endmodule|endpackage|endprimitive"+
        "|endprogram|endproperty|endspecify|endsequence|endtable|endtask|enum|event|eventually"+
        "|expect|export|extends|extern|final|first_match|for|force|foreach|forever|fork|forkjoin"+
        "|function|generate|genvar|global|highz0|highz1|if|iff|ifnone|ignore_bins|illegal_bins"+
        "|implements|implies|import|incdir|include|initial|inout|input|inside|instance|int|integer"+
        "|interconnect|interface|intersect|join|join_any|join_none|large|let|liblist|library|local"+
        "|localparam|logic|longint|macromodule|matches|medium|modport|module|nand|negedge|nettype"+
        "|new|nexttime|nmos|nor|noshowcancelled|not|notif0|notif1|null|or|output|package|packed"+
        "|parameter|pmos|posedge|primitive|priority|program|property|protected|pull0|pull1|pulldown"+
        "|pullup|pulsestyle_ondetect|pulsestyle_onevent|pure|rand|randc|randcase|randsequence"+
        "|rcmos|real|realtime|ref|reg|reject_on|release|repeat|restrict|return|rnmos|rpmos|rtran"+
        "|rtranif0|rtranif1|s_always|s_eventually|s_nexttime|s_until|s_until_with|scalared|sequence"+
        "|shortint|shortreal|showcancelled|signed|small|soft|solve|specify|specparam|static|string"+
        "|strong|strong0|strong1|struct|super|supply0|supply1|sync_accept_on|sync_reject_on|table"+
        "|tagged|task|this|throughout|time|timeprecision|timeunit|tran|tranif0|tranif1|tri|tri0|tri1"+
        "|triand|trior|trireg|type|typedef|union|unique|unique0|unsigned|until|until_with|untyped|use"+
        "|uwire|var|vectored|virtual|void|wait|wait_order|wand|weak|weak0|weak1|while|wildcard|wire|with"+
        "|within|wor|xnor|xor)\\b"))
}

//----------------------------------------------------------------------------
function wordIsNumber(word) {
    return word.match(/\b\d+/)
}


//----------------------------------------------------------------------------
// use a match function to see if sucessfull in ALL file
// matchInFileObj.path = file path
// matchInFileObj.text = fileText
// matchInFileObj.match = MatchAll object from regEx
// matchInFileObj.fileNameWithoutExt = fileNameWithoutExt
function getMatchInAllFile(funcMatch) {
	let fileNameWithoutExtList = getFilePath().map(x => filePathToFileNameWithoutExt(x))
	let matchInFileObjList = []
	for (let fileNameWithoutExt of fileNameWithoutExtList) {
        let matchInFileObj = getMatchInFile(fileNameWithoutExt, funcMatch)
		if(matchInFileObj) matchInFileObjList.push(matchInFileObj)
	}
	return matchInFileObjList
}

//----------------------------------------------------------------------------
// use a match function to see if sucessfull in file or in import of this file
// matchInFileObj.path = file path
// matchInFileObj.text = fileText
// matchInFileObj.match = MatchAll object from regEx
// matchInFileObj.fileNameWithoutExt = fileNameWithoutExt
function getMatchInFileOrImport(fileNameWithoutExt, funcMatch) {
	let matchInFileObj = getMatchInFile(fileNameWithoutExt, funcMatch)
	if(matchInFileObj) return matchInFileObj
	matchInFileObj = getMatchInImport(fileNameWithoutExt, funcMatch)
	if(matchInFileObj) return matchInFileObj
}

//----------------------------------------------------------------------------
// use a match function to see if sucessfull in the file
// if MATCH => return fileTextObj that containt .path .text .fileNameWithoutExt .match
function getMatchInFile(fileNameWithoutExt, funcMatch) {
	let fileTextObj = getFileText(fileNameWithoutExt)
	fileTextObj.match = funcMatch(fileTextObj.text)
	if(fileTextObj.match.length) return fileTextObj
}

//----------------------------------------------------------------------------
// check in the import of the file if there a match using a match function
function getMatchInImport(fileNameWithoutExt, funcMatch) {
	for (let importfileNameWithoutExt of getImportNameList(fileNameWithoutExt)) {
		let matchInFileObj = getMatchInFile(importfileNameWithoutExt, funcMatch)
		if(matchInFileObj) return matchInFileObj
	}
}

//----------------------------------------------------------------------------
module.exports = {
    replaceCommentWithSpace,
    getFilePath,
    getFileText,
	uriToFileNameWithoutExt,
	filePathToFileNameWithoutExt,
	indexToPosition,
	wordIsNumber,
	wordIsReserved,
	getMatchInFileOrImport,
	getMatchInAllFile,
	getImportNameListInOrder,
}

//----------------------------------------------------------------------------
// Catch to see the error
// function tryCatch = (func) => {
// 	return (...restArgs) => {
// 		try{
// 			return func(...restArgs)
// 		} catch (error) {
// 			console.error(`>> ${error}`)
// 			// console.trace()
// 			throw("Fuck off")
// 		}
// 	}
// }
