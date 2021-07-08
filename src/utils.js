//----------------------------------------------------------------------------
// Contains function that need to be share accross multiple files
//----------------------------------------------------------------------------
const vscode = require('vscode')
const path = require('path')
const fs = require('fs')

//----------------------------------------------------------------------------
// Catch to see the error
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
// const tryCatchAsync = (func) => {
// 	return (...restArgs) => {
// 		func(...restArgs).
// 		then((ret)=>{
// 			console.log(ret)
// 			return ret
// 		}).catch((error) => {
// 			console.error(`>> ${error}`)
// 			// console.trace()
// 			throw("Fuck off")
// 		})
// 	}
// }

//----------------------------------------------------------------------------
// Remplace all comment by space so regex are easier to do
const replaceCommentWithSpace = (text) => {
	return text.replace(/\/\*[\s\S]*?\*\/|\/\/.*|/g, (match) => {
		return " ".repeat(match.length)
	})
}

//----------------------------------------------------------------------------
// Will search all file that have the name 'fileNameWithoutExt' with extension .sv or .v
// Ex: toto => return C:/something/toto.sv
// If 'fileNameWithoutExt' is false, will return a list of all the file with extension .sv or .v
const getFilePath = async (fileNameWithoutExt)=> {
	let filePath
	let search_fileNameWithoutExt = (x=> path.parse(x).name == fileNameWithoutExt) // find function
	// If the list is not initialized OR we want all file OR the file is not found in list
	if(!getFilePath.listOfPath || !fileNameWithoutExt || !(filePath = getFilePath.listOfPath.find(search_fileNameWithoutExt))) {
		console.log(`Updating findFiles for ${fileNameWithoutExt}...`)
        let finFiles = await vscode.workspace.findFiles("**/*.{v,sv}") //get URI of all file
		getFilePath.listOfPath = finFiles.map(x => x.fsPath.replace(/\\/g,"/")) //keep only the path

		if (fileNameWithoutExt) //if we want a specific file
			filePath = getFilePath.listOfPath.find(search_fileNameWithoutExt)
		else // if we want all file
			filePath = getFilePath.listOfPath
    }
	if(!filePath) console.log(`Was not able to found '${fileNameWithoutExt}'`)
	return filePath
}

//----------------------------------------------------------------------------
// Get the text comment removed in a file, based on the fileNameWithoutExt
// This function will save the text in memory
// So the next call for same file will return the previous read value
// Calling the fct without parameter clear the memory
const getFileText = async (fileNameWithoutExt) => {
	if(!fileNameWithoutExt ) { // clear memory
		getFileText.textObj = {}
		return
	} else if (!getFileText.textObj)
		throw("getFileText need to be init")

	if(!(fileNameWithoutExt in getFileText.textObj)) { // not already read
		let path = await getFilePath(fileNameWithoutExt)
    	let text = replaceCommentWithSpace(fs.readFileSync(path, 'utf8'))
		getFileText.textObj[fileNameWithoutExt] = {path, text, fileNameWithoutExt} //save for future call
	}

	return getFileText.textObj[fileNameWithoutExt];
}

//----------------------------------------------------------------------------
const uriToFileNameWithoutExt = (uri) => {
	return filePathToFileNameWithoutExt(uri.fsPath)
}
//----------------------------------------------------------------------------
const filePathToFileNameWithoutExt = (filePath) => {
	return path.parse(filePath).name
}
//----------------------------------------------------------------------------
// Get a index/offset caracter, convert into line/char
const indexToPosition = (text, index) => {
	let lineSplit = text.substr(0, index).split(/\r\n|\n/)
	let line = lineSplit.length - 1
	let char = lineSplit[lineSplit.length - 1].length
	return new vscode.Position(line, char)
}
//----------------------------------------------------------------------------
// return a name of import use in file (import oti_header_pkg::*; => return oti_header_pkg)
const getImportNameList = async (fileNameWithoutExt) => {
	let text = (await getFileText(fileNameWithoutExt)).text
	let matchAll = Array.from(text.matchAll(/(\w+)::\*/gm))
	if (matchAll.length) {
		return  matchAll.map(x => x[1]).filter(x=> x != fileNameWithoutExt)
	}
	return matchAll
}
//----------------------------------------------------------------------------
const getImportNameListRecursive = async (fileNameWithoutExt, importList = []) => {
	// console.log(`Inspecting ${fileNameWithoutExt}`)
	let importListOfFile = await getImportNameList(fileNameWithoutExt)
	for (let importName of importListOfFile) {
		let index = importList.findIndex(x => x == importName)
		importList.push(importName) // add to the end
		if(index == -1) { // if we have not scanned this yet
			importList = await getImportNameListRecursive(importName, importList)
		} else {
			// console.log(`Skip ${importName}`)
			importList.splice(index, index) //remove duplicate
		}
	}
	return importList
}
//----------------------------------------------------------------------------
const wordIsReserved = (word) => {
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
const wordIsNumber = (word) => {
    return word.match(/\b\d+/)
}


//----------------------------------------------------------------------------
// use a match function to see if sucessfull in ALL file
// matchInFileObj.path = file path
// matchInFileObj.text = fileText
// matchInFileObj.match = MatchAll object from regEx
// matchInFileObj.fileNameWithoutExt = fileNameWithoutExt
const getMatchInAllFile = async (funcMatch) => {
	let fileNameWithoutExtList = (await getFilePath()).map(x => filePathToFileNameWithoutExt(x))
	let matchInFileObjList = []
	for (let fileNameWithoutExt of fileNameWithoutExtList) {
        let matchInFileObj = await getMatchInFile(fileNameWithoutExt, funcMatch)
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
const getMatchInFileOrImport = async (fileNameWithoutExt, funcMatch) => {
	let matchInFileObj = await getMatchInFile(fileNameWithoutExt, funcMatch)
	if(matchInFileObj) return matchInFileObj
	matchInFileObj = await getMatchInImport(fileNameWithoutExt, funcMatch)
	if(matchInFileObj) return matchInFileObj
}

//----------------------------------------------------------------------------
// use a match function to see if sucessfull in the file
// if MATCH => return fileTextObj that containt .path .text .fileNameWithoutExt .match
const getMatchInFile = async (fileNameWithoutExt, funcMatch) => {
	let fileTextObj = await getFileText(fileNameWithoutExt)
	fileTextObj.match = funcMatch(fileTextObj.text)
	if(fileTextObj.match.length) return fileTextObj
}

//----------------------------------------------------------------------------
// check in the import of the file if there a match using a match function
const getMatchInImport = async (fileNameWithoutExt, funcMatch) => {
	for (let importfileNameWithoutExt of await getImportNameList(fileNameWithoutExt)) {
		let matchInFileObj = await getMatchInFile(importfileNameWithoutExt, funcMatch)
		if(matchInFileObj) return matchInFileObj
	}
}

//----------------------------------------------------------------------------
module.exports = {
    tryCatch,
    replaceCommentWithSpace,
    getFilePath,
    getFileText,
	uriToFileNameWithoutExt,
	indexToPosition,
	wordIsNumber,
	wordIsReserved,
	getMatchInFileOrImport,
	getMatchInAllFile,
	getImportNameListRecursive,
};