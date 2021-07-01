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
		//console.log(`Reading '${path}'`)
    	let text = replaceCommentWithSpace(fs.readFileSync(path, 'utf8'))
		getFileText.textObj[fileNameWithoutExt] = { path, text }
	}

	return getFileText.textObj[fileNameWithoutExt];
}

//----------------------------------------------------------------------------
const uriToFileNameWithoutExt = tryCatch((uri) => {
	return filePathToFileNameWithoutExt(uri.fsPath)
})
//----------------------------------------------------------------------------
const filePathToFileNameWithoutExt = tryCatch((filePath) => {
	return path.parse(filePath).name
})
//----------------------------------------------------------------------------
const indexToPosition = tryCatch((text, index) => {
	let lineSplit = text.substr(0, index).split(/\r\n|\n/)
	let line = lineSplit.length - 1
	let char = lineSplit[lineSplit.length - 1].length
	return new vscode.Position(line, char)
})
//----------------------------------------------------------------------------
const getImportNameList = tryCatch((text) => {
	let matchAll = Array.from(text.matchAll(/(\w+)::\*/gm))
	if (matchAll.length) return  matchAll.map(x => x[1])
	return matchAll
})
//----------------------------------------------------------------------------
//----------------------------------------------------------------------------
const wordIsReserved = tryCatch((word) => {
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
})

//----------------------------------------------------------------------------
const wordIsNumber = tryCatch((word) => {
    return word.match(/\b\d+/)
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
	filePathToFileNameWithoutExt,
	getImportNameList,
	wordIsNumber,
	wordIsReserved
};