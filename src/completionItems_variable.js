//----------------------------------------------------------------------------
// Function to do the completion for port and variable
//----------------------------------------------------------------------------
const vscode = require('vscode')
const utils = require('./utils')
const ouputChannel = require('./ouputChannel')

//----------------------------------------------------------------------------
function provideCompletionItems(document){
	let documentWithoutComment = utils.removeComment(document.getText())
	let entityAndArchObj = getEntityAndArch(documentWithoutComment)
	if(!entityAndArchObj) return

	let completionArray = []
	for (let labelDescObj of getAllPortLabelDescFromEntity(entityAndArchObj.entity))
		completionArray.push(new vscode.CompletionItem(labelDescObj, vscode.CompletionItemKind.Class))

	for (let labelDescObj of getAllSignalLabelDescFromArchitecture(entityAndArchObj.architecture))
		completionArray.push(new vscode.CompletionItem(labelDescObj, vscode.CompletionItemKind.Variable))

	return completionArray
}

//----------------------------------------------------------------------------
function getEntityAndArch(text) {
	let matchAllModule = Array.from(text.matchAll(/^[ ]*(module\s+[\s\S]*?\)\s*;)([\s\S]*^\s*endmodule\b)/gm))
	if(!matchAllModule.length) return
	return {entity:matchAllModule[0][1], architecture:matchAllModule[0][2]}
}

//----------------------------------------------------------------------------
// parameter a  = 64,
// parameter int a [P_NB_CH-1:0] = {int'(1), int'(7), int'(8)},
// input  a,
// input  logic a,
// input  logic [16:0] a,
// input  logic [16:0][5:0] a,
// input  logic [16:0] a [1:0],
// input  logic a [1:0],
// input  logic a = 0,
function getAllPortLabelDescFromEntity(text) {
	let matchAll = Array.from(text.matchAll(/^\s*(parameter|input|output|inout)\s+(\w*\s+)*\s*(\[.*\]\s*?)*\s*(\w+)\s*(\[.*\]\s*?)*\s*(?:=.*)?(?:,|\s*\))/gm))

	let nameDescArray = []
	for (let match of matchAll) { //extract all variable separate by ,
		let kind = match[1]
		let type = match[2]
		let urange = match[3]
		let name = match[4]
		let prange = match[5]

		let description = kind
		if(type)
			description += ` ${type.trim()}`
		if(urange)
			description += ` ${urange.replace(/\s+/, '')}`
		if(prange)
			description += ` x ${prange.replace(/\s+/, '')}`
			nameDescArray.push({label:name, description})
	}
	return nameDescArray
}

//----------------------------------------------------------------------------
// extract all line of declaration, then get all varialbe in the name (,)
// bit                    a;
// bit                    a = 0;
// bit                    a [1:0];
// bit [$clog2(SIZE)-1:0] a [1:0];
// bit [$clog2(SIZE)-1:0] a, b;
// bit [$clog2(SIZE)-1:0] a = 0, b;
// bit [$clog2(SIZE)-1:0] a = 0,
// bit [$clog2(SIZE)-1:0][3:0] a [1:0];
// bit [$clog2(SIZE)-1:0] [3:0] a [1:0];
//                        b, c [1:0];
// type(woof)  b;
function getAllSignalLabelDescFromArchitecture(text) {
	let matchAllvariableLineDeclaration = Array.from(text.matchAll(/^[ ]*(type\b.*?\)|\w+)[ ]*([ ]*\[.*\][ ]*)*[ ]+([ ]*\w+\s*(\[.*?\])*(?:=.*?)?(,*)\s*?)+;/gm))
	let nameDescArray = []
	for (let variableLineDeclaration of matchAllvariableLineDeclaration) { //extract all variable separate by ,
		let type = variableLineDeclaration[1]
		let urange = variableLineDeclaration[2]
		let prange = variableLineDeclaration[4]

		let description = type
		if(urange)
			description += ` ${urange.replace(/\s+/, '')}`
		if(prange)
			description += ` x ${prange.replace(/\s+/, '')}`

		let allVariableNameInLine = Array.from(variableLineDeclaration[0].matchAll(/(\w+)\s*(?:=.*?)?\s*(?:,|;)/g)).map(x=>x[1])
		for (let name of allVariableNameInLine) {
			nameDescArray.push({label:name, description:description})
		}
	}
	return nameDescArray
}

//----------------------------------------------------------------------------
module.exports = {
	provideCompletionItems,
}

//----------------------------------------------------------------------------
// also get struct {} and enum {}
// let matchAllvariableDeclaration = Array.from(architectureDeclaration.matchAll(/^[ ]*(?:type\b.*?\)|\w+|enum\b[\s\S]*?}|struct\b[\s\S]*?})(?:\s*\[.*?\]\s*)*[ ]+(?:\s*\w+\s*(?:=.*?)?(?:,|;)\s*?)+/gm))

// extract type from enum/struct, do we need to support ',' ???
//let enums_struct = Array.from(match[0].matchAll(/\.*}\s*(\w+)/g))
//if (enums_struct.length) {
//	allVariable.push(enums_struct[0][1])
