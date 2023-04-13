//----------------------------------------------------------------------------
// Function to do the completion for port and variable
//----------------------------------------------------------------------------
const vscode = require('vscode')
const utils = require('./utils')
const ouputChannel = require('./ouputChannel')

//----------------------------------------------------------------------------
function provideCompletionItemsVariable(document){
	return utils.tryCatch(__provideCompletionItemsVariable, document)
}

//----------------------------------------------------------------------------
function __provideCompletionItemsVariable(document){
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
	let matchAll = Array.from(text.matchAll(/module\s+.*?[;#]\s*\(\s*(.*)\)\s*;/gms)) // get all parameter and io
	if(!matchAll.length) return [] //no IO or parameter detected
	let parameter_and_io_list = matchAll[0][1].split(/\r?\n/) //split in line

	let nameDescArray = []
	for (let match of parameter_and_io_list) { //each line
		match = match.replace(/\s+/gm, " ").trim() // remove duplicate space + trim

		let description = match.replace(/\s*(=.*)/gm, "") // remove = ...
		description = description.replace(/\s*,/gm, "") // remove ,
		let not_bracket = description.replace(/\[.*?\]/gm, "") // remove []
		matchAll = Array.from(not_bracket.matchAll(/(\w+)\s*$/gm))
		if(matchAll.length) {
			let name = matchAll[0][1]
			nameDescArray.push({label:name, description})
		}
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
// bit [$clog2(SIZE)-1:0] a = 0, b; [UNSUPPORTED]
// bit [$clog2(SIZE)-1:0] a = 0;
// bit [$clog2(SIZE)-1:0][3:0] a [1:0];
// bit [$clog2(SIZE)-1:0] [3:0] a [1:0];
// bit [$clog2(SIZE)-1:0] [3:0] a [1:0][3:0];
// type(woof)  b;
function getAllSignalLabelDescFromArchitecture(text) {
	let matchAllvariableLineDeclaration = Array.from(text.matchAll(/^[ ]*(?!\bassign\b|\balways_comb\b)(type\b.*?\)|\w+)[ ]*(\[.*\])*[ ]+(\w[a-zA-Z_0-9, ]*)(\[.*\])*(?:=.*)?[ ]*;/gm))
	let nameDescArray = []
	for (let variableLineDeclaration of matchAllvariableLineDeclaration) { //extract all variable separate by ,
		let type = variableLineDeclaration[1]
		let urange = variableLineDeclaration[2]
		let names = variableLineDeclaration[3]
		let prange = variableLineDeclaration[4]

		let description = type
		if(urange)
			description += ` ${urange.replace(/\s+/, '')}`
		if(prange)
			description += ` x ${prange.replace(/\s+/, '')}`

		let allVariableNameInLine = names.split(',').map(x=>x.trim())
		for (let name of allVariableNameInLine) {
			nameDescArray.push({label:name, description:description})
		}
	}
	return nameDescArray
}

//----------------------------------------------------------------------------
module.exports = {
	provideCompletionItemsVariable,
}

//----------------------------------------------------------------------------
// also get struct {} and enum {}
// let matchAllvariableDeclaration = Array.from(architectureDeclaration.matchAll(/^[ ]*(?:type\b.*?\)|\w+|enum\b[\s\S]*?}|struct\b[\s\S]*?})(?:\s*\[.*?\]\s*)*[ ]+(?:\s*\w+\s*(?:=.*?)?(?:,|;)\s*?)+/gm))

// extract type from enum/struct, do we need to support ',' ???
//let enums_struct = Array.from(match[0].matchAll(/\.*}\s*(\w+)/g))
//if (enums_struct.length) {
//	allVariable.push(enums_struct[0][1])
