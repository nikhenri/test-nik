//----------------------------------------------------------------------------
// Function to do the completion for port and variable
//----------------------------------------------------------------------------
const vscode = require('vscode')
const utils = require('./utils')
const ouputChannel = require('./ouputChannel')

//----------------------------------------------------------------------------
function provideCompletionItems(document, position){
	let documentWithoutComment = utils.removeComment(document.getText())
	let entityAndArchObj = getEntityAndArch(documentWithoutComment)
	if(!entityAndArchObj) return

	let allPortName = getAllPortNameFromEntity(entityAndArchObj.entity)
	let allSignalName = getAllSignalNameFromArchitecture(entityAndArchObj.architecture)

	let completionArray =[...allPortName.map(x=>new vscode.CompletionItem(x, vscode.CompletionItemKind.Class)),
		                  ...allSignalName.map(x=>new vscode.CompletionItem(x, vscode.CompletionItemKind.Variable))]
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
// input  logic [16:0] a [1:0],
// input  logic a [1:0],
// input  logic a = 0,
function getAllPortNameFromEntity(text) {
	return Array.from(text.matchAll(/^\s*(?:parameter|input|output|inout)\s+\w*?\s*(?:\[.*?\]\s*)*(\w+)\s*(?:\[.*?\]\s*)*(?:=.*)?(?:,|\s*\))/gm)).map(x=>x[1])
}

//----------------------------------------------------------------------------
// extract all line of declaration, then get all varialbe in the name (,)
//ex: bit                    a;
//ex: bit                    a = 0;
//ex: bit                    a [1:0];
//ex: bit [$clog2(SIZE)-1:0] a [1:0];
//ex: bit [$clog2(SIZE)-1:0] a, b;
//ex: bit [$clog2(SIZE)-1:0] a = 0, b;
function getAllSignalNameFromArchitecture(text) {
	let matchAllvariableLineDeclaration = Array.from(text.matchAll(/^[ ]*(?:type\b.*?\)|\w+)(?:\s*\[.*?\]\s*)*[ ]+(?:\s*\w+\s*(?:=.*?)?(?:,|;)\s*?)+/gm))
	let allSignalNameFromArchitecture = []
	for (let variableLineDeclaration of matchAllvariableLineDeclaration) { //extract all variable separate by ,
		let allVariableNameInLine = Array.from(variableLineDeclaration[0].matchAll(/(\w+)\s*(?:=.*?)?\s*(?:,|;)/g)).map(x=>x[1])
		allSignalNameFromArchitecture.push(...allVariableNameInLine)
	}
	return allSignalNameFromArchitecture
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
