//----------------------------------------------------------------------------
// Function to do the completion after the '.'
//----------------------------------------------------------------------------
const vscode = require('vscode')
const utils = require('./utils')
const ouputChannel = require('./ouputChannel')

//----------------------------------------------------------------------------
function provideCompletionItems(document){
	let documentWithoutComment = utils.removeComment(document.getText())

	let allPort
	let allVariable = []
	let matchAllModule = Array.from(documentWithoutComment.matchAll(/^[ ]*(module\s+[\s\S]*?\)\s*;)([\s\S]*^\s*endmodule\b)/gm))
	if(matchAllModule.length) {
		let entityDeclaration = matchAllModule[0][1];
		let architectureDeclaration = matchAllModule[0][2];

		allPort = Array.from(entityDeclaration.matchAll(/^\s*(?:parameter|input|output|inout)\s+\w*?\s*(?:\[.*?\]\s*)*(\w+)\s*(?:\[.*?\]\s*)*(?:=.*)?(?:,|\s*\))/gm)).map(x=>x[1])

		// let matchAllvariableDeclaration = Array.from(architectureDeclaration.matchAll(/^[ ]*(?:type\b.*?\)|\w+|enum\b[\s\S]*?}|struct\b[\s\S]*?})(?:\s*\[.*?\]\s*)*[ ]+(?:\s*\w+\s*(?:=.*?)?(?:,|;)\s*?)+/gm))
		let matchAllvariableDeclaration = Array.from(architectureDeclaration.matchAll(/^[ ]*(?:type\b.*?\)|\w+)(?:\s*\[.*?\]\s*)*[ ]+(?:\s*\w+\s*(?:=.*?)?(?:,|;)\s*?)+/gm))

		for (let match of matchAllvariableDeclaration) {
			//let enums_struct = Array.from(match[0].matchAll(/\.*}\s*(\w+)/g))
			//if (enums_struct.length) {
			//	allVariable.push(enums_struct[0][1])
			//} else {
				let variableName = Array.from(match[0].matchAll(/(\w+)\s*(?:=.*?)?\s*(?:,|;)/g)).map(x=>x[1])
				allVariable.push(...variableName)
			//}
		}
	}
	let completionArray =[...allPort.map(x=>new vscode.CompletionItem(x, vscode.CompletionItemKind.Class)),
		                  ...allVariable.map(x=>new vscode.CompletionItem(x, vscode.CompletionItemKind.Variable))]
	return completionArray
}

//----------------------------------------------------------------------------
module.exports = {
	provideCompletionItems,
}
