//----------------------------------------------------------------------------
// Contains function to handle vscode TERMINAL
//----------------------------------------------------------------------------
const vscode = require('vscode')
const ouputChannel = require('./ouputChannel')
const utils = require('./utils')

//----------------------------------------------------------------------------
// We want to clickable link for ModelSim Time print, example:
//   #    Time: 0 fs  Iteration: 0  Instance: /tcp_dma_tb/DUT/qmngr_top/local_pointers_if File: C:/src/queue_manager/src/qmngr_top.sv Line: 451
function provideTerminalLinks(context) {
	return utils.tryCatch(__provideTerminalLinks, context)
}

//----------------------------------------------------------------------------
// We want to clickable link for ModelSim Time print, example:
//   #    Time: 0 fs  Iteration: 0  Instance: /tcp_dma_tb/DUT/qmngr_top/local_pointers_if File: C:/src/queue_manager/src/qmngr_top.sv Line: 451
function __provideTerminalLinks(context) {
  console.log(`Terminal line: ${context.line}`)
	let matchArray = Array.from(context.line.matchAll(/([^ ]+) Line: (\d+)/g))
	if (matchArray.length) {
		return [{startIndex: matchArray[0].index,
			     length: matchArray[0][0].length,
				 uri: vscode.Uri.file(matchArray[0][1]),
				 line: matchArray[0][2]}]
	}
}
//----------------------------------------------------------------------------
// What to we do when the link is clicked
// show document at the right line
function handleTerminalLink(link) {
  return utils.tryCatch(__handleTerminalLink, link)
}

//----------------------------------------------------------------------------
// What to we do when the link is clicked
// show document at the right line
function __handleTerminalLink(link) {
	//console.log(`link: ${JSON.stringify(link)}`)
let pos = new vscode.Position(parseInt(link.line) - 1, 0)
	vscode.workspace.openTextDocument(link.uri)
.then((doc) => vscode.window.showTextDocument(doc, {selection: new vscode.Range(pos, pos)}))
}

//----------------------------------------------------------------------------
module.exports = {
	provideTerminalLinks,
	handleTerminalLink,
}