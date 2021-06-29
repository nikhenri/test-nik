const vscode = require('vscode')
const utils = require('./utils')

//----------------------------------------------------------------------------
const provideTerminalLinks = utils.tryCatch((context, token) => {
    console.log(`Terminal line: ${context.line}`)
	// #    Time: 0 fs  Iteration: 0  Instance: /tcp_dma_tb/DUT/qmngr_top/local_pointers_if File: C:/src/queue_manager/src/qmngr_top.sv Line: 451
	let matchArray = Array.from(context.line.matchAll(new RegExp(`([^ ]+) Line: (\\d+)`, "g")))
	if (matchArray.length) {
		return [{startIndex: matchArray[0].index,
			     length: matchArray[0][0].length, // + " Line: "
				 uri: vscode.Uri.file(matchArray[0][1]),
				 line: matchArray[0][2]}]
	}
})
//----------------------------------------------------------------------------
const handleTerminalLink = utils.tryCatch((link) => {
    console.log(`link: ${JSON.stringify(link)}`)
	let pos = new vscode.Position(parseInt(link.line) - 1, 0)
    vscode.workspace.openTextDocument(link.uri)
	.then((doc) => vscode.window.showTextDocument(doc, {selection: new vscode.Range(pos, pos)}))
})

//----------------------------------------------------------------------------
module.exports = {
	provideTerminalLinks,
	handleTerminalLink,
}