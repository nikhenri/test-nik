//----------------------------------------------------------------------------
// Contains function to log in output console
//----------------------------------------------------------------------------
const vscode = require('vscode')

//----------------------------------------------------------------------------
const outputChannel = vscode.window.createOutputChannel("Nik")

//----------------------------------------------------------------------------
function log(text) {
    console.log(text)
    outputChannel.appendLine(text)
}

//----------------------------------------------------------------------------
function error(text) {
    text = `!!! CRASH !!!: ${text}`
    outputChannel.appendLine(text)
    console.log(text)
    vscode.window.showErrorMessage(text)
}
//----------------------------------------------------------------------------
module.exports = {
	log,
    error,
}