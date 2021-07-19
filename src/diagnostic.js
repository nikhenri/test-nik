//----------------------------------------------------------------------------
// Contains function to flag error in text
//----------------------------------------------------------------------------
const vscode = require('vscode')
const fs = require('fs')
const os = require("os")
const child_process = require('child_process')
const path = require('path')
const utils = require('./utils')
const ouputChannel = require('./ouputChannel')

//----------------------------------------------------------------------------
const collection = vscode.languages.createDiagnosticCollection('nik')
const tempDir = os.tmpdir().replace(/\\/g,"/")

//----------------------------------------------------------------------------
// Save activeTextEditor text in file
// search activeTextEditor dependancy
// create and execute vlog cmd
// Extract info from cmd stdout
// Add error wave
function updateDiagnostic() {
    if(path.parse(vscode.window.activeTextEditor.document.uri.fsPath).ext == ".svh") return

    ouputChannel.log("Diagnostic")
    utils.getFileText() // init
    let fileNameWithoutExt = utils.uriToFileNameWithoutExt(vscode.window.activeTextEditor.document.uri)

    fs.mkdtemp(tempDir + '/work_', (err, directory) => {
        saveCurrentTextToTemporayFile(fileNameWithoutExt, directory)
        let cmdStr = getCompilationCommand(fileNameWithoutExt, directory)
        child_process.exec(cmdStr, (error, stdout) => {compilationCommandCallback(fileNameWithoutExt, directory, error, stdout)})
    })
}

//----------------------------------------------------------------------------
// save the current live text in order to compile it
function saveCurrentTextToTemporayFile(fileNameWithoutExt, directory) {
    let tempFilePath = getTempFilePath(fileNameWithoutExt, directory)
    let text = utils.getFileText(fileNameWithoutExt).text
    fs.writeFileSync(tempFilePath, text)
}

//----------------------------------------------------------------------------
function getTempFilePath (fileNameWithoutExt, directory) {
    return directory + `/${fileNameWithoutExt}.sv`
}

//----------------------------------------------------------------------------
// get the vlog command to run in order to compile the file with pkg
function getCompilationCommand (fileNameWithoutExt, directory) {
    let fileDir = path.dirname(vscode.window.activeTextEditor.document.uri.fsPath).replace(/\\/g,"/")
    let incdirStr = getIncdirStrFromSettings()
    let fileStr = getCompilationFileList(fileNameWithoutExt, directory)
    let cmdStr = `vlog -quiet -warning error -svinputport=relaxed -lint=default -suppress 2181,7061,2254 -work ${directory} +incdir+${fileDir} ${incdirStr} ${fileStr}`
    ouputChannel.log(cmdStr)
    return cmdStr
}
//----------------------------------------------------------------------------
// get the string in order of the file that need to be compiled (pkg first)
function getCompilationFileList(fileNameWithoutExt, directory) {
    let tempFilePath = getTempFilePath(fileNameWithoutExt, directory)
    let importNameList = utils.getImportNameListInOrder(fileNameWithoutExt)
    let fileStr = ""
    for (let fileNameWithoutExtList of importNameList)
        fileStr += utils.getFilePath(fileNameWithoutExtList) + " "
    fileStr += tempFilePath
    return fileStr
}

//----------------------------------------------------------------------------
// load the path put by the user, load once
function getIncdirStrFromSettings() {
    if(!getIncdirStrFromSettings.incdirStr) {
        let workspaceFolder = vscode.workspace.workspaceFolders[0].uri.fsPath.replace(/\\/g,"/")
        let incdirList = vscode.workspace.getConfiguration('nik').get("incdir")
        if(incdirList)
            getIncdirStrFromSettings.incdirStr = `+incdir+${workspaceFolder}/` + incdirList.join(` +incdir+${workspaceFolder}/`)
        else
            getIncdirStrFromSettings.incdirStr = ""
    }
    // console.log(`incdirStr: ${incdirStr}`)
    return getIncdirStrFromSettings.incdirStr
}

//----------------------------------------------------------------------------
// The function call after the compilation is done, analyse stdout and add/remove error
function compilationCommandCallback(fileNameWithoutExt, directory, error, stdout) {
    fs.rmdir(directory, { recursive: true }, ()=>{})
    if(error) {
        ouputChannel.log(stdout)
        let {line, msg} = getLineAndMsgFromStdout(stdout, fileNameWithoutExt)
        addErrorOnActiveTextEditor(line, msg)
    } else {
        ouputChannel.log("no error!\n")
        removeErrorOnActiveTextEditor()
    }
}

//----------------------------------------------------------------------------
// from the stdout get the where (line) and what (msg) to display as error
function getLineAndMsgFromStdout(stdout, fileNameWithoutExt) {
    let line, msg
    try {
        let firstErrorInfo = getFirstErrorInfo(stdout)
        msg = firstErrorInfo.msg
        if(firstErrorInfo.fileNameWithoutExt != fileNameWithoutExt) { // if from import file
            line = getImportLine(fileNameWithoutExt, firstErrorInfo.fileNameWithoutExt)
        } else { // error is in current file
            line = firstErrorInfo.line
        }

    } catch (error) {
        ouputChannel.log(`CRASH: ${error}`)
        msg = error
        line = 0
    }
    return {line, msg}
}
//----------------------------------------------------------------------------
// ** Error: C:/Users/nhenri/AppData/Local/Temp/tcp_regs.sv(478): (vlog-2730) Undefined variable: 'vg_Read_Datas'.
// ** Error: (vlog-13069) C:/Users/nhenri/AppData/Local/Temp/tcp_regs.sv(32): near "input": syntax error, unexpected input, expecting ')'.
// ** Error (suppressible): C:/Users/nhenri/AppData/Local/Temp/tcp_regs.sv(226): (vlog-2623) Undefined variable: i_cfg_axi_aclk_p.
function getFirstErrorInfo(text) {
    let matchAll = Array.from(text.matchAll(/\*\* Error.*?:.*? ([^(]*)\((\d+)\): (?:\(.*?\) )?(.*)/g))
    let fileNameWithoutExt = utils.filePathToFileNameWithoutExt(matchAll[0][1])
    let line = parseInt(matchAll[0][2])-1
    let msg = matchAll[0][3]
    return {line, msg, fileNameWithoutExt}
}

//----------------------------------------------------------------------------
// found the import:: line in a file
function getImportLine(fileNameWithoutExt, importName) {
    let txt = utils.getFileText(fileNameWithoutExt).text
    let index = txt.match(new RegExp(`\\b${importName}::`)).index //seatch import
    let line = utils.indexToPosition(txt, index).line
    return line
}
//----------------------------------------------------------------------------
// add error wave to text
function addErrorOnActiveTextEditor (line, msg) {
    collection.set(vscode.window.activeTextEditor.document.uri, [new vscode.Diagnostic(
        new vscode.Range(new vscode.Position(line, 0), new vscode.Position(line, 999)),
        msg,
        vscode.DiagnosticSeverity.Error
    )])
}

//----------------------------------------------------------------------------
// add error wave to text
function removeErrorOnActiveTextEditor () {
    collection.delete(vscode.window.activeTextEditor.document.uri)
}

//----------------------------------------------------------------------------
module.exports = {
    updateDiagnostic
}
