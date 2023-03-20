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
function updateDiagnostic() {
    return utils.tryCatch(__updateDiagnostic)
}

//----------------------------------------------------------------------------
// Save activeTextEditor text in file
// search activeTextEditor dependancy
// create and execute vlog cmd
// Extract info from cmd stdout
// Add error wave
function __updateDiagnostic() {

    let uri = vscode.window.activeTextEditor.document.uri //Save value before it change
    if(uri.scheme != 'file') return
    if(path.parse(uri.fsPath).ext == ".svh") return

    utils.getFileText() // init
    let fileNameWithoutExt = utils.uriToFileNameWithoutExt(uri)
    let fileNameExt = path.parse(uri.fsPath).ext

    fs.mkdtemp(tempDir + '/work_', (err, directory) => {
        saveCurrentTextToTemporayFile(fileNameWithoutExt, fileNameExt, directory)
        let cmdStr = getCompilationCommand(fileNameWithoutExt, fileNameExt, directory, uri)
        child_process.exec(cmdStr, (error, stdout) => {compilationCommandCallback(uri, fileNameWithoutExt, directory, error, stdout)})
    })
}

//----------------------------------------------------------------------------
// save the current live text in order to compile it
function saveCurrentTextToTemporayFile(fileNameWithoutExt, fileNameExt, directory) {
    let tempFilePath = getTempFilePath(fileNameWithoutExt, fileNameExt, directory)
    let text = utils.getFileText(fileNameWithoutExt).text
    fs.writeFileSync(tempFilePath, text)
}

//----------------------------------------------------------------------------
function getTempFilePath (fileNameWithoutExt, fileNameExt, directory) {
    return directory + `/${fileNameWithoutExt}${fileNameExt}`
}

//----------------------------------------------------------------------------
// get the vlog command to run in order to compile the file with pkg
function getCompilationCommand (fileNameWithoutExt, fileNameExt, directory, uri) {
    let fileDir = path.dirname(uri.fsPath).replace(/\\/g,"/")
    // let incdirStr = getIncdirStrFromSettings()
    let fileStr = getCompilationFileList(fileNameWithoutExt, fileNameExt, directory)

    let cmdStr = `vlog -quiet -warning error -svinputport=relaxed -lint=default +incdir+${fileDir} -work ${directory} ${vscode.workspace.getConfiguration('nik').get("vlog_arg") || ""} ${fileStr}`
    ouputChannel.log(cmdStr)
    return cmdStr
}
//----------------------------------------------------------------------------
// get the string in order of the file that need to be compiled (pkg first)
function getCompilationFileList(fileNameWithoutExt, fileNameExt, directory) {
    let tempFilePath = getTempFilePath(fileNameWithoutExt, fileNameExt, directory)
    let importNameList = utils.getImportNameListInOrder(fileNameWithoutExt)
    let fileStr = ""
    for (let fileNameWithoutExtList of importNameList)
        fileStr += utils.getFilePath(fileNameWithoutExtList) + " "
    fileStr += tempFilePath
    return fileStr
}

//----------------------------------------------------------------------------
// load the path put by the user, load once
// function getIncdirStrFromSettings() {
//     if(!getIncdirStrFromSettings.incdirStr) {
//         let workspaceFolder = vscode.workspace.workspaceFolders[0].uri.fsPath.replace(/\\/g,"/")
//         let incdirList = vscode.workspace.getConfiguration('nik').get("incdir")
//         if(incdirList)
//             getIncdirStrFromSettings.incdirStr = `+incdir+${workspaceFolder}/` + incdirList.join(` +incdir+${workspaceFolder}/`)
//         else
//             getIncdirStrFromSettings.incdirStr = ""
//     }
//     // console.log(`incdirStr: ${incdirStr}`)
//     return getIncdirStrFromSettings.incdirStr
// }

//----------------------------------------------------------------------------
// The function call after the compilation is done, analyse stdout and add/remove error
function compilationCommandCallback(uri, fileNameWithoutExt, directory, error, stdout) {
    fs.rm(directory, { recursive: true }, ()=>{})
    if(error) {
        ouputChannel.log(stdout)
        let {line, msg} = getLineAndMsgFromStdout(stdout, fileNameWithoutExt)
        addErrorOnActiveTextEditor(uri, line, msg)
    } else {
        ouputChannel.log("no error!\n")
        removeErrorOnActiveTextEditor(uri)
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
        msg = stdout
        line = 0
    }
    return {line, msg}
}

//----------------------------------------------------------------------------
// ** Error: C:/Users/nhenri/AppData/Local/Temp/tcp_regs.sv(478): (vlog-2730) Undefined variable: 'vg_Read_Datas'.
// ** Error: (vlog-13069) C:/Users/nhenri/AppData/Local/Temp/tcp_regs.sv(32): near "input": syntax error, unexpected input, expecting ')'.
// ** Error (suppressible): C:/Users/nhenri/AppData/Local/Temp/tcp_regs.sv(226): (vlog-2623) Undefined variable: i_cfg_axi_aclk_p.
// ** Error: ** while parsing file included at C:/Users/nhenri/AppData/Local/Temp/work_V9UoIP/tcp_dma_tb.sv(2)
//    ** at c:/Users/nhenri/Desktop/tcp_ip_ip__IISTDE-377_txDataOutMux/src/verif/tb/include_list.h(2): (vlib-13006) Could not find the package (uvm_pkg).  Design read will continue, but expect a cascade of errors after this failure.  Furthermore if you experience a vopt-7 error immediately before this error then please check the package names or the library search paths on the command line.
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
function addErrorOnActiveTextEditor (uri, line, msg) {
    collection.set(uri, [new vscode.Diagnostic(
        new vscode.Range(new vscode.Position(line, 0), new vscode.Position(line, 999)),
        msg,
        vscode.DiagnosticSeverity.Error
    )])
}

//----------------------------------------------------------------------------
// add error wave to text
function removeErrorOnActiveTextEditor (uri) {
    collection.delete(uri)
}

//----------------------------------------------------------------------------
module.exports = {
    updateDiagnostic
}
