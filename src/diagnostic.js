//----------------------------------------------------------------------------
// Contains function to flag error in text
//----------------------------------------------------------------------------
const vscode = require('vscode')
const fs = require('fs')
const os = require("os")
const child_process = require('child_process');
const path = require('path');
const utils = require('./utils')
const ouputChannel = require('./ouputChannel')

//----------------------------------------------------------------------------
const collection = vscode.languages.createDiagnosticCollection('nik');
const tempDir = os.tmpdir().replace(/\\/g,"/")
const tempWorkDir = tempDir + "/work"
const workspaceFolder = vscode.workspace.workspaceFolders[0].uri.fsPath.replace(/\\/g,"/")
const incdirStr = `+incdir+${workspaceFolder}/` + vscode.workspace.getConfiguration('nik').get("incdir", []).join(` +incdir+${workspaceFolder}/`)

//----------------------------------------------------------------------------
// Save activeTextEditor text in file
// search activeTextEditor dependancy
// create and execute vlog cmd
// Extract info from cmd stdout
// Add error wave
async function updateDiagnostic() {
    console.log("Diagnostic")
	if(!vscode.window.activeTextEditor || !vscode.languages.match('systemverilog', vscode.window.activeTextEditor.document)) return
	await utils.getFileText() // init
	if(fs.existsSync(tempWorkDir)) fs.rmdirSync(tempWorkDir, { recursive: true })

	let fileNameWithoutExt = utils.uriToFileNameWithoutExt(vscode.window.activeTextEditor.document.uri)
    let tempFilePath = tempDir + `/${fileNameWithoutExt}.sv`
    await saveCurrentTextToTemporayFile(fileNameWithoutExt, tempFilePath)
    let fileStr = await getCompilationFileList(fileNameWithoutExt, tempFilePath)
	let filePath = vscode.window.activeTextEditor.document.uri.fsPath.replace(/\\/g,"/")
	let fileDir = path.dirname(filePath)
	let cmdStr = `vlog -quiet -warning error -svinputport=relaxed -lint=default -suppress 2181,7061,2254 +incdir+${fileDir} ${incdirStr} -work ${tempWorkDir} ${fileStr}`
	ouputChannel.log(cmdStr)

	child_process.exec(cmdStr, async (error, stdout, stderr) => {
		if(error) {
		    ouputChannel.log(stdout)
			let msg, line
			try {
				let firstErrorInfo = getFirstErrorInfo(stdout, filePath)
				msg = firstErrorInfo.msg
				if(firstErrorInfo.fileNameWithoutExt != fileNameWithoutExt) {
					let txt = (await utils.getFileText(fileNameWithoutExt)).text
					let index = txt.match(new RegExp(`\\b${firstErrorInfo.fileNameWithoutExt}::`)).index
					line = utils.indexToPosition(txt, index).line
				} else {
					line = firstErrorInfo.line
				}
			} catch (error) {
				ouputChannel.log(`CRASH: ${error}`)
				msg = stdout
				line = 0
			}


			collection.set(vscode.window.activeTextEditor.document.uri, [new vscode.Diagnostic(
                new vscode.Range(new vscode.Position(line, 0), new vscode.Position(line, 999)),
                msg,
                vscode.DiagnosticSeverity.Error
            )])
		} else {
			ouputChannel.log("no error!\n");
			collection.clear();
		}
	})
}

//----------------------------------------------------------------------------
async function saveCurrentTextToTemporayFile(fileNameWithoutExt, tempFilePath) {
    let text = (await utils.getFileText(fileNameWithoutExt)).text
	fs.writeFileSync(tempFilePath, text)
}

//----------------------------------------------------------------------------
async function getCompilationFileList(fileNameWithoutExt, tempFilePath) {
    let importNameList = await utils.getImportNameListRecursive(fileNameWithoutExt)
	importNameList.reverse()
	let fileStr = ""
	for (let fileNameWithoutExtList of importNameList)
		fileStr += await utils.getFilePath(fileNameWithoutExtList) + " "
	fileStr += tempFilePath
    return fileStr
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
module.exports = {
	updateDiagnostic
}

// ** Error (suppressible): c:/Users/common/pkg/cbdma_pkg.sv(214): (vlog-13233) Design unit "cbdma_pkg_sv_unit" already exists and will be overwritten. Overwriting SystemVerilog $unit with different source files.