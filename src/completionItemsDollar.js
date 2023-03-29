//----------------------------------------------------------------------------
// Function to do the completion after the '$'
//----------------------------------------------------------------------------
const vscode = require('vscode')
const ouputChannel = require('./ouputChannel')
const utils = require('./utils')

const DollarCompletionList = getDollarCompletionList()

//----------------------------------------------------------------------------
function provideCompletionItemsDollar(document, position){
	return utils.tryCatch(__provideCompletionItemsDollar, document, position)
}

//----------------------------------------------------------------------------
function __provideCompletionItemsDollar(document, position){
	let linePrefix = document.lineAt(position).text.substr(0, position.character)
	if (!linePrefix.endsWith('$')) return //avoid trig for nothing
	ouputChannel.log("$")
	return DollarCompletionList
}

//----------------------------------------------------------------------------
function getDollarCompletionList () {
	const systemVerilogFunction = [
		'$finish', '$stop', '$exit', '$realtime', '$stime', '$time', '$printtimescale', '$timeformat', '$bitstoreal', '$realtobits', '$bitstoshortreal', '$shortrealtobits', '$itor', '$rtoi', '$signed', '$unsigned',
		'$cast', '$bits', '$isunbounded', '$typename', '$unpacked_dimensions', '$dimensions', '$left', '$right', '$low', '$high', '$increment', '$size', '$clog2', '$asin', '$ln', '$acos', '$log10','$atan', '$exp',
		'$atan2', '$sqrt', '$hypot', '$pow', '$sinh', '$floor', '$cosh', '$ceil', '$tanh', '$sin', '$asinh', '$cos', '$acosh', '$tan', '$atanh', '$countbits', '$countones', '$onehot', '$onehot0', '$isunknown',
		'$fatal', '$error', '$warning', '$info', '$asserton', '$assertoff', '$assertkill', '$assertcontrol', '$assertpasson', '$assertpassoff', '$assertfailon', '$assertfailoff', '$assertnonvacuouson',
		'$assertvacuousoff', '$sampled', '$rose', '$fell', '$stable', '$changed', '$past', '$past_gclk', '$rose_gclk', '$fell_gclk', '$stable_gclk', '$changed_gclk', '$future_gclk', '$rising_gclk', '$falling_gclk',
		'$steady_gclk', '$changing_gclk', '$coverage_control', '$coverage_get_max', '$coverage_get', '$coverage_merge', '$coverage_save','$get_coverage', '$set_coverage_db_name', '$load_coverage_db', '$random',
		'$dist_chi_square', '$dist_erlang', '$dist_exponential', '$dist_normal', '$dist_poisson', '$dist_t', '$dist_uniform', '$q_initialize',	'$q_add', '$q_remove', '$q_full', '$q_exam', '$system','$display',
    '$write', '$displayb', '$writeb', '$displayh', '$writeh', '$displayo', '$writeo', '$strobe', '$monitor', '$strobeb', '$monitorb', '$strobeh', '$monitorh', '$strobeo', '$monitoro', '$monitoroff', '$monitoron',
    '$fclose', '$fopen', '$fdisplay', '$fwrite', '$fdisplayb', '$fwriteb', '$fdisplayh', '$fwriteh', '$fdisplayo', '$fwriteo', '$fstrobe', '$fmonitor', '$fstrobeb', '$fmonitorb', '$fstrobeh', '$fmonitorh',
		'$fstrobeo', '$fmonitoro', '$swrite', '$sformat', '$swriteb', '$sformatf', '$swriteh', '$fgetc', '$swriteo', '$ungetc', '$fscanf', '$fgets', '$fread', '$sscanf', '$fseek', '$rewind', '$fflush', '$ftell',
		'$feof', '$ferror', '$dumpfile', '$dumpvars', '$dumpoff', '$dumpon', '$dumpall', '$dumplimit', '$dumpflush', '$dumpports', '$dumpportsoff', '$dumpportson', '$dumpportsall', '$dumpportslimit', '$dumpportsflush',
		'$writememb', '$writememh', '$readmemb', '$readmemh', '$test$plusargs', '$value$plusargs'
	]
	let list = []
	systemVerilogFunction.forEach((item, index) => {
		list[index] = new vscode.CompletionItem(item, vscode.CompletionItemKind.Function)
		list[index].insertText = item.substr(1)
	})
	return list
}

//----------------------------------------------------------------------------
module.exports = {
	provideCompletionItemsDollar,
}
