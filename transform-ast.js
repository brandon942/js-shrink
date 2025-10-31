const acorn = require('acorn')
/** @import {Node, Options as ParserOptions} from 'acorn' */
var MagicStringModule = require('magic-string')
var MagicString = MagicStringModule.default
/** @import { SourceMap, SourceMapOptions, default as MagicString } from 'magic-string' */
var convertSourceMap = require('convert-source-map')
var mergeSourceMap = require('merge-source-map')
module.exports = {
	default: astTransformMS,
	astTransformMS,
	walk,
	mergeSourceMap,
	MagicStringModule,
	MagicString, 
	acorn,
}

	
/** @typedef {(context:Context) => "end"|"jump"|"stop"|any} VisitorFunction0 */
/** @typedef {(context:ContextExpanded) => "end"|"jump"|"stop"|any} VisitorFunction */
/** 
 * @typedef {Object} Context
 * @property {Node}  node 
 * @property {Node|null}  parent
 * @property {Node|null}  previousSibling
 * @property {number|null}  index - index of this Node if inside a list like Block.body
*/
/** 
 * @typedef {Object} ContextExpansion
 * @property {MagicString}  edit
 * @property {(node?:Node) => string}  sourceOrig - get node's original source code without changes
 * @property {(node?:Node) => string}  source - get node's source code with changes
 * @property {(replacement:string, node:Node) => Context}  update - replace the source code of the node
 * @property {(append:string, node:Node) => Context}  append - append code to the node's source code
 * @property {(prepend:string, node:Node) => Context}  prepend - prepend code to the node's source code
*/
/** @typedef {Context & ContextExpansion} ContextExpanded */
/** 
 * @typedef {Object} Options
 * @property {string|Buffer}  [source] - source code
 * @property {string|Buffer}  [src] - source alias
 * @property {string|Buffer}  [code] - source alias
 * @property {Node}  ast - ast root node
 * @property {{ parse(source:string, options:ParserOptions):Node }}  [parser] - custom parser (eg acorn typescript)
 * @property {ParserOptions}  [parserOptions]
 * @property {SourceMap}  [prevSourceMap] - SourceMap object of the previous transfomation. If the code contains a `#sourceMappingURL=...` comment then it is extracted from the comment.
 * @property {string}  [inputFilename] - filename of input file (for sourceMap)
 * @property {boolean}  [inExecutionOrder=false] - whether to visit nodes in execution order
 * @property {boolean}  [parentChain=false] - whether to set "parent" on every Node
 * @property {boolean}  [noSourceMap=false] - set to true if source map is not wanted for better performance.
 * @property {VisitorFunction}  enter - on Node enter
 * @property {VisitorFunction}  leave - on Node leave (after visiting all children)
*/
/** 
 * @typedef {Object} MagicStringExtension
 * @property {(withMap?:boolean, sourcesContent?:string[], filenameOverride?:string) => string}  toString - returns the changed source code; can append an inlined source map in a comment
 * @property {(node:Node, enter:VisitorFunction, leave:VisitorFunction) => any}  walk
 * @property {ContextExpansion} ctx - helpers
 * @property {SourceMap?} map - returns a SourceMap of the changed code
*/
function astTransformMS(/** @type {Options} */ options) {
	var {source, src, code, ast, parser, parserOptions, prevSourceMap, inputFilename, inExecutionOrder, parentChain, enter, leave, noSourceMap} = options
	source = source ?? code ?? src
	if (isBuffer(source)) {
		source = source.toString("utf8");
	}
	
	var parse = (parser || acorn).parse;
	/** @type {SourceMap?} */
	var inputMap
	if (!noSourceMap) {
		inputMap = prevSourceMap || convertSourceMap.fromSource(source)?.toObject();
		source = convertSourceMap.removeComments(source);
	}
	/** @type {MagicString & MagicStringExtension} */
	var string = new MagicString(source, {
		filename: inputFilename,
	});
	var ast = options.ast ? options.ast : parse(source, parserOptions || {ecmaVersion: "latest"});

	/** @type {ContextExpanded} */
	var context = {
		edit: string,
		node: null, index: null, parent: null, previousSibling: null,
		sourceOrig(node) {
			node = node || context.node
			return source.slice(node.start, node.end);
		},
		source(node) {
			node = node || context.node
			return string.slice(node.start, node.end);
		},
		update(replacement, node) {
			node = node || context.node
			string.overwrite(node.start, node.end, replacement);
			return context;
		},
		append(append, node) {
			node = node || context.node
			string.appendLeft(node.end, append);
			return context;
		},
		prepend(prepend, node) {
			node = node || context.node
			string.prependRight(node.start, prepend);
			return context;
		},
	};
	string.ctx = context

	
	
	if (!noSourceMap || parentChain) {
		let onEnter
		if (!noSourceMap) {
			onEnter = function ({node, parent}) {
				string.addSourcemapLocation(node.start);
				string.addSourcemapLocation(node.end);
			}
		}
		else {
			onEnter = ()=>false
		}
		walk(ast, onEnter, null, {addParentChain:parentChain});
	}
	string.walk = (node, enter, leave)=>walk(node||ast, enter, leave, {context, inExecutionOrder});
	
	walk(ast, enter, leave, {context, inExecutionOrder});

	var toString = string.toString.bind(string);
	string.toString = function (withMap, sourcesContent, filenameOverride) {
		var src = toString();
		if (withMap && !noSourceMap) {
			var map = getSourceMap()
			if (inputFilename) map.file = inputFilename
			if (filenameOverride) {
				map.file = filenameOverride
				if (map.sources?.length == 1) map.sources[0] = filenameOverride
			}
			if (sourcesContent) map.sourcesContent = sourcesContent
			src +=
				"\n" +
				convertSourceMap.fromObject(map).toComment() +
				"\n";
		}
		return src;
	};

	if (!noSourceMap) {
		Object.defineProperty(string, "map", {
			get: getSourceMap,
		});
	}

	return string;

	/** @returns {SourceMap} */
	function getSourceMap() {
		const defaultFileName = "input.js"
		let options = {}
		if (!inputMap) {
			options.source = inputFilename || defaultFileName
			options.file = inputFilename
		}
		else{
			options.file = inputFilename || inputMap.file || defaultFileName
			options.source = inputMap.sources?.length? inputMap.sources[0] : options.file
		}
		var magicMap = string.generateMap(options);

		if (inputMap) {
			var map =  mergeSourceMap(inputMap, magicMap);
			if (inputFilename) map.file = inputFilename
			return map
		}

		return magicMap;
	}
}
function isBuffer(obj) {
	return (
		obj != null &&
		obj.constructor != null &&
		typeof obj.constructor.isBuffer === "function" &&
		obj.constructor.isBuffer(obj)
	);
}
function walk(
	ast_node,
	/** @type {VisitorFunction0} */ cbEnter,
	/** @type {VisitorFunction0} */ cbLeave,
	/** @type {{ inExecutionOrder?:boolean, addParentChain?:any, context?:Context }?} */ opts
) {
	if (!ast_node || (!cbEnter && !cbLeave)) return;
	var { inExecutionOrder, addParentChain, context } = opts || {}
	if (!context) context = {node: null, parent: null, previousSibling: null, index: null, }
	
	function _walk(node, parent, previousSibling, index) {
		var ret
		if (addParentChain) node.parent = parent;
		if (cbEnter) {
			context.node = node
			context.parent = parent
			context.previousSibling = previousSibling
			context.index = index
			ret = cbEnter(context)
		}
		var walked = false;
		if (ret === "end") return "end";
		if (ret !== "jump" && ret !== "stop") {
			if (inExecutionOrder) {
				walked = true;
				if (
					node.type == "BinaryExpression" ||
					node.type == "LogicalExpression" ||
					node.type == "AssignmentExpression"
				) {
					ret = _walk(node.left, node);
					if (ret === "end") return "end";
					ret = _walk(node.right, node);
					if (ret === "end") return "end";
				} else if (
					node.type == "ConditionalExpression" ||
					node.type == "IfStatement"
				) {
					ret = _walk(node.test, node);
					if (ret === "end") return "end";
					ret = _walk(node.consequent, node);
					if (ret === "end") return "end";
					if (node.alternate) {
						ret = _walk(node.alternate, node);
						if (ret === "end") return "end";
					}
				} else if (node.type == "MemberExpression") {
					ret = _walk(node.object, node);
					if (ret === "end") return "end";
					ret = _walk(node.property, node);
					if (ret === "end") return "end";
				} else if (node.type == "CallExpression") {
					ret = _walk(node.callee, node);
					if (ret === "end") return "end";
					ret = walkArray(node.arguments, node);
					if (ret === "end") return "end";
				} else if (
					node.type == "ForOfStatement" ||
					node.type == "ForInStatement"
				) {
					ret = _walk(node.right, node);
					if (ret === "end") return "end";
					ret = _walk(node.left, node);
					if (ret === "end") return "end";
					ret = _walk(node.body, node);
					if (ret === "end") return "end";
				} else if (node.type == "ForStatement") {
					if (node.init) {
						ret = _walk(node.init, node);
						if (ret === "end") return "end";
					}
					if (node.test) {
						ret = _walk(node.test, node);
						if (ret === "end") return "end";
					}
					if (node.update) {
						ret = _walk(node.update, node);
						if (ret === "end") return "end";
					}
					ret = _walk(node.body, node);
					if (ret === "end") return "end";
				} else if (node.type == "WhileStatement") {
					ret = _walk(node.test, node);
					if (ret === "end") return "end";
					ret = _walk(node.body, node);
					if (ret === "end") return "end";
				} else if (node.type == "DoWhileStatement") {
					ret = _walk(node.body, node);
					if (ret === "end") return "end";
					ret = _walk(node.test, node);
					if (ret === "end") return "end";
				} else if (node.type == "SwitchStatement") {
					ret = _walk(node.discriminant, node);
					if (ret === "end") return "end";
					ret = walkArray(node.cases, node);
					if (ret === "end") return "end";
				} else if (node.type == "SwitchCase") {
					if (node.test) {
						ret = _walk(node.test, node);
						if (ret === "end") return "end";
					}
					ret = _walk(node.consequent, node);
					if (ret === "end") return "end";
				} else walked = false;
			}
			if (!walked) {
				for (var k in node) {
					if (has(node, k)) {
						if (k[0] === "_") continue;
						if (k === "parent") continue;
						let something = node[k];
						if (isNode(something)) {
							ret = _walk(something, node);
							if (ret === "end") return "end";
						} else if (Array.isArray(something)) {
							ret = walkArray(something, node);
							if (ret === "end") return "end";
						}
					}
				}
			}
		}
		if (cbLeave) {
			context.node = node
			context.parent = parent
			context.previousSibling = previousSibling
			context.index = index
			let _ret = cbLeave(context);
			if (typeof _ret == "string") ret = _ret;
		}
		return ret;
	}
	function walkArray(array, parent) {
		let prev = null;
		for (let i = 0; i < array.length; i++) {
			let n = array[i];
			if (isNode(n)) {
				if (addParentChain) n.parent = parent;
				var ret = _walk(n, parent, prev, i);
				if (ret === "end") return "end";
				if (ret === "stop") return "stop";
				prev = n;
			}
		}
	}
	function has(obj, prop) {
		return Object.prototype.hasOwnProperty.call(obj, prop);
	}
	function isNode(node) {
		return (
			typeof node === "object" && node && typeof node.type === "string"
		);
	}
	_walk(ast_node);
}


