




const DEBUG = 0
const CONST_DECLARATION_QUOTE_CHARACTER = "`"
const TO_SHRINK_ALL_STRING_LITERALS = 1
const TO_SHRINK_ALL_PROPERTY_NAMES = 1
const TO_SHRINK_ALL_UNDECLARED_GLOBALS = 1
const TO_SHRINK_ALL_VARIABLES_WHEN_POSSIBLE = 1
const TO_SHRINK_BUILTIN_VALUES = 1 // replaces: undefined, null, Infinity, 
const TO_SHRINK_ALL_THIS = 1 // "this." => "let x=this; x." if used often enough
const MIN_PROPERTY_NAME_LENGTH = 3
const TO_REPLACE_ON_0_GAIN = 0
// class objects
const TO_INLINE_CLASS_OBJECT_PROPERTIES_AND_REMOVE_UNUSED = 0
// comment markers
const CLASS_OBJECT_MARKER = "CLASS_OBJECT"
const EXCLUDE_FUNCTION_FROM_SHRINK_MARKER = "!EXCLUDE!"
const DECLARATIONS_HERE_MARKER = "__JSSHRINK_DECLARATIONS_HERE__"
// string markers
const ADD_DECLARATIONS_MARKER = "!!! ADD_DECLARATIONS !!!" // this marker is expected in a string. It is replaced with the generated declarations for shrunk property names and global objects
const ADD_DECLARATIONS_MARKER_SAFE = "!!! ADD_DECLARATIONS_SAFE !!!" // like ADD_DECLARATIONS_MARKER but global objects are existence-checked: `typeof name !== "undefined"`




const acorn = require("acorn");
const scan = require('./scope-analyzer')
const {astTransformMS} = require("./transform-ast");
const convertSourceMap = require('convert-source-map')
/** @import { SourceMap } from 'magic-string' */

const keywords = new Set(
	["abstract", "arguments", "await", "boolean", "break", "byte", "case", "catch", "char", "class", "const", "continue", "debugger", "default", 
	"delete", "do", "double", "else", "enum", "eval", "export", "extends", "false", "final", "finally", "float", "for", "function", "goto", "if", 
	"implements", "import", "in", "instanceof", "int", "interface", "let", "long", "native", "new", "null", "package", "private", "protected", 
	"public", "return", "short", "static", "super", "switch", "synchronized", "this", "throw", "throws", "transient", "true", "try", "typeof", 
	"var", "void", "volatile", "while", "with", "yield", "const", 
	"NaN", "undefined", "Infinity"]
)


const base54 = (() => {
    const chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ$_0123456789"
    function base54(num) {
        var ret = "", base = 54;
        num++;
        do {
            num--;
            ret += chars[num % base];
            num = Math.floor(num / base);
            base = 64;
        } while (num > 0);
        return ret;
    }
    return base54;
})();
Map.prototype.some = function(cb) { // callback([key, value])
	for (const pair of this) {
		if(cb(pair)) return true
	}
}
Set.prototype.some = function(cb) { // callback(value)
	for (const val of this) {
		if(cb(val)) return true
	}
}
const gimmeSomethingUnique = (() => {
	var counter = 0
	var prefix = "___$$_y0"+base54(Math.floor(Math.random()*100000000)) // let's not bother searching for collisions, just hope this is unique enough
    return function gimme() {
        return prefix+(++counter);
    }
})();
function isJsAlphanum(char){
	if(!char) return false;
	char = char.charCodeAt(0);
	return char > 47 && char < 58 || char > 96 && char < 123 || char > 64 && char < 91 || char === 95 || char === 36;
}
function getAllTakenNamesFor(ast_nodes) {
	// gets all variable names (as string) declared in each scope (and parent scopes) and merges them
	var scopes = new Set
	for (const node of ast_nodes) {
		var scope = scan.scope(node) || scan.nearestScope(node, true) || scan.nearestScope(node)
		scopes.add(scope)
		var p = scope
		while (p = p.parent) {
			scopes.add(p)
		}
	}
	var names = new Set
	for (const scope of scopes) {
		for (const [n] of scope.bindings) {
			names.add(n)
		}
	}
	return names
}
function getIIFEBodyBlockNode(ast_node) {
	// if ast_node is a script wrapped in a IIFE without arguments, then returns the block node of that function
	if(ast_node.type != "Program") return
	var n = ast_node.body
	if(n.length != 1) return
	n = n[0]
	if(n.type != "ExpressionStatement") return
	n = n.expression
	if(n.type == "UnaryExpression"){ // !function(){...}()
		if (n.operator != "!") return
		n = n.argument
	}
	if (n.type != "CallExpression") return
	if(n.arguments.length != 0) return
	n = n.callee
	if(n.type != "FunctionExpression" && n.type != "ArrowFunctionExpression") return
	n = n.body
	if(n.type != "BlockStatement") return
	return n
}
function escapeCharacter(str, charToEscape) {
	if(String.prototype.replaceAll) return str.replaceAll(charToEscape, "\\"+charToEscape)
	else return str.replace(new RegExp(charToEscape, "g"), "\\"+charToEscape)
}
function obtainNewVariableIdentifiers(ast_node, otherIdentifiersInThisScope, customGlobalReservedNames /* Set<string> */) {
	// otherIdentifiersInThisScope: [id?, numOccurences, Set(Nodes)?, maxNameLength, name?, nodeKey?]
	
	function areRefsInScope(referencedNodesSet, scopeNode) {
		var i=0
		for (const refNode of referencedNodesSet) {
			// The first entry is the declaration. The declaration can be anywhere.
			if(i === 0) {
				++i
				if (scopeNode.start <= refNode.start && scopeNode.end >= refNode.end) {
					return true
				}
				continue
			}
			// ordered from here
			if (scopeNode.start > refNode.end) {
				continue
			}
			else if(refNode.start > scopeNode.end){
				return false
			}
			else if (refNode.start >= scopeNode.start) {
				return true
			}
		}
		return false
	}
	function canTake(id, scope, node) {
		if (keywords.has(id)
			|| undeclaredBindings.has(id)
			|| customGlobalReservedNames && customGlobalReservedNames.has(id)) {
			return false
		}
		var isInBlockScope = scope.isBlock
		var aParentScope = scope
		while (aParentScope = aParentScope.parent){
			if (aParentScope.newVars) {
				var referencedNodesSet = aParentScope.newVars.get(id)
				if (referencedNodesSet) {
					if (isInBlockScope) {
						return false
					}
					if(areRefsInScope(referencedNodesSet, node)){
						return false
					}
				}
			}
			if (isInBlockScope && !aParentScope.isBlock) {
				isInBlockScope = false
			}
		}
		return true
	}
	function assignNewNames(scope, node, otherIdentifiersInThisScope) {
		var variableItems = [...scope.bindings].map(x=>[null, x[1].references.size, x[1].references, 100, x[1].name, "_v"])
		var allItems = variableItems
		if(otherIdentifiersInThisScope){
			allItems = allItems.concat(otherIdentifiersInThisScope)
		}
		allItems.sort(([, aLength], [, bLength]) => bLength - aLength)
		var nameCounter = -1
		varsLoop:
		for (const t of allItems) {
			while (true) {
				let aname = base54(++nameCounter)
				// the new name can be longer than the original if another item has a higher priority
				if (canTake(aname, scope, node)) {
					var maxIdLength = t[3]
					if(aname.length > maxIdLength){
						t[0] = null
						--nameCounter
						continue varsLoop
					}
					t[0] = aname
					var nodes = t[2]
					if (nodes) {
						nodes = nodes.references || nodes // Binding or Set
						for (const n of nodes) {
							if(t[5]) n[t[5]] = aname
							if(n.type != "Identifier" && n.type != "Literal" && n.type != "TemplateLiteral" && !(n.type === "UnaryExpression" && n.operator === "void")) {
								throw "node must be a Identifier|Literal|TemplateLiteral"
							}	
						}
					}
					continue varsLoop
				}
			}
		}
		if(allItems.length){
			 scope.newVars = new Map(allItems.map(t => [t[0], t[2]]))
		}
		variableItems.forEach(t => gain += (t[4].length - t[0].length) * t[1])
	}
	function assignNewLabelNames(labels) {
		var nameCounter = -1
		for (var labelName in labels) {
			var nodes = labels[labelName];
			var aname = base54(++nameCounter)
			for (const node of nodes) {
				node._v = aname
				gain += node.name.length - aname.length
			}
		}
	}
	
	var n = ast_node
	while (n.parent) n = n.parent
	var undeclaredBindings = scan.scope(n).undeclaredBindings
	
	var gain = 0
	walk(ast_node, node=>{
		var scope = scan.scope(node)
		if (scope) {
			assignNewNames(scope, node, otherIdentifiersInThisScope)
			if(scope.labels) assignNewLabelNames(scope.labels)
		}
		otherIdentifiersInThisScope = null
	})
	return gain
}
function findAllStringLiterals(ast_node, toIncludePropertyKeys=true, minPropertyKeyLength=1, excludeNodes) {
	var names = new Map
	walk(ast_node, node=>{
		if (excludeNodes?.size && excludeNodes.has(node)) {
			return "jump"
		}
		
		var name = null
		var isIdentifier = node.type == "Identifier"
		var isLiteral = node.type == "Literal"
		var isTemplateLiteral = node.type == "TemplateLiteral" && node.expressions.length == 0
		var templateLiteralValue = isTemplateLiteral &&  node.quasis[0].value.cooked
		if(isLiteral || isTemplateLiteral || isIdentifier) {
			var isObjectKey = node.parent.type == "Property" && node.parent.key == node
			var isPropertyMemberKey = node.parent.type == "MemberExpression" && node.parent.property == node
			var isPropertyKey = isObjectKey || isPropertyMemberKey
			var caseDelta = -2
			if (isPropertyKey) {
					
				var isComputed = node.parent.computed
				var isOptional = node.parent.optional
				if (isLiteral) {
					// it can be a string, bool, number, ...
					if(typeof node.value !== "string") return // do not deal with non strings here
					name = node.value
				}
				else if(isTemplateLiteral){
					name = templateLiteralValue
				}
				else if(isIdentifier && !isComputed){ // if computed key then Identifier is a variable and not a string
					name = node.name
				}
				else{
					return
				}
				//filter
				let isActuallyALiteral = isComputed  // treat x["literal"] like a literal
				if (isActuallyALiteral) {
					
				}
				else{
					if(!toIncludePropertyKeys){
						return
					}
					
					if(name.length < minPropertyKeyLength){
						return
					}
					
					if (isIdentifier) { // {a: | x?.a | x.a
						caseDelta = isObjectKey || isOptional? 2 : 1
					}
					else{ // {"a":
						caseDelta = 0
					}
				}
				
			}
			else if(isLiteral && typeof node.value == "string"){
				name = node.value
			}
			else if(isTemplateLiteral){
				name = templateLiteralValue
			}
			else{
				return
			}
			
			
			var tuple = names.get(name)
			if(!tuple){
				tuple = [[], 0, 0, 0, 0]
				names.set(name, tuple)
			}
			var nodes = tuple[0]
			nodes.push(node)
			if(caseDelta == -2) tuple[1] += 1
			else if(caseDelta == 0) tuple[2] += 1
			else if(caseDelta == 1) tuple[3] += 1
			else if(caseDelta == 2) tuple[4] += 1
			return
		}
	})
	return names
}
function findBuiltinValues(ast_node, excludeNodes) {
	var names = new Map
	walk(ast_node, node=>{
		if (excludeNodes?.size && excludeNodes.has(node)) {
			return "jump"
		}
		
		var isLiteral = node.type === "Literal"
		var isIdentifier = node.type === "Identifier"
		if(isLiteral || isIdentifier) {
			if(isLiteral && node.value === null) {
				var name = "null"
			}
			else if(isIdentifier){
				if (node.name === "undefined") {
					var name = "void 0"
				} else if (node.name === "Infinity"){
					var name = "Infinity"
				}
			}
		}
		else if(node.type === "UnaryExpression" && node.operator === "void" && (node.argument.type === "Literal" || node.argument.type === "Identifier")){
			var name = "void 0"
		}
		if (name) {
			var refNodes = names.get(name)
			if(!refNodes){
				refNodes = []
				names.set(name, refNodes)
			}
			refNodes.push(node)
		}
	})
	return names
}
function getCharacterGain(origLiteralLength, newIdentifierLength, n_m2, n_p0, n_p1, n_p2) {
	var diff = origLiteralLength - newIdentifierLength
	var gain = (diff+2)*n_m2 + (diff)*n_p0
	if (diff > 1) {
		gain += (diff-1)*n_p1
	}
	if (diff > 2) {
		gain += (diff-2)*n_p2
	}
	var declarationCost = origLiteralLength + newIdentifierLength + 2 + 2
	gain -= declarationCost
	return gain
}
function maxIdentifierLengthFor(num, origLength, allow0Gain) {
	var maxLength = (num*origLength-origLength-2)/(num+1) 
	if(maxLength%1 == 0 && !allow0Gain) maxLength -= 1
	return maxLength
}
function getMaxIdentifierLengthForPropsLiterals(originalLiteral, toAllow_0_Gain, n_m2, n_p0, n_p1, n_p2) {
	var newIdentifierLength = 1
	// The function has conditional branches so extrapolation would be bad
	while (true) {
		var gain = getCharacterGain(originalLiteral.length, newIdentifierLength, n_m2, n_p0, n_p1, n_p2)
		var hasGain = toAllow_0_Gain? gain >= 0 : gain > 0
		if(!hasGain) break
		++newIdentifierLength
		if (newIdentifierLength > 10) { // cap at 8
			break;
		}
	}
	return newIdentifierLength -1
}
function getAllScopeVariableNames(scope) {
	var names = new Set
	getAllBlockNames(scope)
	function getAllBlockNames(scope) {
		scope.bindings.forEach(b => names.add(b.name))
		if (scope.children) {
			for (const child of scope.children) {
				if(child.isBlock) getAllBlockNames(child)
			}
		}
	}
	return names
}
function walk(ast_node, cb, cbLeave, inExecutionOrder) {
	// cb(node, parent, previousSibling, index) : "end" | "stop" | "jump"
	// 	 "end" = stop walking, and don't call the "leave" callbacks
	// 	 "stop" = stop walking, do call the "leave" callbacks
	// 	 "jump" = jump over this node
	if(!ast_node || !cb && !cbLeave) return
	function _walk(node, parent, previousSibling, index) {
		var ret = cb && cb(node, parent, previousSibling, index)
		var walked = false
		if(ret === "end") return "end"
		if(ret !== "jump" && ret !== "stop") {
			if (inExecutionOrder) {
				walked = true
				if (node.type == "BinaryExpression" || node.type == "LogicalExpression" || node.type == "AssignmentExpression") {
					ret = _walk(node.left, node)
					if(ret === "end") return "end"
					ret = _walk(node.right, node)
					if(ret === "end") return "end"
				}
				else if (node.type == "ConditionalExpression" || node.type == "IfStatement") {
					ret = _walk(node.test, node)
					if(ret === "end") return "end"
					ret = _walk(node.consequent, node)
					if(ret === "end") return "end"
					if (node.alternate) {
						ret = _walk(node.alternate, node)
						if(ret === "end") return "end"
					}
				}
				else if (node.type == "MemberExpression") {
					ret = _walk(node.object, node);
					if (ret === "end") return "end";
					ret = _walk(node.property, node);
					if (ret === "end") return "end";
				}
				else if (node.type == "CallExpression") {
					ret = _walk(node.callee, node)
					if(ret === "end") return "end"
					ret = walkArray(node.arguments, node)
					if(ret === "end") return "end"
				}
				else if (node.type == "ForOfStatement" || node.type == "ForInStatement") {
					ret = _walk(node.right, node)
					if(ret === "end") return "end"
					ret = _walk(node.left, node)
					if(ret === "end") return "end"
					ret = _walk(node.body, node)
					if(ret === "end") return "end"
				}
				else if (node.type == "ForStatement") {
					if (node.init) {
						ret = _walk(node.init, node)
						if(ret === "end") return "end"
					}
					if (node.test) {
						ret = _walk(node.test, node)
						if(ret === "end") return "end"
					}
					if (node.update) {
						ret = _walk(node.update, node)
						if(ret === "end") return "end"
					}
					ret = _walk(node.body, node)
					if(ret === "end") return "end"
				}
				else if (node.type == "WhileStatement") {
					ret = _walk(node.test, node)
					if(ret === "end") return "end"
					ret = _walk(node.body, node)
					if(ret === "end") return "end"
				}
				else if (node.type == "DoWhileStatement") {
					ret = _walk(node.body, node)
					if(ret === "end") return "end"
					ret = _walk(node.test, node)
					if(ret === "end") return "end"
				}
				else if (node.type == "SwitchStatement") {
					ret = _walk(node.discriminant, node)
					if(ret === "end") return "end"
					ret = walkArray(node.cases, node)
					if(ret === "end") return "end"
				}
				else if (node.type == "SwitchCase") {
					if (node.test) {
						ret = _walk(node.test, node)
						if(ret === "end") return "end"
					}
					ret = _walk(node.consequent, node)
					if(ret === "end") return "end"
				}
				else walked = false
			}
			if(!walked){
				for (var k in node) {
					if (has(node, k)) {
						if (k[0] === '_') continue
						if (k === 'parent') continue
						let something = node[k]
						if (isNode(something)) {
							ret = _walk(something, node)
							if(ret === "end") return "end"
						} else if (Array.isArray(something)) {
							ret = walkArray(something, node)
							if(ret === "end") return "end"
						}
					}	
				}
			}
		}
		if (cbLeave) {
			let _ret = cbLeave(node, parent, previousSibling, index)
			if(typeof _ret == "string") ret = _ret
		}
		return ret
	}
	function walkArray(array, parent) {
		let prev = null
		for (let i = 0; i < array.length; i++) {
			let n = array[i]
			if (isNode(n)){
				ret = _walk(n, parent, prev, i)
				if(ret === "end") return "end"
				if(ret === "stop") return "stop"
				prev = n
			}
		}
	}
	function has (obj, prop) {
		return Object.prototype.hasOwnProperty.call(obj, prop)
	}
	function isNode (node) {
		return typeof node === 'object' && node && typeof node.type === 'string'
	}
	_walk(ast_node)
}
function getRefsInScope(referencedNodesSet, scopeNode) {
	var refs
	var i=0
	for (const refNode of referencedNodesSet) {
		// The first entry is the declaration.
		if(i === 0) {
			++i
			continue
		}
		if (scopeNode.start > refNode.end) {
			continue
		}
		else if(refNode.start > scopeNode.end){
			break
		}
		else if (refNode.start >= scopeNode.start) {
			if(!refs) refs = []
			refs.push(refNode)
			continue
		}
	}
	return refs
}
function getDirectParentScope(node) {
	return scan.nearestScope(node, true) || scan.nearestScope(node) 
}
function getNodeDepth(node) {
	var depth = 1
	while (node = node.parent) ++depth
	return depth
}
function isVariableAssignedTo(binding, except) {
	var i=0
	for (const refNode of binding.references) {
		if(++i == 1) continue // skip definition
		if((refNode.parent.type == "UpdateExpression"
			|| refNode.parent.type == "AssignmentExpression" && refNode.parent.left == refNode
			) && !(except && except.includes(refNode))
		) return true
	}
}
function transform_addSemicolIfNeeded(node, ctx) {
	var block
	var statement = node
	while (block = statement.parent) {
		if (block.type == "Program" || block.type == "BlockStatement") {
			break
		}
		if(isFunctionNode(block)) return
		statement = statement.parent
	}
	if (!block) {
		return 
	}
	var ni = block.body.indexOf(statement)
	if(ni > 0){
		let char
		let iu = ni, io = ni-1
		let nu, no
		while (!char) {
			nu = block.body[iu++]
			char = ctx? ctx.source(nu)[0] : nu.source()[0]
			if(iu >= block.body.length) return 
		}
		
		if (char == "(" || nu.type == "AssignmentExpression" && (char == "[" || char == "{")) {
			let char2, src2
			do {
				no = block.body[io]
				src2 = ctx? ctx.source(no) : no.source()
			} while (--io >= 0 && !src2.length);
			if(io < 0) return
			char2 = src2[src2.length-1]
			if(char2 != ";"){
				if (ctx) {
					ctx.append(";", no)
				}
				else {
					no.edit.append(";")
				}
			}
		}
	}
}
function ToNotWrapExpressionInRoundParantheses(inlinedNode, replacedNode) {
	return inlinedNode.type == "CallExpression" 
		|| inlinedNode.type == "Literal" 
			&& !(replacedNode && replacedNode.parent && replacedNode.parent.type == "MemberExpression" && typeof inlinedNode.value == "number")
		|| inlinedNode.type == "Identifier" 
		|| inlinedNode.type == "MemberExpression"
}
function isBindingExistenceChecked(binding) {
	for (const ref of binding.references) {
		if(ref.parent.type == "UnaryExpression" && ref.parent.operator == "typeof") return true
	}
}
function isCallNode(node) {
	return node.type === "CallExpression" 
	|| node.type === "MemberExpression" // Can be a getter
}
function hasExpressionCalls(node) {
	var has = false
	walk(node, n=>{
		if (isCallNode(n)){
			has = true
			return "end"
		}
		if (isFunctionNode(n)) {
			return "jump"
		}
	})
	return has
}
function isFunctionNode(n) {
	return n.type === 'FunctionDeclaration' || n.type === 'FunctionExpression' || n.type === 'ArrowFunctionExpression'
}
function isSafeAssignment(AssignmentExpression) {
	var safe = true
	walk(AssignmentExpression.left, n=>{
		if (isCallNode(n)){
			safe = false
			return "end"
		}
	})
	return safe
}
function getFunctionInfo(functionNode, refCallExpressionNode, variableNamesChangable) {
	function checkStatements(functionNode) {
		var hasStatements = false
		var lastReturnNode = false
		var conditionalReturn = false
		if (functionNode.expression) {
			return {hasStatements:false, lastReturnNode:false}
		}
		var BlockStatement = functionNode.body
		if(BlockStatement.type != "BlockStatement") throw "BlockStatement expected"
		var hasStatements = false, lastReturnNode = null
		var statements = BlockStatement.body
		let lastNode = statements[statements.length-1]
		for (var i = 0; i < statements.length; i++) {
			var statement = statements[i];
			if (statement.type == "ReturnStatement") {
				if (statement == lastNode) {
					lastReturnNode = statement
					break
				}
				else {
					conditionalReturn = true
					break
				}
			}
			if (statement.type != "ExpressionStatement") {
				hasStatements = true
			}
		}
		
		return {hasStatements, lastReturnNode, conditionalReturn}
	}
	function hasFunctionDeclarations(functionNode) {
		var has = false
		var names = [[], new Set] // names, nodes
		walk(functionNode, n=>{
			if (n == functionNode) return
			if (n.type === 'FunctionDeclaration') {
				has = true
				names[0].push(n.id.name)
				names[1].add(n)
				return "jump"
			}
			if (n.type === 'FunctionExpression' || n.type === 'ArrowFunctionExpression') {
				return "jump"
			}
		})
		return has && names
	}
	if(refCallExpressionNode.type != "CallExpression") throw "CallExpression expected"
	if(functionNode.generator || functionNode.async) return 
	var isCallSiteAStatement = refCallExpressionNode.parent.type == "ExpressionStatement"
	var isCallSiteAVariableDeclarator = refCallExpressionNode.parent.type == "VariableDeclarator" // var a=func();
										&& refCallExpressionNode.parent.id.type == "Identifier"
										&& refCallExpressionNode.parent.id
	var isCallSiteAnAssignmentExpression = refCallExpressionNode.parent.type == "AssignmentExpression" 
										&& refCallExpressionNode.parent.parent.type == "ExpressionStatement" // a=func();
										&& isSafeAssignment(refCallExpressionNode.parent)
										&& refCallExpressionNode.parent.left
	var funcScope = scan.scope(functionNode)
	var {hasStatements, lastReturnNode, conditionalReturn} = checkStatements(functionNode)
	if(conditionalReturn) return
	var isExpression = functionNode.expression || !hasStatements
	var params = functionNode.params
	var isOriginallyABlock = false
	var toCreateBlock = !isExpression
	var toInlineArg = new Set
	
	if(!functionNode.expression){
		if(functionNode.body.type == "BlockStatement"){
			let fbScope = scan.scope(functionNode.body)
			var hasFunctionBlockLets = fbScope && fbScope.bindings.size
			isOriginallyABlock = true
		}
	}
	
	var funcDeclarations = hasFunctionDeclarations(functionNode) // function Name(){...} - special handling for these inner functions
	if(funcDeclarations){
		if(funcDeclarations[0].some(n => isVariableAssignedTo(funcScope.bindings.get(n)))) return // declared function name reassigned
		if(!variableNamesChangable) return
		functionNode._funDeclarations = funcDeclarations[1]
	}
	
	
	for (var i = 0; i < params.length; i++) {
		var paramNode = params[i]
		var arg = refCallExpressionNode.arguments[i]
		if(paramNode.type != "Identifier") return
		var paramBinding = funcScope.bindings.get(paramNode.name)
		if(isExpression) {
			var numReferences = paramBinding.references.size - 1
			var isSimpleArg = arg && (arg.type === 'Literal' || arg.type === 'Identifier' || arg.type === "TemplateLiteral" && arg.expressions.length == 0)
			var isArgString = isSimpleArg && (arg.type === 'Literal' && typeof arg.value === "string" || arg.type === "TemplateLiteral")
			var isArgIdentifier = isSimpleArg && arg.type === 'Identifier'
			var canInlineParam = !isVariableAssignedTo(paramBinding)
			if(!canInlineParam){
				if (isCallSiteAStatement) {
					toCreateBlock = true 
				}
				else return
			}
			if(numReferences > 1){
				if(canInlineParam && (!arg || numReferences <= 3 && isSimpleArg && !isArgString || isArgIdentifier)){
					toInlineArg.add(paramBinding.name)
				}
				else if (isCallSiteAStatement) {
					toCreateBlock = true 
				}
				else return
			}
		}
	}
	var toPrependForAssignment = false
	if(toCreateBlock && variableNamesChangable && isCallSiteAVariableDeclarator){
		toPrependForAssignment = true
	}
	if (!toPrependForAssignment && toCreateBlock && !isCallSiteAStatement) {
		let anode = refCallExpressionNode
		let isunsafe
		let targetStatement
		while ((anode = anode.parent) && anode.parent) {
			if(isFunctionNode(anode) || anode.type === 'ForStatement' || anode.type === 'ForInStatement' || anode.type === 'ForOfStatement'){
				isunsafe = true
				break
			}
			if (anode.parent.type == "BlockStatement") {
				targetStatement = anode
				anode = anode.parent
				break
			}
		}
		if(!isunsafe && anode && targetStatement){
			if(!hasCallsBetween(anode, targetStatement, refCallExpressionNode, 1)){
				var toPrependForExpression = {
					targetStatement,
					returnVarName: gimmeSomethingUnique()
				}
			}
		}
		if (!toPrependForExpression) {
			return
		}
	}
	
	var type = {
		isExpression, 
		hasStatements, 
		lastReturnNode, 
		hasFunctionBlockLets,
		isOriginallyABlock,
		toCreateBlock,
		toInlineArg,
		toPrependForAssignment,
		toPrependForExpression,
		isCallSiteAVariableDeclarator,
		isCallSiteAnAssignmentExpression,
		isCallSiteAStatement,
		refCallExpressionNode,
	}
	return type
}
function editInlinedFunctionBody(functionNode, functionInfo, refCallExpressionNode, ctx) {
	if (functionInfo.toCreateBlock) {
		walk(functionNode, n =>{
			if (n != functionNode && isFunctionNode(n)) {
				return "jump"
			}
			if (n.type == "VariableDeclaration" && n.kind == 'var') {
				let assignmentDeclarators = []
				let hasComplicated
				n.declarations.forEach(d => {
					if(d.id.type !== "Identifier") hasComplicated = 1
					d.init && assignmentDeclarators.push(d)
				})
				let assignmentStatementsSrc = assignmentDeclarators.map(d=>ctx.source(d)).join(",")
				if(hasComplicated && assignmentDeclarators.length == 1) assignmentStatementsSrc = "0,"+assignmentStatementsSrc
				if(assignmentStatementsSrc) assignmentStatementsSrc += ";"
				ctx.update(assignmentStatementsSrc, n)
			}
		})
	}
	if(!functionInfo.toCreateBlock){
		for (var i = 0; i < functionNode.params.length; i++) {
			var param = functionNode.params[i];
			var arg = refCallExpressionNode.arguments[i];
			if (arg === undefined) {
				arg = "undefined"
			}
			var binding = scan.binding(param)
			if (functionInfo.toInlineArg.has(param.name)) {
				var paramRefNodes = [...binding.references].slice(1)
			}
			else{
				var paramRefNodes = [[...binding.references][1]]
			}
			for (const paramRefNode of paramRefNodes) {
				if (paramRefNode) {
					let replacementArgSrc
					if (typeof arg == "string") {
						replacementArgSrc = arg
					}
					else{
						replacementArgSrc = ctx.source(arg)
						if (!ToNotWrapExpressionInRoundParantheses(arg, paramRefNode)) {
							replacementArgSrc = "("+replacementArgSrc+")"
						}
					}
					ctx.update(replacementArgSrc, paramRefNode)
				}
			}
		}
	}
	
	var node = functionNode
	var fBody = node.body
	var isCallSiteAStatement = refCallExpressionNode.parent.type == "ExpressionStatement"
	if(fBody.type == "BlockStatement"){
		let bodyBlockNodes = fBody.body
		let assignmentLeftNode = functionInfo.isCallSiteAVariableDeclarator || functionInfo.isCallSiteAnAssignmentExpression
		let lastReturnNode = functionInfo.lastReturnNode
		if (lastReturnNode) {
			let returnSrc
			if(isCallSiteAStatement && lastReturnNode.argument.type == "Literal") returnSrc = ""
			else returnSrc = ctx.source(lastReturnNode.argument)
			if (functionInfo.toPrependForAssignment) {
				returnSrc = ctx.source(assignmentLeftNode) + "=" + returnSrc
			}
			else if (functionInfo.toPrependForExpression) {
				returnSrc = functionInfo.toPrependForExpression.returnVarName + "=" + returnSrc
			}
			ctx.update(returnSrc, lastReturnNode)
		}
		else{
			if(functionInfo.toPrependForAssignment){
				let lastBodyNode = bodyBlockNodes[bodyBlockNodes.length-1]
				ctx.append(";"+ctx.source(assignmentLeftNode) + "=void 0", lastBodyNode)
			}
		}
		let toConvertBlockIntoExpression = !functionInfo.toCreateBlock && functionInfo.isOriginallyABlock
		if(toConvertBlockIntoExpression){
			let newBodyParts = bodyBlockNodes.map(bn => {
				var bns = ctx.source(bn)
				if(bns[bns.length-1] == ";") bns = bns.slice(0, bns.length-1)
				return bns
			})
			if(!lastReturnNode && !isCallSiteAStatement) newBodyParts.push("void 0")
			let newBodySrc = newBodyParts.join(",")
			let toNotWrapInRoundParantheses = isCallSiteAStatement || (
				bodyBlockNodes.length == 1 && ToNotWrapExpressionInRoundParantheses(bodyBlockNodes[0])
			)
			if(!toNotWrapInRoundParantheses){
				newBodySrc = "("+newBodySrc+")"
			}
			if (isCallSiteAStatement) {
				newBodySrc = newBodySrc+";"
			}
			ctx.update(newBodySrc, fBody)
		}
		else{
			if (node._funDeclarations && node._funDeclarations.size) {
				var scopeFDs = new Map
				for (const d of node._funDeclarations) {
					let fscope = scan.nearestScope(d, true) || scan.nearestScope(d)
					let block
					if (fscope.n.type == "BlockStatement") {
						block = fscope.n
					}
					else if (fscope.n.body && fscope.n.body.type == "BlockStatement") {
						block = fscope.n.body
					}
					else throw "BlockStatement expected"
					let funcSrc = ctx.source(d)
					let name = d.id._rn || d.id.name
					funcSrc = funcSrc.replace(/^\s*function\s+[\w_\$]+/, "function")
					let src = name + "=" + funcSrc
					let assignments = scopeFDs.get(fscope)
					if (!assignments) {
						assignments = [block, []]
						scopeFDs.set(fscope, assignments)
					}
					assignments = assignments[1]
					assignments.push(src)
				}
				for (const [scope, [block, assignments]] of scopeFDs) {
					let src = assignments.join(",")+";"
					ctx.prepend(src, block.body[0])
				}
				for (const d of node._funDeclarations) {
					ctx.update("", d)
				}
			}
			
		}
	}
	else if(!ToNotWrapExpressionInRoundParantheses(fBody)){
		ctx.update("("+ctx.source(fBody)+")", fBody)
	}
	node._fBodySrc = ctx.source(fBody)
	
}
function inlineFunctionBody(functionNode, functionInfo, refCallExpressionNode, ctx) {
	var node = refCallExpressionNode
	var fBodySrc = functionNode._fBodySrc
	var toCreateBlock = functionInfo.toCreateBlock
	var editSrc
	if (toCreateBlock) {
		var funcScopeBindings = scan.scope(functionNode).bindings
		var lets = []
		var paramsMap = new Map
		functionNode.params.forEach((p, i)=>{
			paramsMap.set(p.name, refCallExpressionNode.arguments[i])
		})
		for (const [, b] of funcScopeBindings) {
			let name = b.definition._rn || b.name
			if(paramsMap.has(b.name) && paramsMap.get(b.name)){
				lets.push(name + "=" + ctx.source(paramsMap.get(b.name)))
			}
			else{
				lets.push(name)
			}
		}
		if (lets.length) {
			var letsDecl = "let "+lets.join(",")+";"
		}
		if (!functionInfo.hasFunctionBlockLets && functionInfo.isOriginallyABlock) {
			fBodySrc = fBodySrc.slice(1, fBodySrc.length-1)
		}
		if (letsDecl) {
			var inlSrc = "{" + letsDecl + fBodySrc + "}"
		}
		else {
			var inlSrc = fBodySrc 
		}
		
		if (functionInfo.toPrependForAssignment) {
			if (functionInfo.isCallSiteAnAssignmentExpression) {
				editSrc = inlSrc 
			} 
			else if(functionInfo.isCallSiteAVariableDeclarator){
				let varDeclaratorNode = refCallExpressionNode.parent
				let varDeclarationNode = varDeclaratorNode.parent
				varDeclaratorNode._inlinedFunc = inlSrc
				if (DEBUG) {
					varDeclaratorNode._name = functionNode._name
				}
				var toPrependForAssignment = {
					varDeclarationNode,
				}
			}
			else throw "toPrependForAssignment error"
		}
		else if(functionInfo.toPrependForExpression){
			functionInfo.toPrependForExpression.targetStatement._inlinedFunc = inlSrc
			var toPrependForExpression = {
			}
		}
		else{
			editSrc = inlSrc
		}
		
	}
	else{
		if (!functionInfo.hasFunctionBlockLets && functionInfo.isOriginallyABlock 
			&& !scan.scope(functionNode).bindings.size
			&& fBodySrc[0] == "{"
		) {
			fBodySrc = fBodySrc.slice(1, fBodySrc.length-1)
		}
		editSrc = fBodySrc
	}
	
	if (editSrc) {
		ctx.update(editSrc, node)
		transform_addSemicolIfNeeded(node, ctx)
	}
	
	return {
		toPrependForAssignment,
		toPrependForExpression,
	}
}
function hasCallsBetween(rootNode, startNode, endNode, toCheckStartNodeToo, toCheckEndNodeToo) {
	var has = false
	var begin = false
	var end = false
	function check(node) {
		walk(node, n=>{
			if (toCheckStartNodeToo && n == startNode) {
				begin = true
			}
			if(!begin) return
			if (!toCheckEndNodeToo && n === endNode) {
				end = true
				return "end"
			}
			if (n.type == "ConditionalExpression" || n.type == "IfStatement") {
				check(n.test)
				if(end) return "end"
				check(n.consequent)
				if (end) {
					if(endNode && endNode.start >= n.consequent.start && endNode.start < n.consequent.end || !endNode) return "end"
					has = false
					end = false
				}
				if (n.alternate) {
					check(n.alternate)
					if(end) return "end"
				}
				return "jump"
			}
			if (n.type == "MemberExpression") {
				let mem = n
				while(mem.object.type == "MemberExpression") mem = mem.object
				check(mem.object)
				if(end) return "end"
				check(mem.property)
				has = true
				end = true
				return "end"
			}
			if (n.type == "CallExpression") {
				check(n.callee)
				if(end) return "end"
				for (const arg of n.arguments) {
					check(arg)
					if(end) return "end"
				}
				has = true
				end = true
				return "end"
			}
			if (isCallNode(n)){
				has = true
				end = true
				return "end"
			}
			if (isFunctionNode(n)) {
				return "jump"
			}
			if (n === endNode) {
				end = true
				return "end"
			}
		}, n=>{
			if (!toCheckStartNodeToo && n == startNode) {
				begin = true
			}
		}, 1)
	}
	check(rootNode)
	return has
}
function inlineClassObjectProperties(src, options) {
	const variableNamesChangeable = options && "variableNamesChangeable" in options? options.variableNamesChangeable : false
	const infoObject = options && "infoObject" in options? options.infoObject : null
	const withSourceMap = options && "withSourceMap" in options? options.withSourceMap : false
	let inputMap = options?.map
	
	function _inline() {
		
		
		var ast = acorn.parse(src, {
			ecmaVersion: "latest",
			// sourceType: "module",
		})
		scan.crawl(ast)
		
		
		
		function findClassObject() {
			function hasMarker(ObjectExpressionNode) {
				var reg = new RegExp("/\\*\\s*"+CLASS_OBJECT_MARKER+"\\s*\\*/")
				testStr = src.slice(ObjectExpressionNode.start-(CLASS_OBJECT_MARKER.length*2 + 15), ObjectExpressionNode.start)
				return reg.test(testStr)
			}
			walk(ast, n=>{
				if (n.type == "ObjectExpression" && _offset <= n.start && hasMarker(n)) {
					_offset = n.start
					_object_found = 1
					cObj = n
					return "end" 
				}
				if (n.type == "ClassDeclaration" && _offset <= n.start && n.body && n.body.body) {
					_offset = n.start
					_object_found = 1
					cObj = n
					cObj._isClass = 1
					return "end" 
				}
			})
		}
		var cObj
		findClassObject()
		if (!_object_found) return
		var objScope = getDirectParentScope(cObj)
		
		var allProps = new Map
		var unusedProps
		function getPropsAndFilterUnsuitables() {
			
			function filterIfAccessedOnUnknownObjectsAndGetRefs() {
				function isThisConnected(refsite) {
					var isConnected = false
					var curScope = getDirectParentScope(refsite)
					do {
						if (curScope == objScope) {
							isConnected = true
							break
						}
						if (curScope.isBlock) {
							continue
						}
						else if (curScope.n.type != "ArrowFunctionExpression") {
							break
						}
					} while (curScope = curScope.parent);
					return !isConnected
				}
				function isAssignedTo(node) {
					return  node.parent.type == "UpdateExpression" 
						|| node.parent.type == "AssignmentExpression" && node.parent.left == node
				}
				for (const [n, propNode] of allProps) {
					if(propNode) propNode._refs = new Set
				}
				walk(ast, node=>{
					var name = null
					var isIdentifier = node.type == "Identifier"
					var isLiteral = node.type == "Literal"
					var isTemplateLiteral = node.type == "TemplateLiteral" && node.expressions.length == 0
					var templateLiteralValue = isTemplateLiteral &&  node.quasis[0].value.cooked
					if(!(isLiteral || isTemplateLiteral || isIdentifier)) return 
					var isPropertyMemberKey = node.parent.type == "MemberExpression" && node.parent.property == node
					if (isPropertyMemberKey) {
							
						var isComputed = node.parent.computed
						if (isLiteral) {
							if(typeof node.value !== "string") return
							name = node.value
						}
						else if(isTemplateLiteral){
							name = templateLiteralValue
						}
						else if(isIdentifier && !isComputed){
							name = node.name
						}
						else{
							return
						}
					}
					else{
						return
					}
					
					node = node.parent
					
					var notOK = (node.start < cObj.start || node.start > cObj.end)
								|| node.object.type != "ThisExpression"
								|| !isThisConnected(node)
								|| isAssignedTo(node)
								
								
					var propNode = allProps.get(name)
					if(propNode) propNode._uses = (propNode._uses||0)+1
					if (notOK) {
						if(propNode) propNode._forbidden = true
						return 
					}
					
					var propNode = allProps.get(name)
					if (propNode) {
						var isInSameNode = node.start >= propNode.start && node.end < propNode.end
						if (!isInSameNode) {
							propNode._refs.add(node)
						}
						
					}
				})
			}
			function findAllObjectProperties() {
				var properties = cObj._isClass? cObj.body.body : cObj.properties
				for (let propertyNode of properties) {
					if(cObj._isClass){
						if(propertyNode.kind == "constructor") continue
						if(propertyNode.kind == "get" || propertyNode.kind == "set") continue
						
					}
					else{
						if (propertyNode.kind !== "init") continue
						
					}
					if (propertyNode.key.type == "Identifier") {
						var name = propertyNode.key.name
					}
					else if(propertyNode.key.type == "Literal" && typeof propertyNode.key.value == "string"){
						var name = propertyNode.key.value 
					}
					else continue
					if(!propertyNode.value) continue
					if(hasExpressionCalls(propertyNode.value)) continue
					allProps.set(name, propertyNode.value)
					if(propertyNode.value) propertyNode.value._name = name
				}
			}
			
			
			findAllObjectProperties(cObj)
			if(!allProps.size) return 
			filterIfAccessedOnUnknownObjectsAndGetRefs()
			if(!allProps.size) return 
			function findUnusedProps() {
				while (1) {
					let filtered
					for (const [name, node] of allProps) {
						if (!node._uses && !node._unused && !node._forbidden) {
							node._unused = 1
							filtered = 1
														
							for (const [name2, node2] of allProps) {
								for (const refNode of node2._refs) {
									if (refNode.start >= node.start && refNode.start < node.end) {
										node2._refs.delete(refNode)
									}
								}
							}
						}
					}
					if (filtered) {
						continue
					}
					break
				}
			}
			findUnusedProps()
			unusedProps = [...allProps].filter(([n,p])=>p._unused)
			allProps.forEach((p, n) => p._unused && allProps.delete(n))
			allProps.forEach((p, n) => p._forbidden && allProps.delete(n))
			function filterByCriteria() {
				allProps.forEach((propNode, name)=>{
					var numRefs = propNode._refs && propNode._refs.size||0
					var isIdentifier = propNode.type == "Identifier"
					var isLiteral = propNode.type == "Literal"
					var isMethod = propNode.type == "FunctionExpression" && (propNode.parent.method || propNode.parent.kind == "method")
					
					var ok = numRefs == 1 
						|| isLiteral && typeof propNode.value == "string" && numRefs > 1 && numRefs < 3
						|| isLiteral && typeof propNode.value == "number" && numRefs > 1 && numRefs < 5
						|| isIdentifier
						
					if (!ok) {
						allProps.delete(name)
						return 
					}
					
					var isValidMethod
					if (isMethod) {
						checkMethod()
						function checkMethod() {
							var functionNode = propNode
							if(functionNode.uses_arguments) return
							
							
							let refCallExpression = [...propNode._refs][0].parent
							var funcInfo = getFunctionInfo(propNode, refCallExpression, variableNamesChangeable)
							if (funcInfo) {
								propNode._isMethod = true
								propNode._funcInfo = funcInfo
								isValidMethod = true
							}
						}
					}
					
					if (!isValidMethod && isFunctionNode(propNode)) {
						allProps.delete(name)
					}
				})
			}
			filterByCriteria()
			function filterNonInlinables() {
				function findOutsideRefs() {
					for (const [name, propNode] of allProps) {
						propNode._outsideRefs = new Map
						var aScope = objScope
						do {
							for (const [,b] of aScope.bindings) {
								var refs = getRefsInScope(b.references, propNode)
								if (refs) {
									propNode._outsideRefs.set(b.name, [b, refs])
								}
							}
						} while (aScope = aScope.parent);
					}
				}
				function isInlinedToWithOutsideRefs_orMethodUnfinished(propNode) {
					let isVar = !propNode._isMethod
					for (const [name, otherInlinedPropNode] of allProps) {
						if(isVar && !otherInlinedPropNode._outsideRefs.size) continue
						if(otherInlinedPropNode == propNode) continue
						for (const refNode of otherInlinedPropNode._refs) {
							if (refNode.start >= propNode.start && refNode.start < propNode.end) {
								return true
							}
						}
					}
				}
				function findCoveringBindings() {
					for (const [name, propNode] of allProps) {
						for (const refNode of propNode._refs) {
							var refScope = scan.nearestScope(refNode, true) || scan.nearestScope(refNode)
							var commonScope = objScope
							var outsideBindings = propNode._outsideRefs
							var aScope = refScope
							var coveringBindings = []
							do {
								if(commonScope == aScope) break
								for (const [,b] of aScope.bindings) {
									if(outsideBindings.has(b.name)){
										coveringBindings.push(b)
									}
								}	
							} while (aScope = aScope.parent);
							if(coveringBindings.length) {
								refNode._covOutRefs = coveringBindings
							}
						}
					}
					
				}
				function checkMethodArgumentNameCollisions() {
					var has
					for (const [name, propNode] of allProps) {
						if(!propNode._isMethod) continue
						var methodScope = scan.scope(propNode)
						for (const refNode of propNode._refs) {
							let refCallExpressionNode = [...propNode._refs][0].parent
							for (var i = 0; i < refCallExpressionNode.arguments.length; i++) {
								var arg = refCallExpressionNode.arguments[i]
								walk(arg, n=>{
									var binding = scan.binding(n)
									if (binding && methodScope.bindings.has(binding.name)) {
										has = true
										return "end"
									}
								})
								if (has) {
									propNode._hasArgNameCols = true
								}
							}
						}
					}
					
				}
				checkMethodArgumentNameCollisions()
				
				findOutsideRefs()
				allProps.forEach((propNode, name)=>{
					if (propNode._outsideRefs.size && !propNode._isMethod && propNode._outsideRefs.some(([n,[b, rs]]) => {
						return !(b.definition.parent.type === 'VariableDeclarator' && b.definition.parent.parent.kind == "const")
					})) {
						allProps.delete(name) 
					}
				})
				
				allProps.forEach((propNode, name)=>{
					if (isInlinedToWithOutsideRefs_orMethodUnfinished(propNode)) {
						++_num_Pending
						allProps.delete(name)
					}
				})
				findCoveringBindings()
			}
			filterNonInlinables()	
			if(!variableNamesChangeable){
				allProps.forEach((propNode, name)=>{
					if (propNode._refs.some(r=>(r._covOutRefs && r._covOutRefs.length))) {
						allProps.delete(name)
					}
				})
				allProps.forEach((propNode, name)=>{
					if (propNode._hasArgNameCols) {
						allProps.delete(name)
					}
				})
			}
			else{
				allProps.forEach((propNode, name)=>{
					for (const refNode of propNode._refs) {
						var coveringBindings = refNode._covOutRefs
						if(!(coveringBindings && coveringBindings.length)) continue
						coveringBindings.forEach((b) => {
							let name = gimmeSomethingUnique()
							b.references.forEach(r=>r._rn = name)
						})
					}
					
				})
				allProps.forEach((propNode, name)=>{
					if (propNode._hasArgNameCols) {
						var methodScope = scan.scope(propNode)
						methodScope.bindings.forEach(b=>{
							let name = gimmeSomethingUnique()
							b.references.forEach(r=>r._rn = name)
						})
					}
				})
			}
		}
		try {
			getPropsAndFilterUnsuitables()
		} catch (error) {
			console.error(error)
		}
		if(!allProps.size && !unusedProps.length) return
		
		if (infoObject) {
			infoObject.inlined = allProps.size
			infoObject.inlinedProps = [...allProps].map(([n])=>n)
		}
		
		function getTransformedSrc(){
			var result = astTransformMS({src, ast, prevSourceMap:inputMap, parentChain:1, leave({update, node}){
				if(node._rn){
					update(node._rn, node)
				}
			}})
			var ctx = result.ctx
			
			function setInMovementInfo(node, inDepth=0) {
				let had = node._refDepth != null
				let depth = Math.max(inDepth, node._refDepth||0) 
				if(depth == inDepth || had) return 
				node._refDepth = depth
				if (node._refs) {
					for (const refNode of node._refs) {
						refNode._refDepth = depth
						for (const [name, propNode] of allProps) {
							if (refNode.start >= propNode.start && refNode.start < propNode.end) {
								if (propNode == node) {
									throw "circular reference in "+name
								}
								setInMovementInfo(propNode, inDepth+1)
							}
						}
					}
				}
				else{
					throw "no refs for "+node._name
				}
			}
			function getRefDepth(node) {
				if(node._refDepth != null) return node._refDepth 
				var depth = 0
				for (const [, propNode] of allProps) {
					if(!propNode._refs) continue
					for (const refNode of propNode._refs) {
						if (refNode.start >= node.start && refNode.start < node.end) {
							depth = Math.max(depth, refNode._refDepth + 1)
						}
					}
				}
				return depth
			}
			function sortKey(...changeables) {
				var refDepth = changeables.reduce((p, c) => Math.max(getRefDepth(c), p) , 0)
				var nDepth = changeables.reduce((p, c) => Math.max(getNodeDepth(c), p) , 0)
				var pos = changeables.reduce((p, c) => Math.min(c.start, p) , Infinity)
				return refDepth*281474976710656 + (281470681743360-nDepth*4294967296) + pos
			}
			for (const [name, propNode] of allProps) {
				setInMovementInfo(propNode)
			}
			
			var all_edits = []
			for (const [name, propNode] of allProps) {
				for (const refNode of propNode._refs) {
					if (propNode._isMethod) {
						all_edits.push([name, "inl_F", sortKey(refNode, propNode), refNode, propNode])
						
					} else {
						all_edits.push([name, "inl_V", sortKey(refNode), refNode, propNode])
						
					}
				}
			}
			var sortF = (a,b)=>a[2] - b[2]
			all_edits.sort(sortF)
			
			
			for (let i = 0; i < all_edits.length; i++) {
				const edit = all_edits[i];
				let [name, editType,,refNode, propNode] = edit
				let _new = []
				
				
				if (editType == "inl_F") {
					let refCallExpressionNode = refNode.parent
					editInlinedFunctionBody(propNode, propNode._funcInfo, refCallExpressionNode, ctx)
					let info = inlineFunctionBody(propNode, propNode._funcInfo, refCallExpressionNode, ctx)
					if(propNode._funcInfo.toPrependForExpression){
						_new.push(["prependFBE "+name, "prependFBE", sortKey(propNode._funcInfo.toPrependForExpression.targetStatement), [propNode._funcInfo.toPrependForExpression.targetStatement, refCallExpressionNode], propNode])
					}
					else if(info.toPrependForAssignment){
						if(!all_edits.find(t => t[3] == info.toPrependForAssignment.varDeclarationNode)){
							_new.push(["prependFBA "+name, "prependFBA", sortKey(info.toPrependForAssignment.varDeclarationNode), info.toPrependForAssignment.varDeclarationNode])
						}
					}
				}
				else if (editType == "inl_V"){
						
					let varSrc = ctx.source(propNode)
					let isNumberUsedLikeObject
					if (propNode.type == "Literal" && typeof propNode.value == "number" && refNode.parent.type == "MemberExpression") {
						isNumberUsedLikeObject = 1
					}
					let toNotWrapInRoundParantheses = ToNotWrapExpressionInRoundParantheses(propNode, refNode)
					if(!toNotWrapInRoundParantheses || isNumberUsedLikeObject){
						varSrc = "("+varSrc+")"
					}
					
					if (refNode.parent.type == "ExpressionStatement" && varSrc[0] == "(" && !isPreceededBy(refNode.parent, n=>n.type == "EmptyStatement")
					) {
						varSrc = ";"+varSrc
					}
					
					ctx.update(varSrc, refNode)
					
				}
				else if (editType == "prependFBA") { 
					let varDeclarationNode = refNode
					let chunks = []
					let curChunk = []
					let endIndex = varDeclarationNode.declarations.length-1
					for (let index = 0; index <= endIndex; index++) {
						let varDeclaratorNode = varDeclarationNode.declarations[index];
						let varName = varDeclaratorNode.id._rn || varDeclaratorNode.id.name
						let toPrependFunc = varDeclaratorNode._inlinedFunc
						if (DEBUG && toPrependFunc) {
							toPrependFunc = "\n\n/* "+varDeclaratorNode._name+" INLINED SATRT: *\/;\n" + toPrependFunc +"\n /* "+varDeclaratorNode._name+" INLINED END *\/\n"
						}
						if (toPrependFunc) {
							curChunk.push(varName)
							chunks.push(curChunk)
							chunks.push(toPrependFunc)
							curChunk = []
						}
						else{
							curChunk.push(ctx.source(varDeclaratorNode))
							if(index == endIndex) chunks.push(curChunk)
						}
						
					}
					let txt = ""
					chunks.forEach((c,i)=>{
						txt += i%2? c : varDeclarationNode.kind+" "+c.join(",")+";"
					})
					ctx.update(txt, varDeclarationNode)
					transform_addSemicolIfNeeded(varDeclarationNode, ctx)
				} 
				else if (editType == "prependFBE") { 
					let [statement, refCallExpressionNode] = refNode
					let returnVarName = propNode._funcInfo.toPrependForExpression.returnVarName
					let src = "let "+returnVarName+";"+statement._inlinedFunc
					if (DEBUG) {
						src = "\n\n/* "+propNode._name+" INLINED SATRT: *\/;\n" + src +"\n /* "+propNode._name+" INLINED END *\/\n"
					}
					ctx.prepend(src, statement)
					ctx.update(returnVarName, refCallExpressionNode)
				} 
				
				all_edits.splice(i, 1)
				--i
				if(_new.length) {
					all_edits.push(..._new)
					all_edits.sort(sortF)
				}
			}
		
			
			
			var toRemoveProps = new Set([...allProps].map(p=>p[1])
								.concat(unusedProps.map(p=>p[1])).map(p=>p.parent)
			)
			
			if (toRemoveProps.size) {
				if (cObj._isClass) {
					toRemoveProps.forEach(p => ctx.update("", p))
				} else {
					let isFormatted = /\s/.test(src[cObj.start+1])		
					let delim = ","
					if(isFormatted) delim += "\n"
					ctx.update( "{"+ cObj.properties.filter(p => !toRemoveProps.has(p)).map(p=>ctx.source(p)).join(delim) +"}", cObj)
				}
			}
			var resultCode = result.toString()
			if (withSourceMap) {
				inputMap = result.map
				options.map = inputMap
			}
			return resultCode
		}
		try {
			var transformed = getTransformedSrc()
		} catch (error) {
			console.error(error)
		}
		
		
		return transformed
	}
	
	var _offset = 0
	var _changes = 0
	while (1) {
		var _num_Pending = 0
		var _object_found = 0 
		try {
			var src2 = _inline()
		} catch (err) {
			console.error(err);
		}
		if(src2){
			src = src2
			++_changes
		}
		
		if (!_num_Pending) {
			if (!_object_found) {
				break
			}
			else{
				_offset += 3
			}
		}
	}
	return _changes && src
}
function sortScopeBindingsByPositionInCode(scope) {
	// The declaration node is at the top of binding.references, regardless of source position. 
	// The rest is sorted by source position
	for (const [id, binding] of scope.bindings) {
		if (binding.references.size >= 3) {
			var [declaration, ...refs] = [...binding.references]
			refs.sort((a, b) => a.start - b.start)
			// Set is stable by spec. It guarantees that it is iterated in the same order in which items have been added
			binding.references = new Set([declaration, ...refs])
		}
	}
	var children = scope.children
	if (children) {
		for (const child of children) {
			sortScopeBindingsByPositionInCode(child)
		}
	}
}
function JsEscapeString(string, quoteChar) { // Escape any string to be a valid JavaScript string literal between double quotes or single quotes.
	return ('' + string).replace(/["'`\\\n\r\u2028\u2029\u2003]/g, function (character) {
	  switch (character) {
		case '"':
		case '`':
		case "'":
			if(quoteChar !== character) return character
		case '\\':
		  return '\\' + character
		// Four possible LineTerminator characters need to be escaped:
		case '\n':
		  return '\\n'
		case '\r':
		  return '\\r'
		case '\u2028':
		  return '\\u2028'
		case '\u2029':
		  return '\\u2029'
		case '\u2003':
		  return '\\u2003'
	  }
	})
}
function isBindingInExcludedArea(binding, excludeNodes, _NOSHRINK_GLOBALS) {
	// Remove binding if all references are in excluded areas
	// Remove references that are in excluded areas
	if (_NOSHRINK_GLOBALS.includes(binding.name)) {
		return true
	}
	if (!excludeNodes?.size) {
		return false
	}
	for (const ref of binding.references) {
		var isInARange = excludeNodes.some(en => en.start < ref.start && en.end > ref.end)
		if (isInARange) {
			binding.references.delete(ref)
		}
	}
	return !binding.references.size
}
function getExcludeRanges(src, ast) {
	var ranges = []
	var funcNodes = new Set
	walk(ast, node=>{
		if (node.type === "FunctionDeclaration" || node.type === "FunctionExpression" || node.type === "ArrowFunctionExpression") {
			var hasMarker = src.slice(node.start - (EXCLUDE_FUNCTION_FROM_SHRINK_MARKER.length+13), node.start).includes(EXCLUDE_FUNCTION_FROM_SHRINK_MARKER)
			if (hasMarker) {
				ranges.push([node.start, node.end])
				funcNodes.add(node)
				return "jump"
			}
		}
	})
	return [ranges, funcNodes]
}


/** 
 * @typedef {Object} Options
 * @property {any} [all=false] - applies all shrinking options
 * @property {any} [literals=true] - shrink string literals
 * @property {any} [properties=true] - shrink all property names
 * @property {any} [variables=true] - shrink all variables names
 * @property {any} [undeclared=true] - shrink all undeclared globals
 * @property {any} [values=true] - shrink null, undefined, Infinity
 * @property {any} [this=true] - shrink all "this."
 * @property {any} [classObjects=false] - to inline class-object properties and to remove unused properties (see below)
 * @property {any} [allow0Gain=false] - whether to replace a string/property even if the character difference is 0
 * @property {"`"|'"'|"'"} [quote="`"] - the quote character to use. Default `
 * @property {string[]} [globalsToNotShrink=[]] - undeclared globals which are to be excluded
 * @property {number} [minPropertyNameLength=3] - property names below this length are not shrunk
 * @property {SourceMapOptions?} [sourceMap] - source map options if a source map is to be generated
 * @property {any} [debug=false] - prints some debug information
*/
/** 
 * @typedef {Object} SourceMapOptions
 * @property {any} [generateSourceMapObject=false] - whether to generate a source map object; it is written to the "options.sourceMap.map" property
 * @property {any} [generateSourceMapInline=false] - whether to generate and add an inline source map comment to the output
 * @property {SourceMap?} [map] - a prior source map object; this key will hold the new source map object if generateSourceMapObject is truthy
 * @property {string?} [fileName] - filename of the output script file; this is only used to set the "file" property of the source map object
 * @property {string?} [sourceMapUrl] - url of the source map file; if specified then a '//# sourceMappingURL=' comment is appended to the output
*/
/** 
 * @param {string} src - source code 
 * @param {Options} options 
 * @returns {string}
 */
function Shrink(src, options) {
	const _TO_SHRINK_ALL = options && "all" in options? options.all : false
	const _TO_SHRINK_ALL_STRING_LITERALS = _TO_SHRINK_ALL || (options && "literals" in options? options.literals : TO_SHRINK_ALL_STRING_LITERALS)
	const _TO_SHRINK_ALL_PROPERTY_NAMES = _TO_SHRINK_ALL || (options && "properties" in options? options.properties : TO_SHRINK_ALL_PROPERTY_NAMES)
	const _TO_SHRINK_ALL_UNDECLARED_GLOBALS = _TO_SHRINK_ALL || (options && "undeclared" in options? options.undeclared : TO_SHRINK_ALL_UNDECLARED_GLOBALS)
	const _TO_SHRINK_ALL_VARIABLES = _TO_SHRINK_ALL || (options && "variables" in options? options.variables : TO_SHRINK_ALL_VARIABLES_WHEN_POSSIBLE)
	const _TO_SHRINK_BUILTIN_VALUES = _TO_SHRINK_ALL || (options && "values" in options? options.values : TO_SHRINK_BUILTIN_VALUES)
	const _TO_SHRINK_ALL_THIS = _TO_SHRINK_ALL || (options && "this" in options? options.this : TO_SHRINK_ALL_THIS)
	const _MIN_PROPERTY_NAME_LENGTH = options && "minPropertyNameLength" in options? options.minPropertyNameLength : MIN_PROPERTY_NAME_LENGTH
	const _TO_REPLACE_ON_0_GAIN = options && "allow0Gain" in options? options.allow0Gain : TO_REPLACE_ON_0_GAIN
	const _CONST_DECLARATION_QUOTE_CHARACTER = options && "quote" in options && typeof options.quote == "string"? options.quote : CONST_DECLARATION_QUOTE_CHARACTER
	const _NOSHRINK_GLOBALS = options && "globalsToNotShrink" in options && typeof options.globalsToNotShrink == "object"? options.globalsToNotShrink : []
	const _TO_INLINE_CLASS_OBJECT_PROPERTIES_AND_REMOVE_UNUSED = _TO_SHRINK_ALL || (options && "classObjects" in options? options.classObjects : TO_INLINE_CLASS_OBJECT_PROPERTIES_AND_REMOVE_UNUSED)
	const _DEBUG = options && "debug" in options? options.debug : DEBUG
	
	const reg_declarationsMarker = new RegExp(`(?:\\/\\/|\\/\\*)[ \\t]*${DECLARATIONS_HERE_MARKER}[ \\t]*(?:\\r?\\n|\\*\\/)`, "g")
	var declarationsMarker = src.match(reg_declarationsMarker)
	
	
	var src_start_Length = src.length
	var srcInit = src
	var inputMap, inputMapInit
	const _TO_GENERATE_SOURCEMAP_OBJECT = options?.sourceMap?.generateSourceMapObject
	const _TO_GENERATE_SOURCEMAP_INLINE = options?.sourceMap?.generateSourceMapInline
	const _TO_GENERATE_SOURCEMAP = _TO_GENERATE_SOURCEMAP_OBJECT || _TO_GENERATE_SOURCEMAP_INLINE 
	const _INPUT_SOURCEMAP = options?.sourceMap?.map
	const _SOURCEMAP_FILENAME = typeof options?.sourceMap?.fileName === "string" && options.sourceMap.fileName
	const _SOURCEMAP_URL = typeof options?.sourceMap?.sourceMapUrl === "string" && options.sourceMap.sourceMapUrl
	if (_TO_GENERATE_SOURCEMAP) {
		inputMap = _INPUT_SOURCEMAP || convertSourceMap.fromSource(src)?.toObject();
		inputMapInit = inputMap
		src = convertSourceMap.removeComments(src);
	}
	
	// inlining ----------------------------------------------------------------------------------------------------------------------------------------------------------
	var numInlinedItems = 0
	
	// class object ----------------------------------------------------------------------------------------------------------------------------------------------------------
	var numInlinedClassPrperties = options && "inlinedClassPropsPre" in options && Number.isInteger(options.inlinedClassPropsPre)? options.inlinedClassPropsPre : 0
	var allInlinedClassPrperties = options && "inlinedClassPropsAllPre" in options && options.inlinedClassPropsAllPre instanceof Array? options.inlinedClassPropsAllPre : []
	if (_TO_INLINE_CLASS_OBJECT_PROPERTIES_AND_REMOVE_UNUSED) {
		let info = {}
		let options = {
			variableNamesChangeable: _TO_SHRINK_ALL_VARIABLES,
			infoObject: info,
			withSourceMap: _TO_GENERATE_SOURCEMAP,
			map: inputMap,
		}
		let src2 = inlineClassObjectProperties(src, options)
		if (src2) {
			src = src2
			numInlinedClassPrperties += info.inlined
			if(info.inlinedProps instanceof Array) allInlinedClassPrperties = allInlinedClassPrperties.concat(info.inlinedProps)
			numInlinedItems += numInlinedClassPrperties
			if (_TO_GENERATE_SOURCEMAP) inputMap = options.map
		}
	}
	
	// Shrinking "this"  ----------------------------------------------------------------------------------------------------------------------------------------------------------
	var estimated_this_Gain = 0, numThisReplaced = 0
	if (_TO_SHRINK_ALL_THIS && _TO_SHRINK_ALL_VARIABLES) {
		function shrinkAllThis() {
			var allThis = []
			function getAllThisInThisObject(rootNode) {
				var tuple
				walk(rootNode, n=>{
					if(n.type == "ThisExpression"){
						if(!tuple){
							tuple = [rootNode, []]
							allThis.push(tuple)
						}
						tuple[1].push(n)
					}
					if (n !== rootNode && (n.type === 'FunctionDeclaration' || n.type === 'FunctionExpression')) {
						getAllThisInThisObject(n)
						return "jump"
					}
				})
				
			}
			var ast = acorn.parse(src, {
				ecmaVersion: "latest",
			})
			getAllThisInThisObject(ast)
			if(!allThis.length) return 
			var changes = 0
			var numThisReplaced = 0
			var estimatedSumGain = 0
			var transformed = astTransformMS({src, ast, prevSourceMap:inputMap })
			var ctx = transformed.ctx
			allThis.forEach(t => {
				var len = t[1].length
				var gain = len*4 - (len*2+12)
				var gainOk = _TO_REPLACE_ON_0_GAIN? gain >= 0 : gain > 0
				if(!gainOk) return 
				var root = t[0]
				if(root.body && !(root.body instanceof Array)) root = root.body
				if(!(root.body && root.body instanceof Array && root.body.length)) throw "root body expected"
				var id = gimmeSomethingUnique()
				if(DEBUG) id = "this_"+changes+"_"
				t[1].forEach(n => ctx.update(id, n))
				ctx.prepend("var "+id+"=this;"+(DEBUG?"\n":""), root.body[0])
				++changes
				numThisReplaced += t[1].length
				estimatedSumGain += gain
			})
			if(!changes) return 
			var src2 = transformed.toString()
			src = src2
			if (_TO_GENERATE_SOURCEMAP){
				inputMap = transformed.map
			}
			return [estimatedSumGain, numThisReplaced]
		}
		estimated_this_Gain = shrinkAllThis() || 0
		if(estimated_this_Gain) [estimated_this_Gain, numThisReplaced] = estimated_this_Gain
	}
	

	// Shrinking Literals ----------------------------------------------------------------------------------------------------------------------------------------------------------
	var ast = acorn.parse(src, {
		ecmaVersion: "latest",
		// sourceType: "module",
	})
	scan.crawl(ast) 
	var rootScope = scan.scope(ast)
	
	
	var hasExcludes = src.includes(EXCLUDE_FUNCTION_FROM_SHRINK_MARKER)
	if (hasExcludes) {
		var excludeRanges = getExcludeRanges(src, ast, rootScope)
		var excludeNodes = excludeRanges?.[1]
		if (!excludeNodes?.size) {
			excludeNodes = null
		}
	}
	
	sortScopeBindingsByPositionInCode(rootScope)
	
	
	
	var stringLiterals = findAllStringLiterals(ast, _TO_SHRINK_ALL_PROPERTY_NAMES, _MIN_PROPERTY_NAME_LENGTH, excludeNodes)
	var all_string_literals = [...stringLiterals] 
		.filter(([str, tuple]) => {
			var nodes = tuple[0]
			
			var minNumOccurrences = str.length == 1? 4 : str.length == 2? 3 : 2
			return nodes.length >= minNumOccurrences
		})
	
	
		
	
	// get maximum length of new identifier for each string with positive net character gain  -----------------------------------------------------------------------------
	all_string_literals.forEach(t => t[4] = getMaxIdentifierLengthForPropsLiterals(t[0], _TO_REPLACE_ON_0_GAIN, t[1][1], t[1][2], t[1][3], t[1][4]))
	// filter out those with no positive gain
	all_string_literals = all_string_literals.filter(t => t[4] > 0)
	
	
	
	// get available identifiers for each literal -----------------------------------------------------------------------------
	var items_literals=[], items_builtins=[], items_undeclared=[]
	if(_TO_SHRINK_ALL_STRING_LITERALS) items_literals = all_string_literals.map(t => ["s", t[1][0].length, t])
	if(_TO_SHRINK_ALL_UNDECLARED_GLOBALS){
		let all_undeclared_bindings = [...rootScope.undeclaredBindings].map(x=>x[1])
		items_undeclared = all_undeclared_bindings
			.filter(b => b.references.size > 1 && b.name.length >= 3) // at least 2 occurrences and at least 3 characters long
			.filter(b => !isBindingExistenceChecked(b))
		if (excludeNodes || _NOSHRINK_GLOBALS.length) {
			items_undeclared = items_undeclared.filter(b => !isBindingInExcludedArea(b, excludeNodes, _NOSHRINK_GLOBALS))
		}
		items_undeclared = items_undeclared.map(binding => {
				var maxIdentifierLength = maxIdentifierLengthFor(binding.references.size, binding.name.length, _TO_REPLACE_ON_0_GAIN)
				return ["u", binding.references.size, binding, maxIdentifierLength]
			})
	}
	if (_TO_SHRINK_BUILTIN_VALUES) {
		items_builtins = [...findBuiltinValues(ast, excludeNodes)]
			.map(([name, nodes]) => {
				var maxIdentifierLength = maxIdentifierLengthFor(nodes.length, name.length, _TO_REPLACE_ON_0_GAIN)
				return ["b", nodes.length, nodes, maxIdentifierLength, name]
			})
	}
	
	var all_variables_Gain = 0
	var iife_wrapper_node = getIIFEBodyBlockNode(ast)
	var top_scope = iife_wrapper_node && scan.nearestScope(iife_wrapper_node) || scan.scope(ast)
	
	while(true){
		var debug_insufficientGainFor = []
		var undeclared_globals_to_replace = []
		var undeclared_globals_to_replace_variable = [], undeclared_globals_to_replace_constant = []
		var builtin_values_to_replace = []
		
		let all_items = [...items_literals, ...items_undeclared, ...items_builtins]
		all_items.sort(([, aLength], [, bLength]) => bLength - aLength)
		
		if (_TO_SHRINK_ALL_VARIABLES) {
			let items = all_items.map(item => {
				if(item[0] == "s"){
					return [null, item[1], item[2][1][0], item[2][4]]
				}
				else if(item[0] == "u"){
					return [null, item[1], item[2].references, item[3],]
				}
				else if(item[0] == "b"){
					return [null, item[1], item[2], item[3], item[4]]
				}
			})
			var topLevelScopeNode = iife_wrapper_node && iife_wrapper_node.parent || ast
			all_variables_Gain = obtainNewVariableIdentifiers(topLevelScopeNode, items)
			for (var i = 0; i < items.length; i++) {
				var conv = items[i];
				var orig = all_items[i];
				if (orig[0] == "s") {
					orig[2][2] = conv[0]
				}
				else if(orig[0] == "u"){
					if (conv[0]) {
						orig[2].id = conv[0] 
						undeclared_globals_to_replace.push(orig[2])
					}
				}
				else if(orig[0] == "b"){
					if (conv[0]) {
						builtin_values_to_replace.push([orig[4], conv[0], orig[2]]) // [name, id, nodes]
					}
				}
			}
			
		}
		else{
			let all_topLevel_variable_names = getAllScopeVariableNames(top_scope)
			var all_undeclared_set =  new Set([...rootScope.undeclaredBindings].map(x=>x[0]))
			let availableSkippedIdentifiers = new Set
			let nameCounter = -1
			
			literalsLoop: 
			for (const item of all_items) {
				let isLiterals, isGlobals, isBuiltins
				if (item[0] == "s") {
					isLiterals = 1
					var tuple = item[2]
					var occurrence_nodes = tuple[1][0]
					var maxNewIdentifierLength = tuple[4]
				} 
				else if (item[0] == "u"){
					isGlobals = 1
					var binding = item[2]
					var occurrence_nodes = binding.references
					var maxNewIdentifierLength = item[3]
				}
				else if (item[0] == "b"){
					isBuiltins = 1
					var name = item[4]
					var occurrence_nodes = item[2]
					var maxNewIdentifierLength = item[3]
				}
				else {
					throw "unknown item"
				}
				
				let setaname = (aname)=>{
					if (isLiterals) {
						tuple[2] = aname
					}
					else if(isGlobals){
						binding.id = aname
						undeclared_globals_to_replace.push(binding)
					}
					else if(isBuiltins){
						builtin_values_to_replace.push([name, aname, occurrence_nodes])
					}
				}
				var takenNames = getAllTakenNamesFor(occurrence_nodes)
				for (const aname of availableSkippedIdentifiers) {
					if(takenNames.has(aname)){
						continue
					}
					if(aname.length <= maxNewIdentifierLength){
						setaname(aname)
						availableSkippedIdentifiers.delete(aname)
						continue literalsLoop
					}
				}
				
				while (true) {
					let aname = base54(++nameCounter)
					if(keywords.has(aname)) continue
					if (all_undeclared_set.has(aname)) {
						continue
					}
					if(all_topLevel_variable_names.has(aname)){ // the toplevel scope variables are disallowed for everybody
						continue
					}
					if(takenNames.has(aname)){
						availableSkippedIdentifiers.add(aname)
						continue
					}
					if(aname.length <= maxNewIdentifierLength){
						availableSkippedIdentifiers.delete(aname)
						setaname(aname)
						continue literalsLoop
					}
					else{ // generated name is too long for this literal to be worth replacing
						if (isLiterals) {
							tuple[2] = null
							_DEBUG && debug_insufficientGainFor.push({
								literal: tuple[0],
								maxIdentifierLength: maxNewIdentifierLength,
								availableIdentifierLength: aname.length,
							})
						}
						continue literalsLoop
					}
				}
			}
		}
		
		
		// variable undeclared globals must be in a separate "let ;" statement because they are not constant
		// if the gain is not enough for the "let" statement then omit the globals and recreate the variables without the globals competing for them
		var undeclared_globals_Gain = 0
		var undeclared_globals_variable_Gain = 0
		var undeclared_globals_constant_Gain = 0
		var sumGain_let = 0
		if (_TO_SHRINK_ALL_UNDECLARED_GLOBALS && undeclared_globals_to_replace.length) {
			var reduceGainFunctionUndeclaredGlobals = (sum, b) =>{
				var decl_cost = b.name.length + b.id.length + 2
				var gain = (b.name.length - b.id.length) * b.references.size
				return sum + gain - decl_cost
			}
			undeclared_globals_to_replace.forEach(binding => {
				if (isVariableAssignedTo(binding)) {
					undeclared_globals_to_replace_variable.push(binding)
				}
				else {
					undeclared_globals_to_replace_constant.push(binding)
				}
			})
			undeclared_globals_variable_Gain = undeclared_globals_to_replace_variable.reduce(reduceGainFunctionUndeclaredGlobals, 0)
			undeclared_globals_constant_Gain = undeclared_globals_to_replace_constant.reduce(reduceGainFunctionUndeclaredGlobals, 0)
			undeclared_globals_Gain = undeclared_globals_variable_Gain + undeclared_globals_constant_Gain
			
			var sumGain_let = undeclared_globals_variable_Gain
			sumGain_let -= 4 // "let;"
			var isGainOk_let = _TO_REPLACE_ON_0_GAIN? sumGain_let >= 0 : sumGain_let > 0
			if(!isGainOk_let && undeclared_globals_to_replace_variable.length && (_TO_SHRINK_ALL_STRING_LITERALS || _TO_SHRINK_ALL_PROPERTY_NAMES || _TO_SHRINK_BUILTIN_VALUES)){
				items_undeclared = items_undeclared.filter(item => !undeclared_globals_to_replace_variable.includes(item[2]))
				undeclared_globals_to_replace_variable.length = 0
				undeclared_globals_to_replace = undeclared_globals_to_replace_constant
				continue
			}
		}
		break
	}
	
	all_string_literals = all_string_literals.filter(t => t[2] != null)
	all_string_literals.forEach(t => t[5] = getCharacterGain(t[0].length, t[2].length, t[1][1], t[1][2], t[1][3], t[1][4]))
	if (!_TO_REPLACE_ON_0_GAIN) {
		all_string_literals = all_string_literals.filter(t => t[5] > 0)
	}
	
	
	// calculate sizes -----------------------------------------------------------------------------
	var literalsAndProps_Gain = 0
	if (_TO_SHRINK_ALL_STRING_LITERALS || _TO_SHRINK_ALL_PROPERTY_NAMES) {
		literalsAndProps_Gain = all_string_literals.reduce((sum, t) => t[5] + sum, 0)
	}
	
	var builtin_values_Gain = 0
	if (_TO_SHRINK_BUILTIN_VALUES && builtin_values_to_replace.length) {
		builtin_values_Gain = builtin_values_to_replace.reduce((sum, b) =>{
			var decl_cost = b[0].length + b[1].length + 2
			var gain = (b[0].length -  b[1].length) * b[2].length
			return sum + gain - decl_cost
		}, 0)
	}
	var sumGain_const = literalsAndProps_Gain + builtin_values_Gain + undeclared_globals_constant_Gain
	sumGain_const -= 6 // "const;"
	var isGainOk_const = _TO_REPLACE_ON_0_GAIN? sumGain_const >= 0 : sumGain_const > 0
	var sumGain = (isGainOk_const? sumGain_const : 0) + (isGainOk_let? sumGain_let : 0) + all_variables_Gain
	if(!isGainOk_const && !isGainOk_let && !all_variables_Gain && !numInlinedItems){
		console.log("gain not big enough", sumGain);
		return false
	}
	var _allReplacements = all_string_literals.length + undeclared_globals_to_replace_variable.length + undeclared_globals_to_replace_constant.length + builtin_values_to_replace.length
	if (!_allReplacements && !_TO_SHRINK_ALL_VARIABLES && !numInlinedItems) {
		console.log("no suitable replacements available");
		return false
	}
	
	// create the declaration statement (eg. `const a="literal1", b=.....;`) -----------------------------------------------------------------------------
	var declaration_string = ""
	var declaration_string_safe = ""
	if (isGainOk_const) {
		declaration_string += "const " + all_string_literals.map(t => {
			var escaped = t[0]
			escaped = JsEscapeString(escaped)
			if (_CONST_DECLARATION_QUOTE_CHARACTER === "`") {
				escaped = escaped.replace(/\$\{/g, "\\${")
			}
			return t[2] + "=" + _CONST_DECLARATION_QUOTE_CHARACTER + escaped + _CONST_DECLARATION_QUOTE_CHARACTER
		})
		.concat(builtin_values_to_replace.map(b => 
			b[1] + "=" + b[0]
		))
		.concat(undeclared_globals_to_replace_constant.map(b => 
			b.id + "=" + b.name
		))
		.join(",") + ";"
		
		declaration_string_safe += declaration_string
	}
	if (isGainOk_let) {
		let undeclared_globals_declaration = "let " + undeclared_globals_to_replace_variable.map(b => 
			b.id + "=" + b.name
		)
		.join(",") + ";"
		let undeclared_globals_declaration_safe = "let " + undeclared_globals_to_replace_variable.map(b => 
			b.id + "=" + `typeof ${b.name} !== ${_CONST_DECLARATION_QUOTE_CHARACTER}undefined${_CONST_DECLARATION_QUOTE_CHARACTER}?${b.name}:void 0`
		)
		.join(",") + ";"
		declaration_string += undeclared_globals_declaration
		declaration_string_safe += undeclared_globals_declaration_safe
	}
	
	
	
	// replace literals -----------------------------------------------------------------------------
	var stringLiterals_nodesMap = new Map // node => identifier
	if (isGainOk_const) {
		all_string_literals.forEach(t => t[1][0].forEach(n => stringLiterals_nodesMap.set(n, t)))
	}
	if (_TO_SHRINK_ALL_UNDECLARED_GLOBALS) {
		var undeclared_globals_nodesMap = new Map // node => Binding
		if (isGainOk_let || isGainOk_const) {
			undeclared_globals_to_replace.forEach(b => b.references.forEach(n => undeclared_globals_nodesMap.set(n, b)))
		}
	}
	if (_TO_SHRINK_BUILTIN_VALUES) {
		var builtin_values_nodesMap = new Map // node => Binding
		if (isGainOk_const) {
			builtin_values_to_replace.forEach(b => b[2].forEach(n => builtin_values_nodesMap.set(n, b)))
		}
	}
	
	var debugInfo = {
		replacedPropertyNames: new Set,
		replacedLiterals: new Set,
		replacedUndeclared: new Set,
	}
	var result = astTransformMS({src, ast, parentChain:1, prevSourceMap:inputMap, leave({update, source, node}){
			var undeclared_global_binding
			var builtin
			var l_tuple
			if (l_tuple = stringLiterals_nodesMap.get(node)) {
				var id = l_tuple[2]
				var name = l_tuple[0]
				var isIdentifier = node.type == "Identifier"
				if (_TO_SHRINK_ALL_PROPERTY_NAMES) {
					var needsPropertyKeyBrackets = false
					let isObjectKey = node.parent.type == "Property" && node.parent.key == node
					let isPropertyMemberKey = node.parent.type == "MemberExpression" && node.parent.property == node
					var isPropertyKey = isObjectKey || isPropertyMemberKey

					if (isPropertyKey) {
						var isComputed = node.parent.computed
						if (!isComputed) {
							needsPropertyKeyBrackets = true
						}
						
						if(isComputed){
							caseDelta = -2
						}
						else if (isIdentifier) {
							caseDelta = isObjectKey ? 2 : 1
						}
						else{
							caseDelta = 0
						}
						
						var diff = name - id - caseDelta
						if(diff < 0 || diff == 0 && !_TO_REPLACE_ON_0_GAIN) return
						
						if (needsPropertyKeyBrackets) {
							id = "["+id+"]"
							// // Fix: shorthand: {prop}
							if (!_TO_SHRINK_ALL_VARIABLES) {
								if (isObjectKey &&  node.parent.value.type === "Identifier" && node.parent.value.start === node.start) {
									return
								}
							}
						}
						
						
						if (_DEBUG) {
							if (!debugInfo.replacedPropertyNames.has(name)) {
								debugInfo.replacedPropertyNames.add(name)
							}
							
						}
					}
				}
				else{ // literal
					var diff = name - id + 2
					if(diff < 0 || diff == 0 && !_TO_REPLACE_ON_0_GAIN) return
				}
				
				if (_DEBUG) {
					if (!isPropertyKey) {
						if (!debugInfo.replacedLiterals.has(name)) {
							debugInfo.replacedLiterals.add(name)
						}
					}
					
				}
				
				// Fixes: return"something"
				if (isJsAlphanum(src[node.start-1])) {
					id = " "+id
				}
				// Fixes: "something"in object1
				if (isJsAlphanum(src[node.end])) {
					id = id+" "
				}
				
				update(id, node)
			}
			// Fix: "object.[A]" => "object[A]"
			else if(node.type == "MemberExpression" && node.computed == false && !node.optional && stringLiterals_nodesMap.has(node.property)){
				// remove "."
				var curSrc = source(node)
				var i = curSrc.lastIndexOf(".")
				if(i > 0){
					var newSrc = curSrc.slice(0, i) + curSrc.slice(i+1)
					update(newSrc, node)
				}
			}
			else if(_TO_SHRINK_ALL_UNDECLARED_GLOBALS && (undeclared_global_binding = undeclared_globals_nodesMap.get(node))){
				if (_DEBUG) {
					debugInfo.replacedUndeclared.add(undeclared_global_binding.name)
				}
				update(undeclared_global_binding.id, node)
			}
			else if(_TO_SHRINK_ALL_VARIABLES && (node.type == "Identifier" && node._v)){
				// Fix: destructuring shorthand: var {prop} = object
				if (node.parent.type === "Property" && node.parent.value === node && node.parent.key.start === node.start) {
					let propertySrc = source(node.parent.key)
					if (propertySrc !== node._v) {
						update(`${propertySrc}:${node._v}`, node)
					}
				}
				else{
					update(node._v, node)
				}
			}
			else if(_TO_SHRINK_BUILTIN_VALUES && (builtin = builtin_values_nodesMap.get(node))){
				update(builtin[1], node)
			}
			else if(!declarationsMarker && iife_wrapper_node && node === iife_wrapper_node){
				var blockWithConstDeclarations = "{" + declaration_string + source(node).slice(1)
				update(blockWithConstDeclarations, node)
			}
		}
	})
	
	if (declarationsMarker) {
		let optionalNewline = declarationsMarker[0][declarationsMarker[0].length-1] === "\n"? "\n" : ""
		result.replace(reg_declarationsMarker, declaration_string + optionalNewline)
	}
	else if (!iife_wrapper_node) {
		result.prepend(declaration_string)
	}
	
	// check for ADD_DECLARATIONS_MARKER for adding the declarations in a string (for when worker code is built for example)
	if(declaration_string){
		declaration_string = declaration_string.replaceAll("\\", "\\\\")
		declaration_string = declaration_string.replaceAll(_CONST_DECLARATION_QUOTE_CHARACTER, "\\"+_CONST_DECLARATION_QUOTE_CHARACTER)
		declaration_string_safe = declaration_string_safe.replaceAll("\\", "\\\\")
		declaration_string_safe = declaration_string_safe.replaceAll(_CONST_DECLARATION_QUOTE_CHARACTER, "\\"+_CONST_DECLARATION_QUOTE_CHARACTER)
		let reg_ADD_DECLARATIONS_MARKER = new RegExp(`["'\`]?${ADD_DECLARATIONS_MARKER}["'\`]?`, "g")
		let reg_ADD_DECLARATIONS_MARKER_SAFE = new RegExp(`["'\`]?${ADD_DECLARATIONS_MARKER_SAFE}["'\`]?`, "g")
		result.replace(reg_ADD_DECLARATIONS_MARKER, declaration_string)
		result.replace(reg_ADD_DECLARATIONS_MARKER_SAFE, declaration_string_safe)
	}
	
	
	if (_SOURCEMAP_URL && !_TO_GENERATE_SOURCEMAP_INLINE && _TO_GENERATE_SOURCEMAP_OBJECT) {
		result.append("\n//# sourceMappingURL="+_SOURCEMAP_URL)
	}
	var addSourceContentToSourceMap = !inputMapInit && _TO_GENERATE_SOURCEMAP_INLINE
	var resultCode = result.toString(!!_TO_GENERATE_SOURCEMAP_INLINE, addSourceContentToSourceMap && [srcInit], _SOURCEMAP_FILENAME)
	if (_TO_GENERATE_SOURCEMAP_OBJECT) {
		options.map = result.map
	}
	
	// debug
	var realGain = src.length - resultCode.length
	var totalGain = src_start_Length - resultCode.length
	var debugInfo = {
		shrinkGain_real: realGain,
		shrinkGain_predicted: sumGain,
		discr: realGain-sumGain,
		totalGain,
		literalsAndProps_Gain,
		undeclared_globals_Gain,
		all_variables_Gain,
		estimated_this_Gain,
		numThisReplaced,
		numInlinedClassPrperties,
		allInlinedClassPrperties,
		debugInfo,
		debug_insufficientGainFor,
	}
	if (options) options.debugInfo = debugInfo
	if(_DEBUG) {
		console.log(debugInfo);
	}
	return resultCode
}
module.exports = Shrink 
Shrink.inlineClassObjectProperties = inlineClassObjectProperties







