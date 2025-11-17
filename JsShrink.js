



const DEBUG = 0
const CONST_DECLARATION_QUOTE_CHARACTER = "`"
const TO_SHRINK_ALL_STRING_LITERALS = 1
const TO_SHRINK_ALL_PROPERTY_NAMES = 1
const TO_SHRINK_ALL_UNDECLARED_GLOBALS = 1
const TO_SHRINK_ALL_VARIABLES_WHEN_POSSIBLE = 1
const TO_SHRINK_BUILTIN_VALUES = 1 
const TO_SHRINK_ALL_THIS = 1
const MIN_PROPERTY_NAME_LENGTH = 3
const TO_REPLACE_ON_0_GAIN = 0
// class objects
const TO_INLINE_CLASS_OBJECT_PROPERTIES_AND_REMOVE_UNUSED = 0
// comment markers
const CLASS_OBJECT_MARKER = "CLASS_OBJECT"
const CLASS_OBJECT_MARKER_PENDING = "CLASS_OBJECT_PENDING"
const CLASS_OBJECT_MARKER__KEEP_PROPERTY = "JSSHRINK_CLASS_OBJECT__KEEP_PROPERTY"
const CLASS_OBJECT_MARKER__DONT_INLINE_HERE = "JSSHRINK_CLASS_OBJECT__DONT_INLINE_HERE"
const EXCLUDE_FUNCTION_FROM_SHRINK_MARKER = "!EXCLUDE!"
const DECLARATIONS_HERE_MARKER = "__JSSHRINK_DECLARATIONS_HERE__"




const acorn = require("acorn");
const scan = require('./scope-analyzer')
const {astTransformMS, bsGetIndexOfNearest} = require("./transform-ast");
const convertSourceMap = require('convert-source-map')
/** @import { SourceMap } from 'magic-string' */
/** @import { Node } from 'acorn' */
/** @import { Binding } from './scope-analyzer' */

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
	// if ast_node is a script wrapped in a IIFE without arguments, then returns the block node of that IIFE
	if(ast_node.type != "Program") return
	var n = ast_node.body
	if(n.length != 1) return
	n = n[0]
	if(n.type != "ExpressionStatement") return
	n = n.expression
	if(n.type == "UnaryExpression"){ // if: !function(){...}()
		if (n.operator != "!") return
		n = n.argument
	}
	if (n.type != "CallExpression") return
	if(n.arguments.length != 0) return
	n = n.callee
	if(n.type != "FunctionExpression" && n.type != "ArrowFunctionExpression") return
	n = n.body
	if(n.type != "BlockStatement") return
	// n = n.body
	return n
}
function obtainNewVariableIdentifiers(ast_node, otherIdentifiersInThisScope, customGlobalReservedNames) {
	function areRefsInScope(referencedNodesSet, scopeNode) {
		var i=0
		for (const refNode of referencedNodesSet) {
			// The first entry is the declaration. The declaration can be below the block, and below the first ref. Check for that case.
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
		var unsafeNames
		var variableItems = [...scope.bindings]
			.filter(x => { 
				if (x[1].hasRefsInWith) {
					unsafeNames ??= new Set
					unsafeNames.add(x[0])
					return false
				}
				return true
			}) 
			.map(x=>[null, x[1].references.size, x[1].references, 100, x[1].name, "_v"])
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
				if (canTake(aname, scope, node) && !unsafeNames?.has(aname)) {
					var maxIdLength = t[3]
					if(aname.length > maxIdLength){
						t[0] = null
						--nameCounter
						continue varsLoop
					}
					t[0] = aname
					var nodes = t[2]
					if (nodes) {
						nodes = nodes.references || nodes
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
function findAllLiterals(ast_node, comments, toIncludePropertyKeys=true, minPropertyKeyLength=1, excludeNodes, src, toIncludeNumbers_minLength) {
	function getNumber(node) {
		let n = node.value
		let origLen = node.end - node.start
		let seen = numbersSeen.get(n)
		var newStr
		if (seen) {
			newStr = seen
			var tuple = numbers.get(n)
		}
		else {
			let len
			if (typeof n === "number") {
				let hasFraction = n%1, str2
				newStr = n.toString()
				len = newStr.length
				str2 = n.toExponential().replace("+","")
				if (str2.length < len && Number(str2) === n) {
					len = str2.length
					newStr = str2
				}
				if (newStr.startsWith("0.")) {
					newStr = newStr.slice(1)
					--len
				}
				if (!hasFraction) {
					str2 = n.toString(16)
					if (str2.length+2 < len) {
						len = str2.length
						newStr = "0x"+str2
					}
				}
			}
			else if(typeof n === "bigint"){
				newStr = n.toString()+"n"
			}
			var maxIdentifierLength = Math.max(1, newStr.length-1)
			if (maxIdentifierLength > 1 && newStr.length >= toIncludeNumbers_minLength) {
				tuple = [[], newStr, 0, n, maxIdentifierLength, "", 0]
				numbers.set(n, tuple)
			}
			numbersSeen.set(n, newStr)
		}
		let gain = origLen - newStr.length
		if (DEBUG && gain < 0) {
			throw "gain < 0"
		}
		if (gain > 0) {
			node._shrunkNumber = newStr
		}
		if (tuple) {
			tuple[0].push(node)
			tuple[2] += gain
			tuple[6] += origLen
		}
	}
	
	var names = new Map
	/** @type {Map<number, [Node[], str:string, sumGain:number, numValue:number, maxIdentifierLength:number, varName:string, sumLengthOrig]} */
	var numbers = new Map
	var numbersSeen = new Map
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
			var isClassKey = (node.parent.type == "PropertyDefinition" || node.parent.type == "MethodDefinition") && node.parent.key == node
			var isPropertyMemberKey = node.parent.type == "MemberExpression" && node.parent.property == node
			var isPropertyKey = isObjectKey || isClassKey || isPropertyMemberKey
			
			if (isClassKey) {
				let propertyDefinition = node.parent
				let classBody = propertyDefinition.parent
				if (classBody.type !== "ClassBody") throw "ClassBody expected"
				let isFirst = classBody.body[0] === propertyDefinition
				var classKey_needsSemicol = !isFirst && !propertyDefinition.static && !propertyDefinition.computed
				if (classKey_needsSemicol) {
					let indexInBody = classBody.body.indexOf(propertyDefinition)
					let prev = classBody.body[indexInBody-1]
					if (prev.type === "MethodDefinition" || !prev.value) {
						classKey_needsSemicol = false
					}
					else {
						let hasSemicol = findNextIndexInJs(";", src, comments, prev.end, propertyDefinition.start) >= 0
						if (hasSemicol) classKey_needsSemicol = false
					}
				}
			}
			var caseDelta = -2
			if (isPropertyKey) {
					
				var isComputed = node.parent.computed
				var isOptional = node.parent.optional
				if (isLiteral) {
					if(typeof node.value === "string"){
						name = node.value
					}
					else if (toIncludeNumbers_minLength && (typeof node.value === "number" || typeof node.value === "bigint")) {
						getNumber(node)
						return
					}
					else return
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
						if (classKey_needsSemicol) {
							caseDelta = 3
						}
						else {
							caseDelta = isObjectKey || isOptional? 2 : 1
						}
					}
					else{ // {"a":
						caseDelta = 0
					}
				}
				
			}
			else if(isLiteral && typeof node.value == "string"){
				if (node.parent.type === "ExpressionStatement") {
					return
				}
				name = node.value
			}
			else if (toIncludeNumbers_minLength && (typeof node.value === "number" || typeof node.value === "bigint")) {
				getNumber(node)
				return
			}
			else if(isTemplateLiteral){
				name = templateLiteralValue
			}
			else{
				return
			}
			
			if(isPropertyKey) node._caseDelta = caseDelta
			if(classKey_needsSemicol) node._needsSemicol = true
			
			var tuple = names.get(name)
			if(!tuple){
				tuple = [[], 0, 0, 0, 0, 0]
				names.set(name, tuple)
			}
			var nodes = tuple[0]
			nodes.push(node)
			if(caseDelta == -2) tuple[1] += 1
			else if(caseDelta == 0) tuple[2] += 1
			else if(caseDelta == 1) tuple[3] += 1
			else if(caseDelta == 2) tuple[4] += 1
			else if(caseDelta == 3) tuple[5] += 1
			return
		}
	})
	let numbers2 = [...numbers.values()]
	/** @type {[names, numbers2]} */
	let ret = [names, numbers2]
	return ret
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
				if (node.name === "undefined" && !scan.getBinding(node)) {
					let b = scan.getBinding(node)
					if (b) {
						
					}
					else {
						var name = "void 0"
					}
				} 
				else if (node.name === "Infinity" && !scan.getBinding(node)){
					var name = "Infinity"
				}
			}
		}
		else if(node.type === "UnaryExpression" && node.operator === "void" 
			&& (node.argument.type === "Literal" || node.type == "TemplateLiteral" && node.expressions.length == 0 || node.argument.type === "Identifier")
		){
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
function getCharacterGain(origLiteralLength, newIdentifierLength, n_m2, n_p0, n_p1, n_p2, n_p3) {
	var diff = origLiteralLength - newIdentifierLength
	var gain = (diff+2)*n_m2 + (diff)*n_p0
	if (diff > 1) {
		gain += (diff-1)*n_p1
	}
	if (diff > 2) {
		gain += (diff-2)*n_p2
	}
	if (diff > 3) {
		gain += (diff-3)*n_p3
	}
	var declarationCost = origLiteralLength + newIdentifierLength + 2 + 2
	gain -= declarationCost
	return gain
}
function maxIdentifierLengthFor(num, origLength, allow0Gain, extraCost=0) {
	var cost = origLength+2+extraCost
	var maxLength = origLength-cost/(num+1)
	if(maxLength%1 == 0 && !allow0Gain) maxLength -= 1
	return maxLength
}
function getMaxIdentifierLengthForPropsLiterals(originalLiteral, toAllow_0_Gain, n_m2, n_p0, n_p1, n_p2, n_p3) {	
	var newIdentifierLength = 1
	while (true) {
		var gain = getCharacterGain(originalLiteral.length, newIdentifierLength, n_m2, n_p0, n_p1, n_p2, n_p3)
		var hasGain = toAllow_0_Gain? gain >= 0 : gain > 0
		if(!hasGain) break
		++newIdentifierLength
		if (newIdentifierLength > 10) {
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
				var ret = _walk(n, parent, prev, i)
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
function isNodeContainedIn(node, parent, canBeSame) {
	let parent_ = canBeSame? node : node.parent
	while (parent_) {
		if (parent_ === parent) return true
		parent_ = parent_.parent
	}
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
function isAssignmentTarget(node, includingDeclaration, includingUninitializedDeclaration, includingFunctionparam) { 
	let parent = node.parent
	if (parent.type == "UpdateExpression"
		|| parent.type == "AssignmentExpression" && parent.left == node
		|| includingDeclaration && (
			parent.type == "VariableDeclarator" && parent.id == node && (includingUninitializedDeclaration? true : parent.init)
			|| includingFunctionparam && isFunctionNode(parent) && parent.params.includes(node)
		)
	) {
		return parent
	}
	else if (parent.type == "Property" && parent.value == node && parent.kind == 'init'
	) {
		let parent2 = parent.parent
		if (parent2.type == "ObjectPattern") {
			return isAssignmentTarget(parent2)
		}
	}
	else if (parent.type == "ArrayPattern"
	) {
		return isAssignmentTarget(parent)
	}
	else if (parent.type === 'RestElement' && parent.argument == node) {
		return isAssignmentTarget(parent)
	}
	else if (parent.type == "AssignmentPattern" && parent.left == node
	) {
		return isAssignmentTarget(parent)
	}
}
function isVariableAssignedTo(binding, except) {
	for (const refNode of binding.references) {
		if(refNode === binding.definition) continue
		if(isAssignmentTarget(refNode, 1, 1) && !(except && except.includes(refNode))
		) return true
	}
}
function isPreceededBy(node, pred, checkAll) {
	var block = node
	while (!(block.type == "Program" || block.type == "BlockStatement")) {
		block = block.parent
	}
	var ni = block.body.indexOf(node)
	while (--ni >= 0) {
		var n = block.body[ni]
		if(pred(n, ni)) return true
		if(!checkAll) return
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
			char = ctx? ctx.srcOrig[nu.start] : nu.source()[0]
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
	|| node.type === "MemberExpression"
}
function hasExpressionCalls(node, OrThis) {
	var has = false
	walk(node, n=>{
		if (isCallNode(n)){
			has = true
			return "end"
		}
		if (OrThis && n.type === "ThisExpression"){
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
function getFunctionInfo(functionNode, refCallExpressionNode, variableNamesChangeable, src) {
	function checkStatements(functionNode) {
		var hasStatements = false
		var lastReturnNode = null
		var conditionalReturn = false
		if (functionNode.expression) {
			return {hasStatements:false, lastReturnNode:false}
		}
		var BlockStatement = functionNode.body
		if(BlockStatement.type != "BlockStatement") 
			throw "BlockStatement expected"
		var statements = BlockStatement.body
		let firstUnconditionalReturnStatement
		walk(functionNode.body, n=>{
			if (n.type === 'ReturnStatement') {
				if (n.parent === BlockStatement) {
					if (!firstUnconditionalReturnStatement) {
						firstUnconditionalReturnStatement = n
						if (!conditionalReturn) return "stop"
					}
					return "jump"
				}
				else {
					conditionalReturn = true
					return "stop"
				}
			}
			else if(isFunctionNode(n)){
				return "jump"
			}
		})
		lastReturnNode = firstUnconditionalReturnStatement
		
		var unreachable = false
		for (var i = 0; i < statements.length; i++) {
			var statement = statements[i];
			if (unreachable) {
				functionNode._unreachableNodes ??= []
				functionNode._unreachableNodes.push(statement)
				continue
			}
			if (statement.type != "ExpressionStatement" && statement.type != "EmptyStatement") {
				hasStatements = true
			}
			if (statement === firstUnconditionalReturnStatement) {
				unreachable = true
			}
		}
		
		return {hasStatements, lastReturnNode, conditionalReturn}
	}
	function hasFunctionDeclarations(functionNode) {
		var has = false
		var names = [[], new Set, []] // names, nodes, bindings
		walk(functionNode, n=>{
			if (n == functionNode) return
			if (n.type === 'FunctionDeclaration') {
				has = true
				names[0].push(n.id.name)
				names[1].add(n)
				names[2].push(scan.getBinding(n.id))
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
	var isCallSiteAVariableDeclarator = refCallExpressionNode.parent.type == "VariableDeclarator" 
										&& refCallExpressionNode.parent.id.type == "Identifier"
										&& refCallExpressionNode.parent.id
	var isCallSiteAnAssignmentExpression = refCallExpressionNode.parent.type == "AssignmentExpression" 
										&& refCallExpressionNode.parent.parent.type == "ExpressionStatement"
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
	var funcDeclarations = hasFunctionDeclarations(functionNode)
	if(funcDeclarations){
		if(funcDeclarations[2].some((b, i, arr) => isVariableAssignedTo(b))) return 
		if(!variableNamesChangeable) return
		functionNode._funDeclarations = funcDeclarations[1]
	}
	
	
	for (var i = 0; i < params.length; i++) {
		var paramNode = params[i]
		var arg = refCallExpressionNode.arguments[i]
		let identifier
		let defaultValueNode
		if(paramNode.type == "Identifier") identifier = paramNode
		else if(paramNode.type == "AssignmentPattern" && paramNode.left.type === "Identifier"){
			identifier = paramNode.left
			defaultValueNode = paramNode.right
		}
		else return
		var paramBinding = funcScope.bindings.get(identifier.name)
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
				if(canInlineParam && !defaultValueNode && (!arg || numReferences <= 3 && isSimpleArg && !isArgString || isArgIdentifier)){
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
	if(toCreateBlock && variableNamesChangeable && isCallSiteAVariableDeclarator){
		let varDeclaratorNode = refCallExpressionNode.parent
		let varDeclarationNode = varDeclaratorNode.parent
		toPrependForAssignment = {
			returnVarName: gimmeSomethingUnique(),
			varDeclaratorNode,
			varDeclarationNode,
		}
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
			if(!hasCallsBetween(anode, targetStatement, refCallExpressionNode, 1, 0, src)){
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
				let numAssignmentDeclarators = 0
				let hasComplicated
				let firstDeclarator
				n.declarations.forEach((d, i) => {
					if(d.id.type !== "Identifier") hasComplicated = 1
					if (d.init) {
						++numAssignmentDeclarators
						if (!firstDeclarator) firstDeclarator = d
					}
					else { 
						let hasNext = i < n.declarations.length-1
						let end = hasNext? n.declarations[i+1].start : d.end
						ctx.edit.remove(d.start, end)
					}
				})
				if (firstDeclarator) {
					ctx.edit.remove(n.start, firstDeclarator.start)
					if(hasComplicated && numAssignmentDeclarators.length == 1){
						ctx.prepend("0,", n) 
					}
					if (n.parent.type !== "ForStatement") {
						ctx.append(";", n)
					}
				}
				else {
					ctx.edit.remove(n.start, n.end)
				}
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
			let returnArgNode
			if(isCallSiteAStatement && lastReturnNode.argument.type == "Literal") returnArgNode = null
			else returnArgNode = lastReturnNode.argument
			if (functionInfo.toPrependForAssignment) {
				ctx.prepend(functionInfo.toPrependForAssignment.returnVarName + "=", returnArgNode)
			}
			else if (functionInfo.toPrependForExpression) {
				ctx.prepend(functionInfo.toPrependForExpression.returnVarName + "=", returnArgNode)
			}
			ctx.edit.remove(lastReturnNode.start, returnArgNode.start)
		}
		else{
			if(functionInfo.toPrependForAssignment){
				let lastBodyNode = bodyBlockNodes[bodyBlockNodes.length-1]
				ctx.append(";"+ctx.source(assignmentLeftNode) + "=void 0", lastBodyNode)
			}
		}
		let toConvertBlockIntoExpression = !functionInfo.toCreateBlock && functionInfo.isOriginallyABlock
		if(toConvertBlockIntoExpression){
			let lastExpression, numExpressions = 0, bodyBlockNodes_lastIndex = bodyBlockNodes.length - 1
			for (let i = 0; i < bodyBlockNodes.length; i++) {
				let bn = bodyBlockNodes[i];
				if (bn.type === "EmptyStatement") {
					ctx.edit.remove(bn.start, bn.end)
				}
				else {
					++numExpressions
					if(ctx.srcOrig[bn.end-1] == ";") ctx.edit.remove(bn.end-1, bn.end)
					if (lastExpression) ctx.append(",", lastExpression)
					lastExpression = bn.expression
				}
			}
			if(!lastReturnNode && !isCallSiteAStatement && lastExpression) ctx.append("void 0", lastExpression)
			
			let toNotWrapInRoundParantheses = isCallSiteAStatement || (
				bodyBlockNodes.length == 1 && ToNotWrapExpressionInRoundParantheses(bodyBlockNodes[0])
			)
			ctx.edit.remove(fBody.start, fBody.start+1)
			ctx.edit.remove(fBody.end-1, fBody.end) 
			
			if(!toNotWrapInRoundParantheses){
				ctx.prepend("(", fBody)
				ctx.append(")", fBody)
			}
			if (isCallSiteAStatement) {
				ctx.append(";", fBody)
			}
		}
		else{
			if (node._funDeclarations && node._funDeclarations.size) {
				let scopeFDs = new Map
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
					
					let name = d.id._rn || d.id.name
					ctx.update("", d.id) 
					ctx.prepend(name + "=", d)
					let assignments = scopeFDs.get(fscope)
					if (!assignments) {
						assignments = [block, []]
						scopeFDs.set(fscope, assignments)
					}
					assignments = assignments[1]
					assignments.push(d)
				}
				for (const [scope, [block, assignments]] of scopeFDs) {
					if (ctx.srcOrig[block.start] !== "{") {
						throw "expecting {"
					}
					for (let i = 0, endIndex = assignments.length-1; i < assignments.length; i++) {
						let assignment = assignments[i];
						if (i === 0) {
							ctx.prepend("let ", assignment)
						}
						let commaOrSemicol = i === endIndex? ";" : ","
						ctx.append(commaOrSemicol, assignment)
						ctx.move2(assignment.start, assignment.end, block.start+1)
						assignment._moved_ = true
					}
				}
			}
			
		}
		
		if (functionNode._unreachableNodes) {
			for (const unreachableNode of functionNode._unreachableNodes) {
				if (!unreachableNode._moved_) {
					ctx.remove2(unreachableNode.start, unreachableNode.end)
				}
			}
		}
	}
	else if(!ToNotWrapExpressionInRoundParantheses(fBody)){
		ctx.prepend("(", fBody)
		ctx.append(")", fBody)
	}
}
function inlineFunctionBody(functionNode, functionInfo, refCallExpressionNode, ctx) {
	var fBody = functionNode.body
	var toCreateBlock = functionInfo.toCreateBlock
	var editNode
	if (toCreateBlock) {
		var funcScopeBindings = scan.scope(functionNode).bindings
		var lets = []
		var paramsMap = new Map
		functionNode.params.forEach((p, i)=>{
			let callArg = refCallExpressionNode.arguments[i]
			let name, defaultValueNode
			if(p.type == "Identifier") name = p.name
			else if(p.type == "AssignmentPattern" && p.left.type === "Identifier"){
				name = p.left.name
				defaultValueNode = p.right
				if (callArg) {
					ctx.prepend("??", defaultValueNode)
				}
			}
			else throw "pattern parameter support not implemented"
			paramsMap.set(name, [callArg, defaultValueNode])
		})
		for (const [, b] of funcScopeBindings) {
			let name = b.definition._rn || b.name
			let callArg = paramsMap.get(b.name)
			if(callArg){
				let firstArgPart = callArg[0] || callArg[1]
				ctx.prepend(name + "=", firstArgPart)
				lets.push(callArg)
			}
			else{
				lets.push(name)
			}
		}
		if (lets.length) {
			if (typeof lets[0] === "string") {
				lets[0] = "{let "+lets[0]
			}
			else {
				let firstArgPart = lets[0][0] || lets[0][1]
				ctx.prepend("{let ", firstArgPart)
			}
			let firstNode
			for (let i = 0, endIndex = lets.length-1; i < lets.length; i++) {
				let _let = lets[i];
				let commaOrSemicol = i === endIndex? ";" : ","
				if (typeof _let === "string") {
					_let += commaOrSemicol
					lets[i] = _let
				}
				else {
					if (!firstNode) firstNode = _let
					let secondArgPart = _let[1] || _let[0]
					ctx.append(commaOrSemicol, secondArgPart)
				}
			}
			if (firstNode) {
				if (typeof lets[0] === "string") throw "node expected"
				let lastNode
				let combinedStringArgs = ""
				for (const _let of lets) {
					if (typeof _let === "string") {
						combinedStringArgs += _let
					}
					else {
						let firstArgPart = _let[0] || _let[1]
						let secondArgPart = _let[1] || _let[0]
						lastNode = secondArgPart
						if (combinedStringArgs) {
							ctx.prepend(combinedStringArgs, firstArgPart)
						}
						fBody._prependNodes ??= []
						fBody._prependNodes.push(firstArgPart)
						ctx.secureRange(firstArgPart.start, firstArgPart.end)
						if (firstArgPart !== secondArgPart) {
							fBody._prependNodes.push(secondArgPart)
							ctx.secureRange(secondArgPart.start, secondArgPart.end)
						}
					}
				}
				if (combinedStringArgs) {
					ctx.append(combinedStringArgs, lastNode)
				}
			}
			else {
				var toPrependLets = lets.join("")
			}
		}
		if (!functionInfo.hasFunctionBlockLets && functionInfo.isOriginallyABlock) {
			if (ctx.srcOrig[fBody.start] !== "{") {
				throw "expecting {"
			}
			if (ctx.edit.slice(fBody.start, fBody.start+1)[0] !== "{") {
				throw "expecting { 2"
			}
			ctx.edit.remove(fBody.start, fBody.start+1)
			ctx.edit.remove(fBody.end-1, fBody.end)
		}
		if (lets.length) { 
			ctx.append("}", fBody)
			if (toPrependLets) {
				ctx.prepend(toPrependLets, fBody)
			}
		}
		
		if (functionInfo.toPrependForAssignment) {
			if (functionInfo.isCallSiteAnAssignmentExpression) { 
				editNode = fBody 
			} 
			else if(functionInfo.isCallSiteAVariableDeclarator){
				let varDeclaratorNode = refCallExpressionNode.parent
				varDeclaratorNode._inlinedFunc = fBody
				if (DEBUG) {
					varDeclaratorNode._name = functionNode._name
				}
				var toPrependForAssignment = functionInfo.toPrependForAssignment
			}
			else throw "toPrependForAssignment error"
		}
		else if(functionInfo.toPrependForExpression){
			functionInfo.toPrependForExpression.targetStatement._inlinedFunc = fBody
			var toPrependForExpression = functionInfo.toPrependForExpression
		}
		else{
			editNode = fBody
		}
		
	}
	else{
		if (!functionInfo.hasFunctionBlockLets && functionInfo.isOriginallyABlock 
			&& !scan.scope(functionNode).bindings.size
			&& ctx.edit.slice(fBody.start, fBody.start+1) === "{"
		) {
			ctx.edit.remove(fBody.start, fBody.start+1)
			ctx.edit.remove(fBody.end-1, fBody.end)
		}
		editNode = fBody
	}
	
	if (editNode) {
		ctx.remove2(refCallExpressionNode.start, refCallExpressionNode.end)
		if (fBody._prependNodes) {
			for (const node of fBody._prependNodes) {
				ctx.move2(node.start, node.end, refCallExpressionNode.start)
			}
		}
		ctx.move2(fBody.start, fBody.end, refCallExpressionNode.start)
		transform_addSemicolIfNeeded(refCallExpressionNode, ctx)
		if (DEBUG) {
			ctx.edit.prependLeft(refCallExpressionNode.start, "/* "+functionNode._name+" INLINED SATRT: *\/")
			ctx.edit.appendRight(refCallExpressionNode.start, " /* "+functionNode._name+" INLINED END *\/")
		}
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
			if (!begin) {
				if (n.start < startNode.start) {
					if (n.end < startNode.start) {
						return "jump"
					}
					return
				}
				else if(n == startNode){
					begin = true
					if (!toCheckStartNodeToo) {
						return "jump"
					}
				}
				else if(n.start >= startNode.end){
					return "end" 
				}
			}
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
				check(n.object)
				if(end) return "end"
				check(n.property)
				if(end) return "end"
				if (n.parent && !(
						n.parent.type === "CallExpression" && n === n.parent.callee
					)
				) {
					has = true
					end = true
					return "end"
				}
				return "jump"
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
		}, null, 1)
	}
	check(rootNode)
	return has
}
function isBindingInScope(binding, targetNode) {
	let scopeNode = binding.scope?.scopeNode
	return !scopeNode || isNodeContainedIn(targetNode, scopeNode)
}
function sortScopeBindingsByPositionInCode(scope) {
	// The declaration node is at the top of binding.references, regardless of source position. 
	// The rest is sorted by source position
	for (const [id, binding] of scope.bindings) {
		if (binding.references.size >= 3) {
			var [declaration, ...refs] = [...binding.references]
			refs.sort((a, b) => a.start - b.start)
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
function JsEscapeString(string, quoteChar) {
	return ('' + string).replace(/["'`\\\n\r\u2028\u2029\u2003]/g, function (character) {
	  switch (character) {
		case '"':
		case '`':
		case "'":
			if(quoteChar !== character) return character
		case '\\':
		  return '\\' + character
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
		case '\0':
		  return '\\0'
	  }
	})
}
function indexOfSeparator(separator, strAboveOrBelow, below=true) {
	const comments = '(?:\\s*(?:\\/\\/.*\\r?\\n|\\/\\*(?:[\\s\\S](?!\\*\\/))*?(?:.|[\\s])?\\*\\/)*)*'
	let regStr = below? "^"+comments+"\\s*"+separator : separator+comments+"\\s*$"
	if (!separator && below) regStr = "^"+comments+"."
	let regs = indexOfSeparator.regs ??= new Map
	let reg = regs.get(regStr)
	if (!reg) {
		reg = new RegExp(regStr)
		regs.set(regStr, reg)
	}
	let match = strAboveOrBelow.match(reg)?.[0]
	if (!match) return -1
	return below? match.length-1 : strAboveOrBelow.length-match.length
}
function findNextIndexInJs(str, src, comments, start=0, end=src.length, backward) {
	if (!backward) {
		let commentIndex = bsGetIndexOfNearest(comments, start, true, "start")
		let nextComment
		if (commentIndex >= 0) {
			if (start < comments[commentIndex].end)  start = comments[commentIndex].end
		}
		nextComment = comments[++commentIndex]
		var iStr = 0
		var strLen = str.length
		for (let i = start; i < end; i++) {
			if (nextComment && i === nextComment.start) {
				i = nextComment.end
				nextComment = comments[++commentIndex]
			}
			while (src[i+iStr] === str[iStr] && iStr < strLen) ++iStr
			if (iStr >= strLen) return i
			iStr = 0
		}
		return -1
	}
	else {
		let commentIndex = bsGetIndexOfNearest(comments, end, true, "start")
		let nextComment
		if (commentIndex >= 0) {
			if (end < comments[commentIndex].end)  end = comments[commentIndex].start-1
		}
		nextComment = comments[--commentIndex]
		var strLen = str.length
		var iStr = 0
		for (let i = end; i >= start; i--) {
			if (nextComment && i === nextComment.end-1) {
				i = nextComment.start-1
				nextComment = comments[--commentIndex]
			}
			while (src[i-iStr] === str[strLen-1-iStr] && iStr < strLen) ++iStr
			if (iStr >= strLen) return i
			iStr = 0
		}
		return -1
	}
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
function hasCommentAnnotationInFront(src, node, comments, annotation, maxDistance=Infinity, toReturnCommentNode) {
	let commentIndex = bsGetIndexOfNearest(comments, node.start, true, "end")
	if (commentIndex < 0) return 
	if(src.slice(comments[commentIndex].end, node.start).trim() !== "") return 
	var i = commentIndex, c = 0
	while (i >= 0) {
		var comment = comments[i]
		var result = typeof annotation === "string"? comment.value.trimLeft().startsWith(annotation) : comment.value.match(annotation)
		if (result) {
			return toReturnCommentNode? comment : result
		}
		if (++c >= maxDistance) return 
		var prevComment = comments[i-1]
		if (!prevComment) return 
		let prevEnd = prevComment.end
		if(prevComment.type === "Block") prevEnd += 2
		let start = comment.start -2
		if (src.slice(prevEnd, start).trim() !== "") return 
		--i
	}
}
function forceArrowFunctions(ast, src, ms, comments) {
	function usesPrivateFunctionName(n) {
		if (n.id) {
			let b = scan.getBinding(n.id)
			return b && b.references.size > 1
		}
	}
	var numConvertedFunctions = 0
	var hoistingPointsVar = new Map
	var hoistingPointsLet = new Map
	walk(ast, n=>{
		let isFunctionDeclaration = n.type === 'FunctionDeclaration'
		let isFunctionExpression = n.type === 'FunctionExpression'
		if (!isFunctionDeclaration && !isFunctionExpression) return 
		if (n.uses_arguments || n.uses_this) return
		if (n.generator) return
		if (n.parent.type == "Property" && (n.parent.kind != "init" || n.parent.method) || n.parent.type == "MethodDefinition") return
		if (isFunctionExpression) {
			if (usesPrivateFunctionName(n)) return
		}
		var hasParams = n.params.length
		var init_start = n.start
		var async = n.async?"async":""
		if (hasParams) {
			var bracketIndex = findNextIndexInJs("(", src, comments, n.id?.start ?? n.start, n.end)
			if (DEBUG && bracketIndex < 0) throw "!bracketIndex"
			var init_end = bracketIndex
			ms.update(init_start, init_end, async)
			var bracketIndex2 = findNextIndexInJs(")", src, comments, n.start, n.body.start, 1)
			if (DEBUG && bracketIndex2 < 0) throw "!bracketIndex2"
			if (bracketIndex2+1 < n.body.start) {
				ms.update(bracketIndex2+1, n.body.start, "=>")
			}
			else {
				ms.prependRight(n.body.start, "=>")
			}
			
		}
		else {
			var init_end = n.body.start
			ms.update(init_start, init_end, async+"()=>")
		}
		if(isFunctionDeclaration) {
			if (n.id?.type !== "Identifier") {
				throw "n.id: Identifier expected"
			}
			var parentFunc = scan.getNearestScopeNode(n)
			var isStrict = parentFunc.isStrictMode
			var isLet = isStrict
			var points = isLet? hoistingPointsLet : hoistingPointsVar
			var pointDef = scan.getNearestScopeNode(n, 1)
			let arr = points.get(pointDef)
			if (!arr) {
				arr = []
				points.set(pointDef, arr)
			}
			arr.push(n)
		}
		++numConvertedFunctions
	})
	for (const points of [hoistingPointsVar, hoistingPointsLet]) {
		for (const [scopeNode, funcs] of points) {
			if (DEBUG && (scopeNode.type !== "BlockStatement" && scopeNode.type !== "Program")) {
				throw "scopeNode BlockStatement|Program expected"
			}
			let use_strict
			if (scopeNode.body.length) {
				let first = scopeNode.body[0]
				if (first.type === 'ExpressionStatement' && first.expression.type === 'Literal' && first.expression.value === 'use strict') {
					use_strict = first
				}
			}
			
			var isLet = points === hoistingPointsLet
			var decl = isLet? "let " : "var "
			if (use_strict && src[use_strict.end-1] != ";") decl = ";"+decl
			var first = funcs[0]
			for (const func of funcs) {
				let name = func.id._v || func.id.name
				let prependStr = name+"="
				if (func !== first) prependStr = ","+prependStr
				ms.prependRight(func.start, prependStr)
			}
			ms.prependRight(first.start, decl)
			let last = funcs[funcs.length-1]
			ms.appendLeft(last.end, ";")
			if (use_strict) {
				var targetIndex = scopeNode.body[1]?.start ?? use_strict.end
			}
			else {
				if (scopeNode.type === "Program") {
					let firstStatement = scopeNode.body.length && scopeNode.body[use_strict? 1 : 0]
					if (firstStatement) {
						var targetIndex = firstStatement.start
					}
					else {
						let i = indexOfSeparator("", src, 1)
						var targetIndex = i < 0? 0 : i
					}
				}
				else {
					var targetIndex = scopeNode.start
					if (src[targetIndex] == "{") ++targetIndex
				}
			}
			for (const func of funcs) {
				ms.move(func.start, func.end, targetIndex)
			}
		}
	}
	return numConvertedFunctions
}




/** 
 * @typedef {Object} InlineClassObjectPropertiesOptions
 * @property {any} [variableNamesChangeable=false]
 * @property {any} [classesNeedCommentMarker=false]
 * @property {any} [inlineConstantsMaxNumberOfTimes=3]
 * @property {any} [toAllowInliningOutsideOfTheClass=true]
 * @property {any} [withSourceMap=false]
 * @property {any} [rootIsStrictMode=false]
 * @property {{inlinedProps:Set<string>, removedUnusedProps:Set<string>}} [infoObject]
 * @property {SourceMap?} [map] - a prior source map object; this key will hold the new source map object if withSourceMap is truthy
*/
/** 
 * @param {string} src - source code 
 * @param {InlineClassObjectPropertiesOptions} options 
 * @returns {string}
*/
function inlineClassObjectProperties(src, options) {
	const variableNamesChangeable = options && "variableNamesChangeable" in options? options.variableNamesChangeable : false
	const classesNeedCommentMarker = options && "classesNeedCommentMarker" in options? options.classesNeedCommentMarker : false
	const toAllowInliningOutsideOfTheClass = options && "allowInliningOutsideOfTheClass" in options? options.allowInliningOutsideOfTheClass : true
	const inlineLiteralValues_maxNumberOfTimes = Math.max(1, Number(options?.["inlineConstantsMaxNumberOfTimes"]) || 3)
	const infoObject = options && "infoObject" in options? options.infoObject : null
	const withSourceMap = options && "withSourceMap" in options? options.withSourceMap : false
	const rootIsStrictMode = options && "rootIsStrictMode" in options? options.rootIsStrictMode : false
	let inputMap = options?.map
	
	function _inline() {
		
		
		/** @type {acorn.Comment[]} */
		var comments = []
		var ast = acorn.parse(src, {
			ecmaVersion: "latest",
			onComment: comments,
			// sourceType: "module",
		})
		scan.crawl(ast, {rootIsStrictMode})
		
		
		function findClassObject() {
			function hasMarker(node) {
				return hasCommentAnnotationInFront(src, node, comments, firstIteration? CLASS_OBJECT_MARKER : CLASS_OBJECT_MARKER_PENDING, 10, 1)
			}
			walk(ast, n=>{
				let comment
				if (n.type == "ObjectExpression" && _offset <= n.start && (comment = hasMarker(n))) {
					_offset = n.start
					cObj = n
					if (!firstIteration && comment) {
						cObj._comment_pending = comment
					}
					return "end" 
				}
				if ((n.type == "ClassDeclaration" || n.type == "ClassExpression") && _offset <= n.start && n.body && n.body.body 
					&& (!classesNeedCommentMarker && firstIteration || (comment = hasMarker(n)))
				) {
					_offset = n.start
					cObj = n
					cObj._isClass = 1
					if (!firstIteration && comment) {
						cObj._comment_pending = comment
					}
					return "end" 
				}
			})
		}
		function findAllObjectProperties() {
			var properties = cObj._isClass? cObj.body.body : cObj.properties
			var i = -1
			for (let propertyNode of properties) {
				++i
				if(cObj._isClass){
				}
				else{
					if (propertyNode.kind !== "init") continue
					
				}
				if (propertyNode.key.type == "Identifier" || propertyNode.key.type == 'PrivateIdentifier') {
					var name = propertyNode.key.name
				}
				else if(propertyNode.key.type == "Literal" && typeof propertyNode.key.value == "string"){
					var name = propertyNode.key.value 
				}
				else continue
				let valueNode = propertyNode.value
				if(hasExpressionCalls(valueNode, true)) continue
				_allProps.set(name, propertyNode)
				propertyNode._i = i
				propertyNode._isInClass = cObj._isClass
				propertyNode._cObj = cObj
				propertyNode._name = name
				if (valueNode) {
					valueNode._name = name
					if (isPropertyValueAlwaysInlinableLiteral(valueNode) || valueNode.type == "Identifier") {
						propertyNode._isPropertyValueAlwaysInlinable = true
					}
				}
			}
		}
		function isValidAssignment(node, safe=true) {
			var left, right, isDeclaration
			if(node.type === "AssignmentExpression"){
				let operator = node.operator
				if (operator === "=") {
					if (safe && isResultAccessible(node.parent)) {
						return false
					}
					
					left = node.left
					right = node.right
				}
				else return 
			}
			else if (node.type === 'VariableDeclarator' && node.init) {
				left = node.id
				right = node.init
				isDeclaration = true
			}
			else return
			return [left, right, isDeclaration]
			
			
						
						
			function isResultAccessible(node, canBeVariableDeclarator=true) {
				if (canBeVariableDeclarator && node.type == "VariableDeclarator") return false
				if (node.type == "LogicalExpression" || node.type == "BinaryExpression") {
					return isResultAccessible(node.parent, false)
				}
				var isVoided = node.type == "ExpressionStatement"
						|| node.type == "SequenceExpression" && (
							node.expression[node.expression.length-1] !== node || node.parent.type == "ExpressionStatement"
						)
				return !isVoided
			}
		}
		function IsBindingConstant(/** @type {Binding} */ binding, forProperties, addRefsiteChecker) {
			var _isConstant = true
			try {
				if (binding.isConst) return true
				if (binding._isConst2 !== undefined){
					if (binding._isConst2) return true
					if (forProperties){
						if(binding._isConst2_forProperties !== undefined) return binding._isConst2_forProperties
					}
					else return false
				}
				if (!binding.definition){
					return _isConstant = false
				}
				if (binding.references.size === 1) return true
				var _hasCheckedAssignment
				var assignmentNode, assignmentRef
				var initializerNode
				var assignmentFunction 
				var bindingScopeFunction
				if (!getAssignmentContext()) {
					return _isConstant = false
				}
				binding._assignmentNode = assignmentNode
				binding._assignmentRef = assignmentRef
				if (binding.isHoisted && (binding.definition.parent.type === "FunctionDeclaration" && binding.definition.parent.id == binding.definition) && !assignmentRef) return true
				if (!assignmentRef) return true
				var isInitializedAtDeclaration = binding.definition === assignmentRef
				var assignmentLoop
				var assignmentBranch
				var hasUndef = false
				if (binding.references.size <= (isInitializedAtDeclaration?1:2)) return true
				getLocationContext()
				if (!check_refs()){
					return _isConstant = false
				}
				return true
				
			} finally {
				binding._isConst2 = _isConstant && !hasUndef
				if (forProperties) {
					binding._isConst2_forProperties = _isConstant
				}
				if (addRefsiteChecker && _isConstant) {
					binding._isConstantAtNode = isConstantAtNode
				}
			}
			
			function check_refs() {
				if (assignmentLoop){
					if (forProperties) {
						return true
					}
					else return false 
				}
				return verify_functions_validRange()
			}
			function verify_functions_validRange(otherRefNode) {
				var defNode = binding.definition
				var bindingScopes = getScopes()
				if (otherRefNode) {
					if (otherRefNode === defNode || otherRefNode === assignmentRef) return false
					return isRefValid(otherRefNode)
				}
				for (const ref of binding.references) {
					if (ref === defNode || ref === assignmentRef) continue
					if (!isRefValid(ref)) {
						if (forProperties) ref._mightBeUndef = hasUndef = true
						else return false
					}
				}
				return true
				
				function isRefValid(ref) {
					let scopeNode = scan.getNearestScopeNode(ref, 0)
					let refLocationValid = isLocationValid(ref)
					if (refLocationValid === "inFuncOrMethod") return true
					let isRootRef = bindingScopes.has(scopeNode)
					if (isRootRef) {
						return refLocationValid
					}
					while (scopeNode) {
						let parentScopeNode = scan.getNearestScopeNode(scopeNode, 0)
						let isRootFunc = bindingScopes.has(parentScopeNode)
						if (isRootFunc) {
							if (scopeNode.type === "FunctionDeclaration") {
								let funcBinding = scan.getBinding(scopeNode.id)
								return isValidRootFuncBinding(funcBinding)
							}
							else {
								if (isLocationValid(scopeNode)) {
									return true
								}
								var [left] = isValidAssignment(scopeNode.parent, 1)||""
								if (!left) 
									return false
								let funcBinding = scan.getBinding(left)
								return isValidRootFuncBinding(funcBinding, left)
							}
						}
						scopeNode = parentScopeNode
					}
				}
				function getScopes() {
					let scopes = new Set
					let scope = scan.getNearestScopeNode(assignmentBranch, 0, 1)
					let root = bindingScopeFunction
					scopes.add(root)
					while(scope){
						scopes.add(scope)
						scope = scan.getNearestScopeNode(scope, 0)
						if (scope === root) break
					}
					return scopes
				}
				function isValidRootFuncBinding(funcBinding, assignmentRef) {
					let isConst = IsBindingConstant(funcBinding, 1)
					if (!isConst) 
						return false
					for (const ref of funcBinding.references) {
						if (ref === funcBinding.definition || ref === assignmentRef) continue
						if (!isLocationValid(ref)) 
							return false
					}
					return true
				}
				function isLocationValid(ref) {
					let afterAssignment = isAfterAssignment(ref)
					if (afterAssignment
						&& (assignmentBranch? (ref.start >= assignmentBranch.start && ref.end <= assignmentBranch.end): true)
					) {
						return afterAssignment
					}
				}
				function isAfterAssignment(referenceNode) {
					if (referenceNode !== assignmentRef && referenceNode.end <= assignmentNode.end){
						if (referenceNode.end <= initializerNode.start) {
							return false
						}
						let lastFunc
						let parent = referenceNode.parent
						while (parent) {
							if (initializerNode === parent) break
							if (isFunctionNode(parent)) {
								lastFunc = parent
							}
							parent = parent.parent
						}
						if (!lastFunc){
							return false
						}
						if (lastFunc === initializerNode){
						}
						else {
							parent = lastFunc
							while (parent) {
								if (parent === initializerNode) break
								if (parent.parent.parent.type === 'ClassBody') { 
									parent = parent.parent.parent.parent
								}
								else if(parent.parent.type === 'Property'){
									parent = parent.parent.parent
								}
								else if(parent.parent.type === 'ArrayExpression'){
									parent = parent.parent
								}
								else {
									return false
								}
							}
							if (DEBUG && !parent) throw "!parent"
						}
						return "inFuncOrMethod"
					}
					return true
				}
			}
			function getLocationContext() {
				let child = assignmentNode
				let parent = child.parent
				let scopeNode = binding.scope.scopeNode
				while (parent) {
					if (scopeNode === parent || assignmentFunction === parent){
						break
					}
					if (parent.type === 'IfStatement' && child !== parent.test
						|| parent.type === 'ConditionalExpression' && parent.test !== child 
						|| parent.type === 'LogicalExpression' && child === parent.right 
						|| parent.type === 'MemberExpression' && parent.optional && child === parent.property
						|| parent.type === 'SwitchStatement' && child !== parent.discriminant
					) {
						assignmentBranch = child
					}
					else if (parent.type === 'DoWhileStatement' && child !== parent.test
						|| parent.type === 'WhileStatement' && child !== parent.test
						|| parent.type === 'ForStatement' && child !== parent.test && child !== parent.init
					) {
						assignmentBranch = child
						assignmentLoop = parent
					}
					if (assignmentBranch) break
					child = parent
					parent = child.parent
				}
				assignmentBranch ||= assignmentFunction
				
				if (assignmentLoop){
					if (forProperties) {
						for (const ref of binding.references) {
							ref._mightBeUndef = true
						}
						hasUndef = true
					}
				}
			}
			function getAssignmentContext() {
				_hasCheckedAssignment = true
				for (const ref of binding.references) {
					let parent = ref.parent
					if (parent.type === "UpdateExpression") {
						return false
					}
					let _assignmentNode
					if (_assignmentNode = isAssignmentTarget(ref, 1)) {
						if (assignmentNode) return false 
						
						assignmentNode = _assignmentNode
						assignmentRef = ref
						if (assignmentNode.type == "AssignmentExpression") {
							initializerNode = assignmentNode.right
						}
						else if (assignmentNode.type == "VariableDeclarator") {
							initializerNode = assignmentNode.init
						}
					}
				}
				bindingScopeFunction = scan.getNearestScopeNode(binding.scope.scopeNode, 0, 1)
				if (assignmentNode) {
					assignmentFunction = scan.getNearestScopeNode(assignmentNode, 0) || bindingScopeFunction
				}
				return true
			}
			function isConstantAtNode(node) {
				let nodeScopeNode = scan.getNearestScopeNode(node, 1, 0)
				let bindingScopeNode = binding.scope.scopeNode
				if (!nodeScopeNode || !isNodeContainedIn(nodeScopeNode, bindingScopeNode, 1)) return false
				if (!_hasCheckedAssignment) getAssignmentContext()
				if (!assignmentNode) return true
				if (!assignmentFunction) getLocationContext()
				if (assignmentLoop) return false
				return verify_functions_validRange(node)
			}
		}
		function findSafeClassBindings() {
			function isReassigned(binding, validRight, infoObject) {
				let assignment1
				for (const ref of binding.references) {
					let parent = ref.parent
					if (parent.type === "UpdateExpression") {
						return true
					}
					var leftRight = isValidAssignment(parent)
					if (leftRight) {
						if (validRight !== leftRight[1] || assignment1) return true
						assignment1 = leftRight[1]
					}
					else if(parent.type === "AssignmentExpression"){
						return true
					}
				}
				return false
			}
			function getOtherAssignedBindings(binding1, arr=[]) {
				if (binding1) {
					var _assignmentRef = binding1._assignmentRef
					var definition = binding1.definition
					for (const ref of binding1.references) {
						if (ref === _assignmentRef || ref === definition || ref._mightBeUndef) continue
						let leftright = isValidAssignment(ref.parent)
						if (leftright && leftright[1] === ref && leftright[0].type === "Identifier") {
							let binding2 = scan.getBinding(leftright[0])
							if (binding2 && binding2 !== binding1 && !arr.includes(binding2) && IsBindingConstant(binding2, 1)) {
								arr.push(binding2)
								getOtherAssignedBindings(binding2, arr)
							}
						}
					}
				}
				return arr
			}
			function getAllSafeThisBindings(functionNode) {
				var result = []
				walk(functionNode.body, n=>{
					if(n.type == "ThisExpression"){
						var leftRight = isValidAssignment(n.parent)
						if (leftRight) {
							let [left, right, isDeclaration] = leftRight
							if (leftRight && right === n && left.type === "Identifier" && isDeclaration) {
								let binding = scan.getBinding(left)
								if (IsBindingConstant(binding, 1)) {
									result.push(binding, ...getOtherAssignedBindings(binding))
								}
							}
						}
						n._isValidThis = cObj
					}
					if (n !== functionNode && (n.type === 'FunctionDeclaration' || n.type === 'FunctionExpression')) {
						return "jump"
					}
				})
				return result
			}
			
			var classIsExpression
			var binding1, binding2
			if (isClass) {
				binding1 = cObj.id && scan.getBinding(cObj.id) 
				if (binding1 && isReassigned(binding1, cObj)) {
					binding1 = null
				}
				if (cObj.type == "ClassExpression") { 
					classIsExpression = true
				}
			}
			else {
				classIsExpression = true
			}
			if (classIsExpression) {
				let parent = cObj.parent
				var leftRight = isValidAssignment(parent)
				if (leftRight && leftRight[1] === cObj && leftRight[0].type === "Identifier") {
					binding2 = scan.getBinding(leftRight[0])
					if (binding2 && !IsBindingConstant(binding2, 1)) {
						binding2 = null
					}
				}
			}
			if (binding1 || binding2) {
				for (const binding of [binding1, binding2, ...getOtherAssignedBindings(binding2)]) {
					if (binding) {
						if (!cObj._name) cObj._name = binding.name 
						for (const ref of binding.references) {
							let isRefOutsideOfTheClass = ref.start < cObj.start || ref.start >= cObj.end
							if (toAllowInliningOutsideOfTheClass || !isRefOutsideOfTheClass) {
								if (isClass) {
									ref._isSafeClassRef = cObj
								}
								else {
									ref._isSafeThis = cObj
								}
							}
						}
					}
				}
			}
			else {
				cObj._name = isClass? "?class" : "?object"
			}
			
			for (const [n, property] of _allProps) {
				let toNotInlineHereComment = hasCommentAnnotationInFront(src, property, comments, CLASS_OBJECT_MARKER__DONT_INLINE_HERE, 10, 1)
				let propNode = property.value
				if (propNode && propNode.type == "FunctionExpression" && propNode.uses_this) {
					for (const binding of getAllSafeThisBindings(propNode)) {
						for (const ref of binding.references) {
							ref._isSafeThis = cObj
						}
					}
				}
				if (toNotInlineHereComment) {
					property._comment_toNotInlineHere = toNotInlineHereComment
				}
				
				let toNotInlineComment = hasCommentAnnotationInFront(src, property, comments, CLASS_OBJECT_MARKER__KEEP_PROPERTY, 10)
				if (toNotInlineComment) {
					_allProps.delete(n)
				}
			}
			
			
		}
		function filterIfAccessedOnUnknownObjectsAndGetRefs() {
			function isAssignedTo(node) {
				return  node.parent.type == "UpdateExpression" 
					|| node.parent.type == "AssignmentExpression" && node.parent.left == node
			}
			function removeCandidateProperty(name, _allProps) {
				_allProps.delete(name)
				if (!_allProps.size) {
					let allEmpty = classObjects.every(({_allProps})=>!_allProps.size)
					if (allEmpty) return true
				}
			}
			const toInlineSafeLiteralsWherePossible = true
			var classObjects_currentIndex = 0 
			var cObj_ofCurrentLocation = null
			var cObjNext = classObjects[0]
			
			walk(ast, node=>{
				var name = null
				var isIdentifier = node.type == "Identifier" || node.type == 'PrivateIdentifier'
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
				var object = node.object
				var isUsage = true
				try {
					if (cObjNext && cObjNext.start <= node.start && cObjNext.end >= node.end) {
						cObj_ofCurrentLocation = cObjNext
						cObjNext = classObjects[++classObjects_currentIndex]
					}
					else if(cObj_ofCurrentLocation && !(cObj_ofCurrentLocation.start <= node.start && cObj_ofCurrentLocation.end >= node.end)){
						cObj_ofCurrentLocation = null
					}
					
					for (let i = classObjects.length-1; i >= 0; --i) {
						let _cObj = classObjects[i];
						let _allProps = _cObj._allProps
						let knownObject = object._isValidThis || object._isSafeThis || object._isSafeClassRef
						if (!knownObject || knownObject === _cObj) {
							let property = _allProps.get(name)
							if (property) {
								let isRefOutsideOfTheClass = node.start < _cObj.start || node.start >= _cObj.end
								let isValidRef = !isRefOutsideOfTheClass || toAllowInliningOutsideOfTheClass && object._isSafeClassRef === _cObj
								if (!isValidRef && toInlineSafeLiteralsWherePossible && property._isPropertyValueAlwaysInlinable) {
									property._mustKeep = 1
									isValidRef = 1
								}
								if ( !isValidRef
								) { 
									if (removeCandidateProperty(name, _allProps)) return "end"
									continue
								}
							}
						}
						
					}
					
					if (!toAllowInliningOutsideOfTheClass && !cObj_ofCurrentLocation) return
					var cObj_ofProperty = cObj_ofCurrentLocation
					var objectIsSafeClassRef = object.type == "Identifier" && object._isSafeClassRef
					if (toAllowInliningOutsideOfTheClass && objectIsSafeClassRef && cObj_ofCurrentLocation !== objectIsSafeClassRef) {
						cObj_ofProperty = objectIsSafeClassRef
					}
					
					if (cObj_ofProperty) {
						var _allProps = cObj_ofProperty._allProps
						var property = _allProps.get(name)
						if (!property) return
						var isRefOutsideOfTheClass = cObj_ofProperty !== cObj_ofCurrentLocation
						var isClass = cObj_ofProperty._isClass
						var objectIsThis = object.type == "ThisExpression" && object._isValidThis === cObj_ofProperty
						var objectIsSafeThisVariable = !objectIsThis && object.type == "Identifier" && object._isSafeThis === cObj_ofProperty
						var objectIsSafeClassRef = object.type == "Identifier" && object._isSafeClassRef === cObj_ofProperty
						var safeThis = objectIsThis || objectIsSafeThisVariable
						var isSafeClassObjectAccess = objectIsThis || objectIsSafeThisVariable || objectIsSafeClassRef
						var usageOnKnownProperty = isSafeClassObjectAccess && property
						var containingProp, containingPropIsStatic
						if(1){
							let propertyParent = isClass? cObj_ofProperty.body : cObj_ofProperty
							let parent = node
							while(parent && parent !== propertyParent) {
								containingProp = parent
								parent = parent.parent
							}
							if (DEBUG && safeThis && (!containingProp || !containingProp._name || containingProp._cObj !== cObj_ofProperty)) 
								throw "!containingProp"
							containingPropIsStatic = isClass? containingProp.static : true
						}
						
						if (!isSafeClassObjectAccess) {
							if (toInlineSafeLiteralsWherePossible && property._isPropertyValueAlwaysInlinable) {
								property._mustKeep = 1
							}
							else if (removeCandidateProperty(name, _allProps)) return "end"
							return 
						}
						
									
									
						var propNode = property?.value
						var propertyIsStatic = isClass? property.static : true
						var thisIsInstance = isClass? !containingPropIsStatic : false
						var isInSameNode = propNode && node.start >= propNode.start && node.end <= propNode.end
						var isNoAccess = !(safeThis && thisIsInstance != propertyIsStatic)
										&& !(propertyIsStatic && objectIsSafeClassRef)
						if (isNoAccess) {
							isUsage = false
							return
						}
						
						if (propNode && isFunctionNode(propNode) && propNode.uses_this) {
							if (isRefOutsideOfTheClass || containingPropIsStatic != propertyIsStatic) {
								var incompatibleThis = true
							}
						}
						
						node._name = name
						node._prop = property
						if (containingProp) {
							containingProp._inRefs ??= new Set
							containingProp._inRefs.add(node)
						}
						
						var isPropertyChanged = isAssignedTo(node) 
						var mustKeepProp = isInSameNode || object._mightBeUndef || isPropertyChanged || incompatibleThis
						if (!mustKeepProp) {
							property._refs ??= new Set
							property._refs.add(node)
							if (isRefOutsideOfTheClass) node._isOutsideOfTheClass = isRefOutsideOfTheClass
						}
						else {
							if (!isPropertyChanged && !incompatibleThis && toInlineSafeLiteralsWherePossible && property._isPropertyValueAlwaysInlinable) {
								property._mustKeep = 1
							}
							else if (removeCandidateProperty(name, _allProps)) return "end"
							return 
						}
					}
				} finally {
					if (isUsage) {
						if (usageOnKnownProperty) {
							usageOnKnownProperty._uses = (usageOnKnownProperty._uses||0)+1
						}
						else {
							for (const {_allProps} of classObjects) {
								const property = _allProps.get(name)
								if(property) property._uses = (property._uses||0)+1
							}
						}
					}
				}
			})
		}
		
		function isPropertyValueAlwaysInlinableLiteral(propNode) {
			return propNode.type == "Literal" && (
					typeof propNode.value == "string"
					|| typeof propNode.value == "number"
				) || propNode.type == "TemplateLiteral" && !propNode.expressions.length
		}
		function findUnusedProps() {
			let filteredNodes = new Set
			while (1) {
				let filtered
				for (let cObj of classObjects) {
					for (const [name, prop] of cObj._allProps) {
						let propValue = prop.value
						let noUses = !prop._uses
						if (noUses && !prop._unused && !filteredNodes.has(prop)) {
							prop._unused = 1
							filtered = 1
							filteredNodes.add(prop)
							if (propValue) {
								for (let cObj2 of classObjects) {
									for (const [name2, prop2] of cObj2._allProps) {
										if (prop2._unused) continue
										if (prop2._refs) {
											for (const refNode of prop2._refs) {
												if (refNode.start >= propValue.start && refNode.start < propValue.end) {
													prop2._refs.delete(refNode)
													prop2._uses = Math.max(0, prop2._uses-1)
												}
											}
										}
										
									}
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
		function getPropsAndFilterUnsuitables(cObj, _allProps) {
			
			function filterByCriteria() {
				_allProps.forEach((property, name)=>{
					var isClass = property._isInClass
					var numRefs = property._refs && property._refs.size||0
					var propNode = property.value
					if (propNode) {
						var isIdentifier = propNode.type == "Identifier"
						var isLiteral = propNode.type == "Literal" || propNode.type == "TemplateLiteral" && !propNode.expressions.length
						var isFunction = propNode.type == "FunctionExpression" 
							&& (property.method || property.kind == "method" || property.kind == "init")
							&& property.value == propNode
						
						var isArrowFunction = propNode.type == "ArrowFunctionExpression" && (property.kind == "init" || isClass && property.value == propNode)
						var isMethod = isFunction || isArrowFunction
						var usesThis = isMethod && propNode.uses_this
					}
					else {
						var isLiteral = true
					}
					if (usesThis && isArrowFunction) isMethod = false
					let refNodeParent = numRefs && [...property._refs][0].parent
					let refCallExpression = refNodeParent && refNodeParent.type === "CallExpression"? refNodeParent : null
					if (isMethod && !refCallExpression) isMethod = false
					
					
					var ok = numRefs == 1 
						|| isLiteral && numRefs > 1 && numRefs <= inlineLiteralValues_maxNumberOfTimes
						|| isIdentifier
						
					if (!ok) {
						_allProps.delete(name)
						return 
					}
					
					var isValidMethod
					var cannotBeInlined
					if (isMethod) {
						let functionNode = propNode
						if(functionNode.uses_arguments) return
						let funcInfo = getFunctionInfo(propNode, refCallExpression, variableNamesChangeable, src)
						if (funcInfo) {
							property._isMethod = true
							propNode._funcInfo = funcInfo
							isValidMethod = true
						}
					}
					else {
						let isConstantIdentifier
						if (isIdentifier) {
							let binding = scan.getBinding(propNode)
							isConstantIdentifier = IsBindingConstant(binding, 0, 1)
							if (toAllowInliningOutsideOfTheClass && numRefs) {
								if (!isConstantIdentifier) cannotBeInlined = true
								else {
									for (const ref of property._refs) {
										if (ref._isOutsideOfTheClass) {
											let objectNode = ref.object
											if ( objectNode._mightBeUndef
												|| !binding._isConstantAtNode(ref)
											) {
												property._refs.delete(ref)
												property._mustKeep = 1
											}
										}
									}
								}
							}
						}
						
						property._isConstantValue = isLiteral || isIdentifier && isConstantIdentifier
							|| (isFunction||isArrowFunction) && (property.type === "PropertyDefinition" || property.type === "Property" && !property.method && property.kind === "init")
					}
					
					if (!isValidMethod && propNode && isFunctionNode(propNode) && 
						(refCallExpression || !(
							isFunction || isArrowFunction && !usesThis
						))
					){
						cannotBeInlined = true
					}
					
					if (cannotBeInlined) {
						_allProps.delete(name)
					}
				})
			}
			function filterNonInlinables() {
				function getReferencedSpecialNonkeywordValues(property, propNode) {
					let refs = new Map
					walk(propNode, node=>{
						if (node.type === "Identifier") {
							let name = node.name
							if (property._outsideRefs.has(name)) {
								return 
							}
							if(name === "Infinity" || name === "undefined" || name === "NaN"){
								let arr = refs.get(name)
								if (!arr) refs.set(name, arr = [])
								arr.push(node)
							}
						}
					})
					for (const [name, nodes] of refs) {
						property._outsideRefs.set(name, [null, nodes])
					}
				}
				function findOutsideRefs() {
					for (const [name, property] of _allProps) {
						var propNode = property.value
						if (!propNode) continue
						property._outsideRefs = new Map
						var aScope = objScope
						do {
							for (const [,b] of aScope.bindings) {
								var refs = getRefsInScope(b.references, propNode)
								if (refs) {
									property._outsideRefs.set(b.name, [b, refs])
								}
							}
							if (aScope.undeclaredBindings) {
								for (const [,b] of aScope.undeclaredBindings) {
									var refs = getRefsInScope(b.references, propNode)
									if (refs) {
										property._outsideRefs.set(b.name, [b, refs])
									}
								}
							}
						} while (aScope = aScope.parent);
						
						getReferencedSpecialNonkeywordValues(property, propNode)
					}
				}
				function isInlinedToWithOutsideRefs_orUnfinished(property) {
					let isVar = !property._isMethod
					let propNode = property.value
					if (!propNode || property._isConstantValue) return 
					
					for (var cObj of classObjects) {
						var _allProps_ = cObj._allProps
						if (!toAllowInliningOutsideOfTheClass && _allProps_ !== _allProps) continue
						for (const [name, otherProperty] of _allProps_) {
							if(otherProperty == property) continue
							if(!otherProperty._outsideRefs) continue
							if(isVar && !otherProperty._outsideRefs.size) continue
							if (otherProperty._refs) {
								for (const refNode of otherProperty._refs) {
									if (refNode.start >= propNode.start && refNode.start < propNode.end) {
										let propNode2 = otherProperty.value
										if (property._refs && propNode2) {
											for (const refNode2 of property._refs) {
												if (refNode2.start >= propNode2.start && refNode2.start < propNode2.end) {
													_allProps.delete(property._name)
													_allProps_.delete(otherProperty._name)
													return
												}
											}
										}
										return true
									}
								}
							}
						}
					}
				}
				function findCoveringBindings() {
					for (const [name, property] of _allProps) {
						var outsideBindings = property._outsideRefs
						if (property._refs && outsideBindings) {
							for (const refNode of property._refs) {
								var refScope = scan.nearestScope(refNode, true)
								var commonScope = objScope
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
					
				}
				function checkMethodArgumentNameCollisions() {
					var has
					for (const [name, property] of _allProps) {
						let propNode = property.value
						if(!propNode) continue
						if(!property._isMethod) continue
						var methodScope = scan.scope(propNode)
						for (const refNode of property._refs) {
							let refCallExpressionNode = [...property._refs][0].parent
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
									property._hasArgNameCols = true
								}
							}
						}
					}
					
				}
				checkMethodArgumentNameCollisions()
				
				findOutsideRefs()
				_allProps.forEach((prop, name)=>{
					if (prop._outsideRefs && prop._outsideRefs.size && !prop._isMethod && !prop._isConstantValue && prop._outsideRefs.some(([n,[b, rs]]) => {
						return b && (!b.definition || !(b.definition.parent.type === 'VariableDeclarator' && b.definition.parent.parent.kind == "const"))
					})) {
						_allProps.delete(name) 
					}
				})
				
				if (toAllowInliningOutsideOfTheClass) {
					_allProps.forEach((prop, name)=>{
						if (prop._refs && prop._outsideRefs && prop._outsideRefs.size && prop._outsideRefs.some(([n,[b, refs]]) => {
							return !(!b || [...prop._refs].every(node => isBindingInScope(b, node)))
						})) {
							_allProps.delete(name) 
						}
					})
				}
				
				
				findCoveringBindings()
				if(!variableNamesChangeable){
					_allProps.forEach((prop, name)=>{
						if (prop._refs.some(r=>(r._covOutRefs && r._covOutRefs.length))) {
							_allProps.delete(name)
						}
					})
					_allProps.forEach((prop, name)=>{
						if (prop._hasArgNameCols) {
							_allProps.delete(name)
						}
					})
				}
				else{
					_allProps.forEach((prop, name)=>{
						if(prop._refs) for (const refNode of prop._refs) {
							/** @type {[number]} */
							var coveringBindings = refNode._covOutRefs
							if(!(coveringBindings && coveringBindings.length)) continue
							var isAnyRefInWith = coveringBindings.some(b=>b.hasRefsInWith)
							if (!isAnyRefInWith) {
								coveringBindings.forEach((b) => {
									let name = gimmeSomethingUnique()
									b.references.forEach(r=>r._rn = name)
								})
							}
							else {
								_allProps.delete(name)
							}
						}
						
					})
					_allProps.forEach((prop, name)=>{
						if (prop._hasArgNameCols) {
							var propNode = prop.value
							var methodScope = scan.scope(propNode)
							var isAnyRefInWith = methodScope.bindings.some(b=>b.hasRefsInWith)
							if (!isAnyRefInWith) {
								methodScope.bindings.forEach(b=>{
									let name = gimmeSomethingUnique()
									b.references.forEach(r=>r._rn = name)
								})
							}
							else {
								_allProps.delete(name)
							}
						}
					})
				}
				
				_allProps.forEach((property, name)=>{
					if (isInlinedToWithOutsideRefs_orUnfinished(property)) {
						++_num_Pending
						_allProps.delete(name)
						cObj._setComment_pending = 1
					}
				})
			}
			
			
			var objScope = getDirectParentScope(cObj)
			filterByCriteria()
			filterNonInlinables()	
			
		}
		
		
		function getTransformedSrc(){
			var result = astTransformMS({src, ast, prevSourceMap:inputMap, parentChain:1, leave(ctx){
				var {update, node, source} = ctx
				if(node._rn){
					if (node.parent.type === "Property" && node.parent.value === node && node.parent.key.start === node.start) {
						let propertySrc = source(node.parent.key)
						if (propertySrc !== node._rn) {
							update(`${propertySrc}:${node._rn}`, node)
						}
					}
					else{
						update(node._rn, node)
					}
					
				}
			}})
			var ctx = result.ctx
			
			function sortKey(...changeables) {
				var refDepth = 0
				var nDepth = changeables.reduce((p, c) => Math.max(getNodeDepth(c), p) , 0)
				var pos = changeables.reduce((p, c) => Math.min(c.start, p) , Infinity)
				return refDepth*281474976710656 + (281470681743360-nDepth*4294967296) + pos
			}
			
			var all_edits = []
			for (const prop of allProps) {
				if (prop._refs) for (const refNode of prop._refs) {
					if (prop._isMethod) {
						all_edits.push([prop._name, "inl_F", sortKey(refNode, prop), refNode, prop])
						
					} else {
						all_edits.push([prop._name, "inl_V", sortKey(refNode), refNode, prop])
						
					}
				}
			}
			var sortF = (a,b)=>a[2] - b[2]
			all_edits.sort(sortF)
			
			var removedProps = new Set
			for (let i = 0; i < all_edits.length; i++) {
				const edit = all_edits[i];
				let [name, editType,,refNode, prop] = edit
				let propNode = prop.value
				let _new = []
				let isInlined
				
				
				if (editType == "inl_F") {
					let refCallExpressionNode = refNode.parent
					editInlinedFunctionBody(propNode, propNode._funcInfo, refCallExpressionNode, ctx)
					let info = inlineFunctionBody(propNode, propNode._funcInfo, refCallExpressionNode, ctx)
					if(propNode._funcInfo.toPrependForExpression){
						_new.push(["prependFBE "+name, "prependFBE", sortKey(propNode._funcInfo.toPrependForExpression.targetStatement), [propNode._funcInfo.toPrependForExpression.targetStatement, refCallExpressionNode], prop])
					}
					else if(info.toPrependForAssignment){
						if(!all_edits.find(t => t[3] == info.toPrependForAssignment.varDeclarationNode)){
							_new.push(["prependFBA "+name, "prependFBA", sortKey(info.toPrependForAssignment.varDeclarationNode), info.toPrependForAssignment, prop, ])
						}
					}
					isInlined = true
				}
				else if (editType == "inl_V"){
					if (!propNode) { 
						ctx.update("void(0)", refNode)
					}
					else if (prop._isPropertyValueAlwaysInlinable) {
						let isVariable = propNode.type == "Identifier"
						let isLiteral = !isVariable
						let valueStr = isVariable? propNode._rn || propNode.name 
									 : isLiteral? ctx.source(propNode) : ""
						
						if (isLiteral && typeof propNode.value == "number" && refNode.parent.type == "MemberExpression" && refNode.parent.object == refNode) {
							valueStr = `(${valueStr})`
						}
						ctx.update(valueStr, refNode)
					}
					else {
						let toNotWrapInRoundParantheses = ToNotWrapExpressionInRoundParantheses(propNode, refNode)
						if(!toNotWrapInRoundParantheses){
							ctx.prepend("(", propNode)
							ctx.append(")", propNode)
						}
						
						if (refNode.parent.type == "ExpressionStatement" && ctx.edit.slice(propNode.start, propNode.start+1) == "(" && !isPreceededBy(refNode.parent, n=>n.type == "EmptyStatement")
						) {
							ctx.prepend(";", propNode)
						}
						
						ctx.remove2(refNode.start, refNode.end)
						ctx.move2(propNode.start, propNode.end, refNode.start)
					}
					
					isInlined = true
				}
				else if (editType == "prependFBA") {
					let { varDeclarationNode, varDeclaratorNode, returnVarName} = refNode
					let declaratorIndex = varDeclarationNode.declarations.indexOf(varDeclaratorNode)
					let inlinedFunc = varDeclaratorNode._inlinedFunc 
					let refCallExpressionNode = propNode._funcInfo.refCallExpressionNode
					let inlineTarget = varDeclarationNode.start 
					let isFirstDeclarator = declaratorIndex === 0
					let isLet = varDeclarationNode.kind === "let"
					if (!isFirstDeclarator) {
						let prevDeclarator = varDeclarationNode.declarations[declaratorIndex-1]
						inlineTarget = prevDeclarator.end
						ctx.remove2(inlineTarget, varDeclaratorNode.start)
						if (!isLet) {
							ctx.append(";", prevDeclarator)
						}
					}
					let prepend0 = (!isFirstDeclarator && isLet? "," : "let ")+returnVarName+";"
					if (inlinedFunc._prependNodes) {
						for (const node of inlinedFunc._prependNodes) {
							if (prepend0) {
								ctx.prepend(prepend0, node)
								prepend0 = null
							}
							ctx.move2(node.start, node.end, inlineTarget)
						}
					}
					else{
						ctx.prepend(prepend0, inlinedFunc)
					}
					ctx.move2(inlinedFunc.start, inlinedFunc.end, inlineTarget)
					ctx.remove2(refCallExpressionNode.start, refCallExpressionNode.end)
					ctx.prepend(returnVarName, refCallExpressionNode)
					if (!isFirstDeclarator) {
						ctx.prepend(varDeclarationNode.kind+" ", varDeclaratorNode) 
					}
					
					if (DEBUG) {
						ctx.edit.prependLeft(inlineTarget, "/* "+prop._name+" INLINED SATRT: *\/")
						ctx.edit.appendRight(inlineTarget, "/* "+prop._name+" INLINED END *\/")
					}
					isInlined = true
				} 
				else if (editType == "prependFBE") { 
					let [statement, refCallExpressionNode] = refNode
					let returnVarName = propNode._funcInfo.toPrependForExpression.returnVarName
					let inlinedFunc = statement._inlinedFunc
					let inlineTarget = statement.start
					let prepend0 = "let "+returnVarName+";"
					if (inlinedFunc._prependNodes) {
						for (const node of inlinedFunc._prependNodes) {
							if (prepend0) {
								ctx.prepend(prepend0, node)
								prepend0 = null
							}
							ctx.move2(node.start, node.end, inlineTarget)
						}
					}
					else{
						ctx.prepend(prepend0, inlinedFunc)
					}
					ctx.move2(inlinedFunc.start, inlinedFunc.end, inlineTarget)
					ctx.remove2(refCallExpressionNode.start, refCallExpressionNode.end)
					ctx.prepend(returnVarName, refCallExpressionNode)
					
					if (DEBUG) {
						ctx.edit.prependLeft(inlineTarget, " /* "+prop._name+" INLINED SATRT: *\/ ")
						ctx.edit.appendRight(inlineTarget, " /* "+prop._name+" INLINED END *\/ ")
					}
					isInlined = true
				} 
				
				if (isInlined && !prop._mustKeep) {
					removedProps.add(prop)
				}
				
				all_edits.splice(i, 1)
				--i
				if(_new.length) {
					all_edits.push(..._new)
					all_edits.sort(sortF)
				}
			}
			
			var toRemoveProps = new Set( Array.from(removedProps).concat(unusedProps) )
			if (toRemoveProps.size) {
				for (const prop of toRemoveProps) {
					if (prop._isInClass) {
						ctx.remove2(prop.start, prop.end)
					}
					else {
						let i = prop._i, isFirst = i == 0
						let classNode = prop._cObj
						if (isFirst) {
							let end = prop.end
							if (i < classNode.properties.length-1) {
								let ic = findNextIndexInJs(",", src, comments, prop.end, classNode.properties[i+1].start)
								if (ic >= 0) {
									end = ic + 1
								}
							}
							ctx.remove2(prop.start, end)
						}
						else {
							let start = prop.start
							let pAbove = classNode.properties[i-1]
							let ic = findNextIndexInJs(",", src, comments, pAbove.end, prop.start)
							if (ic >= 0) {
								start = ic
							}
							ctx.remove2(start, prop.end)
						}
					}
				}
			}
			
			for (const p of toRemoveProps) {
				if (p._comment_toNotInlineHere) {
					ctx.remove(p._comment_toNotInlineHere)
				}
			}
			for (const cObj of classObjects) {
				if (cObj._setComment_pending) {
					ctx.prepend(`/* ${CLASS_OBJECT_MARKER_PENDING} */`, cObj)
				}
				if (cObj._comment_pending) {
					ctx.remove(cObj._comment_pending)
				}
			}
			
			var resultCode = result.toString()
			if (withSourceMap) {
				inputMap = result.map
				options.map = inputMap
			}
			return resultCode
		}
		
		var _offset = 0
		var allProps = new Set
		var _allProps
		var unusedProps = []
		var classObjects = []
		while(1){
			var cObj = null
			findClassObject()
			if (!cObj) break
			_allProps = new Map 
			cObj._allProps = _allProps
			var isClass = cObj._isClass
			findAllObjectProperties(cObj)
			findSafeClassBindings(cObj)
			_allProps.forEach((p, n) => (p.kind == "constructor" || p.kind == "get" || p.kind == "set") && _allProps.delete(n))
			if(!_allProps.size) continue 
			classObjects.push(cObj)
			_offset += 3
		}
		
		if (classObjects.length) {
			filterIfAccessedOnUnknownObjectsAndGetRefs()
			findUnusedProps()
			
			for (var cObj of classObjects) {
				var _allProps = cObj._allProps
				unusedProps.push(..._allProps.values().filter((p)=>p._unused).toArray())
				_allProps.forEach((p, n) => p._unused && _allProps.delete(n))
				_allProps.forEach((p, n) =>{
					if (p._comment_toNotInlineHere && p._inRefs) {
						for (const ref of p._inRefs) {
							ref._prop._refs?.delete(ref)
						}
					}
				})
			}
		}
		
		
		for (var cObj of classObjects) {
			var _allProps = cObj._allProps
			try {
				getPropsAndFilterUnsuitables(cObj, _allProps)
				
				if (_allProps.size) {
					for (const [k, v] of _allProps) allProps.add(v)
				}
			} catch (error) {
				if (DEBUG) {
					throw error
				}
				return
			}
		}
		
		if(allProps.size || unusedProps.length){
			if (infoObject) {
				infoObject.inlinedProps ??= new Set
				allProps.forEach((p)=>infoObject.inlinedProps.add(p._cObj._name+"."+p._name))
				infoObject.removedUnusedProps ??= new Set
				unusedProps.forEach((p)=>infoObject.removedUnusedProps.add(p._cObj._name+"."+p._name))
			}
			
			try {
				var transformed = getTransformedSrc()
			} catch (error) {
				if (DEBUG) {
					throw error
				}
				return
			}
		}
		
		
		
		return transformed
	}
	
	var _changes = 0
	var firstIteration = true
	while (1) {
		var _num_Pending = 0 
		try {
			var src2 = _inline()
		} catch (err) {
			if (DEBUG) {
				throw err
			}
			else return
		}
		if(src2){
			src = src2
			++_changes
		}
		
		if (!_num_Pending) {
			break
		}
		firstIteration = false
	}
	if (infoObject) {
		infoObject.numInlinedProps = infoObject.inlinedProps?.size || 0
		infoObject.inlinedProps = [...infoObject.inlinedProps||""] 
		infoObject.inlinedProps.sort()
		infoObject.removedUnusedProps = [...infoObject.removedUnusedProps||""]
		infoObject.removedUnusedProps.sort()
	}
	return _changes && src || null
}





/** 
 * @typedef {Object} Options
 * @property {any} [all=false] - shrink everything except: numbers, classObjects, functions
 * @property {any} [literals=true] - shrink string literals
 * @property {any} [properties=true] - shrink all property names
 * @property {any} [variables=true] - shrink all variables names
 * @property {any} [undeclared=true] - shrink all undeclared globals
 * @property {any} [values=true] - shrink null, undefined, Infinity
 * @property {any} [this=true] - shrink all "this."
 * @property {any} [numbers=false] - shrink numbers
 * @property {number} [numbers_minLength=3] - numbers shorter than this won't be shrunk
 * @property {number} [numbers_minOccurrences=5] - numbers won't be replaced with variables if they occur less often than this
 * @property {number} [numbers_maxNumberOfVariables=20] - make no more than this number of variables (for the most frequently occuring numbers)
 * @property {any} [classObjects=false] - to inline class-object properties and to remove unused properties (see below)
 * @property {any} [classObjects_classesNeedCommentMarker=false] - 
 * @property {any} [classObjects_allowInliningOutsideOfTheClass=true] - whether to allow properties to be inlined outside of the class/object
 * @property {number} [classObjects_inlineConstantsMaxNumberOfTimes=3] - properties holding strings/numbers won't be inlined if they're used more often than this
 * @property {any} [functions=false] - turns non arrow functions into arrow functions wherever possible
 * @property {any} [allow0Gain=false] - whether to replace strings even if the character difference is 0
 * @property {"`"|'"'|"'"} [quote="`"] - the quote character to use (default: `)
 * @property {string[]} [globalsToNotShrink=[]] - undeclared globals to exclude
 * @property {number} [minPropertyNameLength=3] - property names shorter than this length won't be shrunk
 * @property {SourceMapOptions?} [sourceMap] - source map options if a source map is to be generated
 * @property {any} [debug=false] - prints some debug information if truthy
 * @property {any} [debugInfo] - will hold an info object about the result if debug is truthy
 * @property {any} [rootIsStrictMode=false] - whether the script is in strict mode from the start
*/
/** 
 * @typedef {Object} SourceMapOptions
 * @property {any} [generateSourceMapObject=false] - whether to generate a source map object; it is written to the property: "options.sourceMap.map"
 * @property {any} [generateSourceMapInline=false] - whether to generate and add an inline source map comment
 * @property {SourceMap?} [map] - a prior source map object; this key will hold the new source map object if generateSourceMapObject is truthy
 * @property {string?} [fileName] - filename of the output script file; this is only used to set the "file" property of the source map object
 * @property {string?} [sourceMapUrl] - url of the source map file; if specified then a '//# sourceMappingURL=' comment is added at the end
*/
/** 
 * @param {string} src - source code 
 * @param {Options} options 
 * @returns {string|false} - returns false if nothing was changed
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
	const _TO_REPLACE_NUMBERS = options && "numbers" in options? options.numbers : false
	const _TO_REPLACE_NUMBERS_MINLENGTH = options && "numbers_minLength" in options? Math.max(2, Number(options.numbers_minLength)||3) : 3
	const _TO_REPLACE_NUMBERS_MINOCCURRENCES = options && "numbers_minOccurrences" in options? Math.max(2, Number(options.numbers_minOccurrences)||5) : 5
	const _TO_REPLACE_NUMBERS_MAXNUMBERS = options && "numbers_maxNumberOfVariables" in options? Math.max(1, Number(options.numbers_maxNumberOfVariables)||20) : 20
	const _TO_FORCE_ARROW_FUNCTIONS = options && "functions" in options? options.functions : false
	const _TO_INLINE_CLASS_OBJECT_PROPERTIES_AND_REMOVE_UNUSED = _TO_SHRINK_ALL || (options && "classObjects" in options? options.classObjects : TO_INLINE_CLASS_OBJECT_PROPERTIES_AND_REMOVE_UNUSED)
	const IS_STRICT_MODE = "rootIsStrictMode" in options? options.rootIsStrictMode : false
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
	var numInlinedFunctions = 0
	var numInlinedVariables = 0
	// ...
	
	// class object ----------------------------------------------------------------------------------------------------------------------------------------------------------
	var numInlinedClassPrperties = options && "inlinedClassPropsPre" in options && Number.isInteger(options.inlinedClassPropsPre)? options.inlinedClassPropsPre : 0
	var allInlinedClassPrperties = options && "inlinedClassPropsAllPre" in options && options.inlinedClassPropsAllPre instanceof Array? options.inlinedClassPropsAllPre : []
	var removedUnusedClassProperties = []
	if (_TO_INLINE_CLASS_OBJECT_PROPERTIES_AND_REMOVE_UNUSED) {
		let _classObjects_classesNeedCommentMarker = false
		let _classObjects_allowInliningOutsideOfTheClass = true
		let _classObjects_inlineConstantsMaxNumberOfTimes = 3
		if (options) {
			if ("classObjects_classesNeedCommentMarker" in options)  _classObjects_allowInliningOutsideOfTheClass = options.classObjects_classesNeedCommentMarker
			if ("classObjects_allowInliningOutsideOfTheClass" in options)  _classObjects_allowInliningOutsideOfTheClass = options.classObjects_allowInliningOutsideOfTheClass
			if ("classObjects_inlineConstantsMaxNumberOfTimes" in options)  _classObjects_inlineConstantsMaxNumberOfTimes = options.classObjects_inlineConstantsMaxNumberOfTimes
		}
		
		let info = {}
		let options_ = {
			variableNamesChangeable: _TO_SHRINK_ALL_VARIABLES,
			rootIsStrictMode: IS_STRICT_MODE,
			infoObject: info,
			withSourceMap: _TO_GENERATE_SOURCEMAP,
			classesNeedCommentMarker: _classObjects_classesNeedCommentMarker,
			allowInliningOutsideOfTheClass: _classObjects_allowInliningOutsideOfTheClass,
			inlineConstantsMaxNumberOfTimes: _classObjects_inlineConstantsMaxNumberOfTimes,
			map: inputMap,
		}
		let src2 = inlineClassObjectProperties(src, options_)
		if (src2) {
			src = src2
			numInlinedClassPrperties += info.numInlinedProps
			if(info.inlinedProps instanceof Array) allInlinedClassPrperties = allInlinedClassPrperties.concat(info.inlinedProps)
			numInlinedItems += numInlinedClassPrperties
			removedUnusedClassProperties = info.removedUnusedProps
			if (_TO_GENERATE_SOURCEMAP) inputMap = options_.map
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
	/** @type {acorn.Comment[]} */
	var comments = []
	var ast = acorn.parse(src, {
		ecmaVersion: "latest",
		onComment: comments,
		// sourceType: "module",
	})
	scan.crawl(ast, {isStrictMode:IS_STRICT_MODE}) 
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
	
	
	var [stringLiterals, numberLiterals] = findAllLiterals(
		ast, comments, _TO_SHRINK_ALL_PROPERTY_NAMES, _MIN_PROPERTY_NAME_LENGTH, excludeNodes, src,
		_TO_REPLACE_NUMBERS && _TO_REPLACE_NUMBERS_MINLENGTH
	)
	/** @type {[stringName:string, [nodes: Node[]], createdVariableName?:string, reservedNames?:Set<string>, maxNewIdentifierLength:number, gain:number][]} */
	var all_string_literals = [...stringLiterals]
		.filter(([str, tuple]) => {
			var nodes = tuple[0]
			var minNumOccurrences = str.length == 1? 4 : str.length == 2? 3 : 2
			return nodes.length >= minNumOccurrences
		})
	
	
	// get maximum length of new identifier for each string with positive net character gain  -----------------------------------------------------------------------------
	all_string_literals.forEach(t => t[4] = getMaxIdentifierLengthForPropsLiterals(t[0], _TO_REPLACE_ON_0_GAIN, t[1][1], t[1][2], t[1][3], t[1][4], t[1][5]))
	// filter out those with no positive gain
	all_string_literals = all_string_literals.filter(t => t[4] > 0)
	
	
	
	/** @typedef {[editType:string, node:Node, string:string, index:number, arg:any]} NodeEdit */
	/** @type {NodeEdit[]} */
	var furtherEdits = []
	
	// get available identifiers for each literal -----------------------------------------------------------------------------
	var /** @type {[itemType:"s", numOccurrences:number, object:typeof all_string_literals[0]][]} */ items_literals=[], 
		/** @type {[itemType:"b", numOccurrences:number, Node[], maxIdentifierLength:number, name:string][]} */ items_builtins=[], 
		/** @type {[itemType:"u", numOccurrences:number, Binding, maxIdentifierLength:number][]} */ items_undeclared=[],
		/** @type {[itemType:"n", numOccurrences:number, object:typeof numberLiterals[0]][]} */ items_numbers=[]
	if(_TO_SHRINK_ALL_STRING_LITERALS) items_literals = all_string_literals.map(t => ["s", t[1][0].length, t])
	if(_TO_SHRINK_ALL_UNDECLARED_GLOBALS){
		var undeclaredNotShrunk = {becauseGain:[], becauseUnsafe:[], becauseUserBlacklisted:[], }
		// for undeclared globals
		let all_undeclared_bindings = [...rootScope.undeclaredBindings].map(x=>x[1])
		let items_undeclared_ = all_undeclared_bindings
			// at least 2 occurrences and at least 3 characters long
			.filter(b => b.references.size > 1 && b.name.length >= 3 || void(undeclaredNotShrunk.becauseGain.push(b.name)))
			.filter(b => !isBindingExistenceChecked(b) || void(undeclaredNotShrunk.becauseGain.push(b.name)))
			.filter(b => !b.hasRefsInWith || void(undeclaredNotShrunk.becauseUnsafe.push(b.name)))
		
		if (_NOSHRINK_GLOBALS.length) {
			let blacklisted = new Set(_NOSHRINK_GLOBALS)
			items_undeclared_ = items_undeclared_.filter(b => !blacklisted.has(b.name))
			undeclaredNotShrunk.becauseUserBlacklisted.push(..._NOSHRINK_GLOBALS)
		}
		if (excludeNodes) {
			// ignore excluded areas
			// - Currently, it is not checked whether the global is changed in these excluded functions. 
			// - If these excluded functions use the same global in the same script then the globals may get out of sync with the short variables
			//   But the only reason for excluded areas is so that the functions can be used for script injections or for worker code which are safe cases.
			//   The user can still add those globals to "options.globalsToNotShrink" to avoid sync problems in rare cases.
			items_undeclared_ = items_undeclared_.filter(b => !removeRefsInExcludedAreas_areAllRefsExcluded(b, excludeNodes) || void(undeclaredNotShrunk.becauseGain.push(b.name)))
		}
			
		loop_items_undeclared: for (let i = items_undeclared_.length-1; i >= 0; --i) {
			let b = items_undeclared_[i];
			let updateCost = 0
			let estimatedGain = (b.name.length - 2) * b.references.size
			let furtherEdits = []
			let canBeConstant = true
			for (const ref of b.references) {
				let node = isAssignmentTarget(ref)
				if (node) {
					canBeConstant = false
					if (node.type === 'AssignmentExpression') {
						if (node.left.type === 'ArrayPattern' || node.left.type === 'ObjectPattern') {
							let parent = node.parent
							if ( parent.type === 'ExpressionStatement' 
								|| parent.type === 'SequenceExpression' && (
									parent.parent.type === 'ExpressionStatement'
									|| parent.expressions.lastIndexOf(node) < parent.expressions.length-1
							)) {
								let appendStr = ","+b.name+"=%ID"
								let appendIndex = node.end
								furtherEdits.push(["append", parent, appendStr, appendIndex])
								updateCost += b.name.length+2+2 // assume ID length of 2
								continue
							}
							
						}
						else if (node.left.type === 'Identifier') {
							furtherEdits.push(["prepend", node, b.name+"="])
							updateCost += b.name.length+1
							continue
						}
						items_undeclared_.splice(i,1)
						continue loop_items_undeclared
					}
					else if (node.type === 'UpdateExpression') {
						let parent = node.parent
						if ( parent.type === 'ExpressionStatement'
							|| parent.type === 'SequenceExpression' && (
								parent.parent.type === 'ExpressionStatement'
								|| parent.expressions.lastIndexOf(node) < parent.expressions.length-1
						)) {
							if (node.prefix) {
								furtherEdits.push(["prepend", node, b.name+"="])
								updateCost += b.name.length+1
							}
							else {
								furtherEdits.push(["prepend", node, b.name+node.operator+","])
								updateCost += b.name.length+node.operator.length+1
							}
						}
						else{
							if (node.prefix) {
								furtherEdits.push(["prepend", node, "("+b.name+"="])
								furtherEdits.push(["append", node, ")"])
								updateCost += b.name.length+3
							}
							else {
								furtherEdits.push(["prepend", node, "("+b.name+node.operator+","])
								furtherEdits.push(["append", node, ")"])
								updateCost += b.name.length+node.operator.length+3
							}
						}
						
					}
				}
			}
			b.canBeConstant = canBeConstant
			if (furtherEdits.length) {
				if (estimatedGain - updateCost < 0) { 
					items_undeclared_.splice(i,1)
					undeclaredNotShrunk.becauseGain.push(items_undeclared_[i].name)
				}
				else{
					b.furtherEdits = furtherEdits
					b.updateCost = updateCost
				}
			}
			
		}
		
		items_undeclared = items_undeclared_.map(binding => {
				var maxIdentifierLength = maxIdentifierLengthFor(binding.references.size, binding.name.length, _TO_REPLACE_ON_0_GAIN, binding.updateCost||0)
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
	if (_TO_REPLACE_NUMBERS) {
		numberLiterals = numberLiterals.filter((tuple) => {
			const minGain = 10
			var decl_cost = tuple[1].length + 2 + 2
			var gain = tuple[6] - 2 * tuple[0].length
			return gain - decl_cost >= minGain && tuple[0].length >= _TO_REPLACE_NUMBERS_MINOCCURRENCES
		})
		numberLiterals.sort((a,b)=>b[2]-a[2]) 
		if (numberLiterals.length > _TO_REPLACE_NUMBERS_MAXNUMBERS ) {
			numberLiterals.length = _TO_REPLACE_NUMBERS_MAXNUMBERS
		}
		items_numbers = numberLiterals.map((t) => {
				return ["n", t[0].length, t]
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
		
		let all_items = [...items_literals, ...items_undeclared, ...items_builtins, ...items_numbers]
		all_items.sort(([, aLength], [, bLength]) => bLength - aLength)
		
		if (_TO_SHRINK_ALL_VARIABLES) {
			/** @type {[veriableName:string, numOccurrences:number, occurrences:Set<Node>|Binding, maxNameLength:number, name:string, keyOnNode:string][]} */
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
				else if(item[0] == "n"){
					return [null, item[1], item[2][0], item[2][4], ]
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
						builtin_values_to_replace.push([orig[4], conv[0], orig[2]])
					}
				}
				if (orig[0] == "n") {
					orig[2][5] = conv[0]
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
				let isLiterals, isGlobals, isBuiltins, isNumbers
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
				else if (item[0] == "n"){
					isNumbers = 1
					var tupleN = item[2]
					var name = tupleN[3]
					var occurrence_nodes = tupleN[0]
					var maxNewIdentifierLength = tupleN[4]
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
					else if(isNumbers){
						tupleN[5] = aname
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
					if(all_topLevel_variable_names.has(aname)){
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
					else{ 
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
				var update_cost = b.updateCost||0
				var gain = (b.name.length - b.id.length) * b.references.size
				return sum + gain - decl_cost - update_cost
			}
			undeclared_globals_to_replace.forEach((binding, i) => {
				if (!binding.canBeConstant) {
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
				items_undeclared = items_undeclared.filter(item => !undeclared_globals_to_replace_variable.includes(item[2]) || void(undeclaredNotShrunk.becauseGain.push(b.name)))
				undeclared_globals_to_replace_variable.length = 0
				undeclared_globals_to_replace = undeclared_globals_to_replace_constant
				continue
			}
		}
		break
	}
	
	// filter out those without a suitable identifier name
	all_string_literals = all_string_literals.filter(t => t[2] != null)
	numberLiterals = numberLiterals.filter(t => t[5])
	all_string_literals.forEach(t => t[5] = getCharacterGain(t[0].length, t[2].length, t[1][1], t[1][2], t[1][3], t[1][4], t[1][5]))
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
	var numbers_Gain = 0
	if (_TO_REPLACE_NUMBERS) {
		numbers_Gain = numberLiterals.reduce((sum, b) =>{
			var decl_cost = b[5].length + b[1].length + 2
			var gain = b[6] - b[5].length * b[0].length
			return sum + gain - decl_cost
		}, 0)
	}
	var sumGain_const = literalsAndProps_Gain + builtin_values_Gain + undeclared_globals_constant_Gain + numbers_Gain
	sumGain_const -= 6 // "const;"
	var isGainOk_const = _TO_REPLACE_ON_0_GAIN? sumGain_const >= 0 : sumGain_const > 0
	var sumGain = (isGainOk_const? sumGain_const : 0) + (isGainOk_let? sumGain_let : 0) + all_variables_Gain
	if (!_TO_FORCE_ARROW_FUNCTIONS && !numInlinedClassPrperties) {
		if(!isGainOk_const && !isGainOk_let && !all_variables_Gain && !numInlinedItems){
			console.log("gain not big enough", sumGain);
			return false
		}
		var _allReplacements = all_string_literals.length + undeclared_globals_to_replace_variable.length + undeclared_globals_to_replace_constant.length + builtin_values_to_replace.length + numberLiterals.length
		if (!_allReplacements && !_TO_SHRINK_ALL_VARIABLES && !numInlinedItems) {
			console.log("no suitable replacements available");
			return false
		}
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
		.concat(numberLiterals.map(b => 
			b[5] + "=" + b[1]
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
	var stringLiterals_nodesMap = new Map
	if (isGainOk_const) {
		all_string_literals.forEach(t => t[1][0].forEach(n => stringLiterals_nodesMap.set(n, t)))
	}
	if (_TO_SHRINK_ALL_UNDECLARED_GLOBALS) {
		var undeclared_globals_nodesMap = new Map
		if (isGainOk_let || isGainOk_const) {
			undeclared_globals_to_replace.forEach(b => b.references.forEach(n => undeclared_globals_nodesMap.set(n, b)))
		}
	}
	if (_TO_SHRINK_BUILTIN_VALUES) {
		var builtin_values_nodesMap = new Map
		if (isGainOk_const) {
			builtin_values_to_replace.forEach(b => b[2].forEach(n => builtin_values_nodesMap.set(n, b)))
		}
	}
	if (_TO_REPLACE_NUMBERS) {
		numberLiterals.forEach(b => b[0].forEach(n => n._shrunkNumberVar = b[5]))
	}
	
	var debugInfo1 = {
		replacedPropertyNames: new Set,
		replacedLiterals: new Set,
		replacedUndeclared: new Set,
	}
	// replace
	for (const binding of undeclared_globals_to_replace_variable) {
		/** @type {NodeEdit[]} */
		let _furtherEdits = binding.furtherEdits
		if (_furtherEdits) {
			furtherEdits.push(..._furtherEdits)
			for (let edit of _furtherEdits) {
				edit[2] = edit[2].replace("%ID", binding.id)
			}
		}
	}
	
	var result = astTransformMS({src, ast, parentChain:1, prevSourceMap:inputMap, leave({node, update, source, append, prepend, edit}){
			var undeclared_global_binding
			var builtin
			var l_tuple
			if (l_tuple = stringLiterals_nodesMap.get(node)) {
				var id = l_tuple[2]
				var name = l_tuple[0]
				if (_TO_SHRINK_ALL_PROPERTY_NAMES) {
					var needsPropertyKeyBrackets = false
					let isObjectKey = (node.parent.type == "Property" || node.parent.type == "PropertyDefinition" || node.parent.type == "MethodDefinition") && node.parent.key == node
					let isPropertyMemberKey = node.parent.type == "MemberExpression" && node.parent.property == node
					var isPropertyKey = isObjectKey || isPropertyMemberKey

					if (isPropertyKey) {
						var isComputed = node.parent.computed
						if (!isComputed) {
							needsPropertyKeyBrackets = true
						}
						
						let caseDelta = node._caseDelta
						var diff = name - id - caseDelta
						if(diff < 0 || diff == 0 && !_TO_REPLACE_ON_0_GAIN) return
						
						if (needsPropertyKeyBrackets) {
							id = "["+id+"]"
							if (node._needsSemicol) id = ";"+id
							// // Fix: shorthand: {prop}
							if (!_TO_SHRINK_ALL_VARIABLES) {
								if (isObjectKey &&  node.parent.value.type === "Identifier" && node.parent.value.start === node.start) {
									return
								}
							}
						}
						
						
						if (_DEBUG) {
							if (!debugInfo1.replacedPropertyNames.has(name)) {
								debugInfo1.replacedPropertyNames.add(name)
							}
							
						}
					}
				}
				else{
					var diff = name - id + 2
					if(diff < 0 || diff == 0 && !_TO_REPLACE_ON_0_GAIN) return
				}
				
				if (_DEBUG) {
					if (!isPropertyKey) {
						if (!debugInfo1.replacedLiterals.has(name)) {
							debugInfo1.replacedLiterals.add(name)
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
					debugInfo1.replacedUndeclared.add(undeclared_global_binding.name)
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
			else if(_TO_REPLACE_NUMBERS && (node.type == "Literal" && (typeof node.value === "number" || typeof node.value === "bigint"))){
				let replacement = node._shrunkNumberVar || node._shrunkNumber 
				if (replacement) {
					update(replacement, node)
				}
			}
			else if(!declarationsMarker && iife_wrapper_node && node === iife_wrapper_node){
				var blockWithConstDeclarations = "{" + declaration_string + source(node).slice(1)
				update(blockWithConstDeclarations, node)
			}
		}
	})
	
	var numFunctionsConvertedToArrowFunctions = 0
	if (_TO_FORCE_ARROW_FUNCTIONS) {
		numFunctionsConvertedToArrowFunctions = forceArrowFunctions(ast, src, result, comments)
	}
	
	if (furtherEdits.length) {
		for (let [type, targetNode, string, targetIndex] of furtherEdits) {
			if (type === "prepend") {
				targetIndex ??= targetNode.start
				result.prependRight(targetIndex, string)
			}
			else if (type === "append") {
				targetIndex ??= targetNode.end
				result.appendLeft(targetIndex, string)
			}
		}
	}
	
	if (declarationsMarker) {
		let optionalNewline = declarationsMarker[0][declarationsMarker[0].length-1] === "\n"? "\n" : ""
		result.replace(reg_declarationsMarker, declaration_string + optionalNewline)
	}
	else if (!iife_wrapper_node) {
		result.prepend(declaration_string)
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
	var debugInfo2 = {
		shrinkGain_real: realGain,
		shrinkGain_predicted: sumGain,
		discr: realGain-sumGain,
		totalGain,
		literalsAndProps_Gain,
		undeclared_globals_Gain,
		all_variables_Gain,
		estimated_this_Gain,
		numbers_Gain,
		numNumbersReplaced: numberLiterals.length,
		numThisReplaced,
		numFunctionsConvertedToArrowFunctions,
		numInlinedFunctions,
		numInlinedVariables,
		numInlinedClassPrperties,
		allInlinedClassPrperties,
		removedUnusedClassProperties,
		debug_insufficientGainFor,
		...debugInfo1,
		undeclaredNotShrunk,
	}
	if (options) options.debugInfo = debugInfo2
	if(_DEBUG) {
		console.log(debugInfo2);
	}
	return resultCode
}
module.exports = Shrink 
Shrink.inlineClassObjectProperties = inlineClassObjectProperties




