










const DEBUG = 0
const CONST_DECLARATION_QUOTE_CHARACTER = "`"
const TO_SHRINK_ALL_STRING_LITERALS = 1
const TO_SHRINK_ALL_PROPERTY_NAMES = 1
const TO_SHRINK_ALL_UNDECLARED_GLOBALS = 1
const TO_SHRINK_ALL_VARIABLES_WHEN_POSSIBLE = 1
const TO_SHRINK_BUILTIN_VALUES = 1 // replaces: undefined, null, Infinity, 
const MIN_PROPERTY_NAME_LENGTH = 3
const TO_REPLACE_ON_0_GAIN = 0 // if the replacement results in a 0 character gain, still replace




var acorn = require("acorn");
var scan = require('./scope-analyzer')
var transform = require('transform-ast');

const keywords = new Set(
	["abstract", "arguments", "await", "boolean", "break", "byte", "case", "catch", "char", "class", "const", "continue", "debugger", "default", 
	"delete", "do", "double", "else", "enum", "eval", "export", "extends", "false", "final", "finally", "float", "for", "function", "goto", "if", 
	"implements", "import", "in", "instanceof", "int", "interface", "let", "long", "native", "new", "null", "package", "private", "protected", 
	"public", "return", "short", "static", "super", "switch", "synchronized", "this", "throw", "throws", "transient", "true", "try", "typeof", 
	"var", "void", "volatile", "while", "with", "yield", "const", 
	"NaN", "undefined", "Infinity"]
)


base54 = (() => {
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
function getAllScopes_andAddAdditionalInfo(ast_node, toAddBlockInfo, toAddASTNode) {
	var all_scopes = []
	function _getAllScopes(ast_node) {
		if(ast_node instanceof Array){
			for (const node of ast_node) {
				_getAllScopes(node)
			}
		}
		else if(typeof ast_node == "object"){
			var scope = scan.scope(ast_node)
			if(scope){
				if (toAddBlockInfo && scan.isBlockScopeNode(ast_node)) {
					scope.isBlock = true
				}
				if (toAddASTNode) {
					scope.n = ast_node
				}
				all_scopes.push(scope)
			}
			
			for (var p in ast_node) {
				if(p == "parent") continue
				var node = ast_node[p];
				if(node == null) continue
				_getAllScopes(node)
			}
		}
	}
	_getAllScopes(ast_node)
	return all_scopes
}
function getAllTakenNamesFor(ast_nodes) {
	// gets all variable names (as string) declared in each scope (and parent scopes) and merges them
	var scopes = new Set
	for (const node of ast_nodes) {
		var scope = scan.scope(node) || scan.scope(scan.nearestScope(node, true)) || scan.scope(scan.nearestScope(node))
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
function obtainNewVariableIdentifiers(node, otherIdentifiersInThisScope, customGlobalReservedNames /* Set<string> */) {
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
			}
			// ordered from here
			if (scopeNode.start > refNode.end) {
				continue
			}
			else if(refNode.start > scopeNode.end){
				return false
			}
			else if (refNode.start > scopeNode.start) {
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
							if(n.type != "Identifier" && n.type != "Literal" && n.type != "TemplateLiteral") {
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
	function getVars(node, otherIdentifiersInThisScope) {
		if(node instanceof Array){
			for (const n of node) {
				getVars(n)
			}
		}
		else if(typeof node == "object"){
			var scope = scan.scope(node)
			if (scope) {
				assignNewNames(scope, node, otherIdentifiersInThisScope)
			}
			for (var p in node) {
				if(p == "parent") continue
				var n = node[p];
				if(n == null) continue
				getVars(n)
			}
		}
	}
	var n = node
	while (n.parent) n = n.parent
	var undeclaredBindings = scan.scope(n).undeclaredBindings
	
	var gain = 0
	getVars(node, otherIdentifiersInThisScope)
	return gain
}
function findAllStringLiterals(ast_node, toIncludePropertyKeys=true, minPropertyKeyLength=1) {
	// string => [[...nodes], m2, p0, p1, p2] // occurrences
	var names = new Map
	function _findAllStringLiterals(node) {
		if(node instanceof Array){
			for (const n of node) {
				_findAllStringLiterals(n)
			}
		}
		else if(typeof node == "object"){
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
						if(typeof node.value !== "string") return // do not deal with non strings here
						name = node.value
					}
					else if(isTemplateLiteral){
						name = templateLiteralValue
					}
					else if(isIdentifier && !isComputed){ // if computed key then Identifier is a variable
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
			else for (var p in node) {
				if(p == "parent") continue
				var n = node[p];
				if(n == null) continue
				_findAllStringLiterals(n)
			}
		}
	}
	_findAllStringLiterals(ast_node)
	return names
}
function findBuiltinValues(ast_node) {
	var names = new Map
	function _findBuiltinValues(node) {
		
		if(node instanceof Array){
			for (const n of node) {
				_findBuiltinValues(n)
			}
		}
		else if(typeof node == "object"){
			var isLiteral = node.type == "Literal"
			var isIdentifier = node.type == "Identifier"
			if(isLiteral || isIdentifier) {
				if(isLiteral && node.value === null) {
					var name = "null"
				}
				else if(isIdentifier){
					if (node.name === "undefined") {
						var name = "undefined"
					} else if (node.name === "Infinity"){
						var name = "Infinity"
					}
				}
				if (name) {
					var refNodes = names.get(name)
					if(!refNodes){
						refNodes = []
						names.set(name, refNodes)
					}
					refNodes.push(node)
				}
			}
			
			else for (var p in node) {
				if(p == "parent") continue
				var n = node[p];
				if(n == null) continue
				_findBuiltinValues(n)
			}
		}
	}
	_findBuiltinValues(ast_node)
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
		if (newIdentifierLength > 8) { // cap at 8
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
function Shrink(src, options) {
	const _TO_SHRINK_ALL = options && "all" in options? options.all : false
	const _TO_SHRINK_ALL_STRING_LITERALS = _TO_SHRINK_ALL || options && "literals" in options? options.literals : TO_SHRINK_ALL_STRING_LITERALS
	const _TO_SHRINK_ALL_PROPERTY_NAMES = _TO_SHRINK_ALL || options && "properties" in options? options.properties : TO_SHRINK_ALL_PROPERTY_NAMES
	const _TO_SHRINK_ALL_UNDECLARED_GLOBALS = _TO_SHRINK_ALL || options && "undeclared" in options? options.undeclared : TO_SHRINK_ALL_UNDECLARED_GLOBALS
	const _TO_SHRINK_ALL_VARIABLES = _TO_SHRINK_ALL || options && "variables" in options? options.variables : TO_SHRINK_ALL_VARIABLES_WHEN_POSSIBLE
	const _TO_SHRINK_BUILTIN_VALUES = _TO_SHRINK_ALL || options && "values" in options? options.values : TO_SHRINK_BUILTIN_VALUES
	const _MIN_PROPERTY_NAME_LENGTH = options && "minPropertyNameLength" in options? options.minPropertyNameLength : MIN_PROPERTY_NAME_LENGTH
	const _TO_REPLACE_ON_0_GAIN = options && "allow0Gain" in options? options.allow0Gain : TO_REPLACE_ON_0_GAIN
	const _CONST_DECLARATION_QUOTE_CHARACTER = options && "quote" in options && typeof options.quote == "string"? options.quote : CONST_DECLARATION_QUOTE_CHARACTER
	const _DEBUG = options && "debug" in options? options.debug : DEBUG
	



	var ast = acorn.parse(src, {
		ecmaVersion: "latest",
	})
	scan.crawl(ast) 
	
	
	var all_scopes = getAllScopes_andAddAdditionalInfo(ast, true, true, !_TO_SHRINK_ALL_VARIABLES)
	
	var all_undeclared_set =  new Set(
		all_scopes.map(s => [...s.undeclaredBindings].map(x=>x[0])) // undeclared names
		.reduce((a, b) => a.concat(b), [])
	)
	
	
	var stringLiterals = findAllStringLiterals(ast, _TO_SHRINK_ALL_PROPERTY_NAMES, _MIN_PROPERTY_NAME_LENGTH)
	var all_string_literals = [...stringLiterals] // [[stringName, [ast_nodes,...], identifier, S[reserved names], maxNewIdentifierLength, gain], ...]
		.filter(([str, tuple]) => {
			var nodes = tuple[0]
			var minNumOccurrences = str.length == 1? 4 : str.length == 2? 3 : 2
			return nodes.length >= minNumOccurrences
		})
	
	
		
	
	// get maximum length of new identifier for each string with positive character gain 
	all_string_literals.forEach(t => t[4] = getMaxIdentifierLengthForPropsLiterals(t[0], _TO_REPLACE_ON_0_GAIN, t[1][1], t[1][2], t[1][3], t[1][4]))
	// filter out those with no positive gain
	all_string_literals = all_string_literals.filter(t => t[4] > 0)
	
	
	
	// get available identifiers for each literal
	// [type, occurrences, object]
	var items_literals=[], items_undeclared=[], items_builtins=[]
	if(_TO_SHRINK_ALL_STRING_LITERALS) items_literals = all_string_literals.map(t => ["s", t[1][0].length, t])
	if(_TO_SHRINK_ALL_UNDECLARED_GLOBALS){
		let all_undeclared_bindings = all_scopes.map(s => [...s.undeclaredBindings].map(x=>x[1]))
			.reduce((a, b) => a.concat(b), [])
		items_undeclared = all_undeclared_bindings
			// .filter(b => !["Infinity", "undefined"].includes(b.name)) // fix scope analyzer
			.filter(b => b.references.size > 1 && b.name.length >= 3) // at least 2 occurrences and at least 3 characters long
			.map(binding => {
				var maxIdentifierLength = maxIdentifierLengthFor(binding.references.size, binding.name.length, _TO_REPLACE_ON_0_GAIN)
				return ["u", binding.references.size, binding, maxIdentifierLength]
			})
	}
	if (_TO_SHRINK_BUILTIN_VALUES) {
		items_builtins = [...findBuiltinValues(ast)]
			.map(([name, nodes]) => {
				var maxIdentifierLength = maxIdentifierLengthFor(nodes.length, name.length, _TO_REPLACE_ON_0_GAIN)
				return ["b", nodes.length, nodes, maxIdentifierLength, name]
			})
	}
	
	
	var iife_wrapper_node = getIIFEBodyBlockNode(ast) // the "BlockStatement" node if the script is a function, otherwise undefined
	var top_scope = iife_wrapper_node && scan.scope(scan.nearestScope(iife_wrapper_node)) || scan.scope(ast)
	
	while(true){
		var debug_insufficientGainFor = []
		var undeclared_globals_to_replace = []
		var builtin_values_to_replace = []
		
		let all_items = [...items_literals, ...items_undeclared, ...items_builtins]
		all_items.sort(([, aLength], [, bLength]) => bLength - aLength)
	
		if (_TO_SHRINK_ALL_VARIABLES) {
			// convert
			let items = all_items.map(item => {
				if(item[0] == "s"){
					return [null, item[1], item[2][1][0], item[2][4]]
				}
				else if(item[0] == "u"){
					return [null, item[1], item[2].references, item[3]]
				}
				else if(item[0] == "b"){
					return [null, item[1], item[2], item[3]]
				}
			})
			var topLevelScopeNode = iife_wrapper_node && iife_wrapper_node.parent || ast
			var all_variables_Gain = obtainNewVariableIdentifiers(topLevelScopeNode, items)
			// convert back & set the name if it was assignd
			for (var i = 0; i < items.length; i++) {
				var conv = items[i];
				var orig = all_items[i];
				if (orig[0] == "s") {
					orig[2][2] = conv[0]
				}
				else if(orig[0] == "u"){
					if (conv[0]) { // can be null (= no short enough identifiers available)
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
				var takenNames = getAllTakenNamesFor(occurrence_nodes) // all declared variablles in all scopes (incl. parents) the literal appears in
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
					if (all_undeclared_set.has(aname)) { // disallowed
						continue
					}
					if(all_topLevel_variable_names.has(aname)){ // disallowed for everybody
						continue
					}
					if(takenNames.has(aname)){ // disallowed
						availableSkippedIdentifiers.add(aname)
						continue
					}
					if(aname.length <= maxNewIdentifierLength){
						availableSkippedIdentifiers.delete(aname)
						setaname(aname)
						continue literalsLoop
					}
					else{ // generated name is too long for this literal to be worth replacing
						// filter out below
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
		// undeclared globals must be in a separate "let ;" statement because they can be assigned to (are not always constant)
		// if the gain is not enough for the "let" statement then omit the globals and recreate the variables without the globals competing for them
		var undeclared_globals_Gain = 0
		var sumGain_let = 0
		if (_TO_SHRINK_ALL_UNDECLARED_GLOBALS && undeclared_globals_to_replace.length) {
			undeclared_globals_Gain = undeclared_globals_to_replace.reduce((sum, b) =>{
				var decl_cost = b.name.length + b.id.length + 2
				var gain = (b.name.length - b.id.length) * b.references.size
				return sum + gain - decl_cost
			}, 0)
			var sumGain_let = undeclared_globals_Gain
			sumGain_let -= 4 // "let;"
			var isGainOk_let = _TO_REPLACE_ON_0_GAIN? sumGain_let >= 0 : sumGain_let > 0
			if(!isGainOk_let && (_TO_SHRINK_ALL_STRING_LITERALS || _TO_SHRINK_ALL_PROPERTY_NAMES || _TO_SHRINK_BUILTIN_VALUES)){
				items_undeclared = []
				continue
			}
		}
		break
	}
	// filter out those without a suitable identifier name
	all_string_literals = all_string_literals.filter(t => t[2] != null)
	all_string_literals.forEach(t => t[5] = getCharacterGain(t[0].length, t[2].length, t[1][1], t[1][2], t[1][3], t[1][4]))
	if (!_TO_REPLACE_ON_0_GAIN) {
		all_string_literals = all_string_literals.filter(t => t[5] > 0)
	}
	
	// calculate sizes
	var literalsAndPropsGain = 0
	if (_TO_SHRINK_ALL_STRING_LITERALS || _TO_SHRINK_ALL_PROPERTY_NAMES) {
		literalsAndPropsGain = all_string_literals.reduce((sum, t) => t[5] + sum, 0)
	}
	var builtin_values_Gain = 0
	if (_TO_SHRINK_BUILTIN_VALUES && builtin_values_to_replace.length) {
		builtin_values_Gain = builtin_values_to_replace.reduce((sum, b) =>{
			var decl_cost = b[0].length + b[1].length + 2
			var gain = (b[0].length -  b[1].length) * b[2].length
			return sum + gain - decl_cost
		}, 0)
	}
	var sumGain_const = literalsAndPropsGain + builtin_values_Gain + (all_variables_Gain||0)
	sumGain_const -= 6 // "const;"
	var isGainOk_const = _TO_REPLACE_ON_0_GAIN? sumGain_const >= 0 : sumGain_const > 0
	var sumGain = sumGain_const + sumGain_let
	if(!isGainOk_const && !isGainOk_let){
		console.log("gain not big enough", sumGain);
		return false
	}
	var _allReplacements = all_string_literals.length + undeclared_globals_to_replace.length + builtin_values_to_replace.length
	if (!_allReplacements && !_TO_SHRINK_ALL_VARIABLES) {
		console.log("no suitable replacements available");
		return false
	}
	
	// create the declaration statement (eg. `const a="literal1", b=.....;`) 
	var declaration_string = ""
	if (isGainOk_const) {
		declaration_string += "const " + all_string_literals.map(t => 
			t[2] + "=" + _CONST_DECLARATION_QUOTE_CHARACTER + escapeCharacter(t[0], _CONST_DECLARATION_QUOTE_CHARACTER) + _CONST_DECLARATION_QUOTE_CHARACTER
		)
		.concat(builtin_values_to_replace.map(b => 
			b[1] + "=" + b[0]
		))
		.join(",") + ";"
	}
	if (isGainOk_let) {
		declaration_string += "let " + undeclared_globals_to_replace.map(b => 
			b.id + "=" + b.name
		)
		.join(",") + ";"
	}
	
	
	// replace literals
	// map
	var stringLiterals_nodesMap = new Map // node => tuple
	all_string_literals.forEach(t => t[1][0].forEach(n => stringLiterals_nodesMap.set(n, t))) // node => identifier
	if (_TO_SHRINK_ALL_UNDECLARED_GLOBALS) {
		var undeclared_globals_nodesMap = new Map // node => Binding
		undeclared_globals_to_replace.forEach(b => b.references.forEach(n => undeclared_globals_nodesMap.set(n, b)))
		delete undeclared_globals_to_replace
	}
	if (_TO_SHRINK_BUILTIN_VALUES) {
		var builtin_values_nodesMap = new Map
		builtin_values_to_replace.forEach(b => b[2].forEach(n => builtin_values_nodesMap.set(n, b)))
		delete builtin_values_to_replace
	}
	
	var debugInfo = {
		replacedPropertyNames: new Set,
		replacedLiterals: new Set,
		replacedUndeclared: new Set,
	}
	// replace
	var result = transform(src, {ast}, node =>{
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
					
					if(isComputed){ // can only be a literal
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
			
			node.edit.update(id)
		}
		// Fix: "object.[A]" => "object[A]", but not object?.[A]
		else if(node.type == "MemberExpression" && node.computed == false && !node.optional && stringLiterals_nodesMap.has(node.property)){
			// remove "."
			var curSrc = node.source()
			var i = curSrc.lastIndexOf(".")
			if(i > 0){
				var newSrc = curSrc.slice(0, i) + curSrc.slice(i+1)
				node.edit.update(newSrc)
			}
		}
		else if(_TO_SHRINK_ALL_UNDECLARED_GLOBALS && isGainOk_let && (undeclared_global_binding = undeclared_globals_nodesMap.get(node))){
			if (_DEBUG) {
				debugInfo.replacedUndeclared.add(undeclared_global_binding.name)
			}
			node.edit.update(undeclared_global_binding.id)
		}
		else if(_TO_SHRINK_ALL_VARIABLES && (node.type == "Identifier" && node._v)){
			node.edit.update(node._v)
		}
		else if(_TO_SHRINK_BUILTIN_VALUES && (builtin = builtin_values_nodesMap.get(node))){
			node.edit.update(builtin[1])
		}
		else if(iife_wrapper_node && node === iife_wrapper_node){
			var blockWithConstDeclarations = "{" + declaration_string + node.source().slice(1)
			node.edit.update(blockWithConstDeclarations)
		}
	})
	var resultCode = result.toString()
	
	if (!iife_wrapper_node) {
		resultCode = declaration_string + resultCode
	}
	
	if(_DEBUG) {
		let realGain = src.length - resultCode.length
		console.log({
			realGain,
			predictedGain: sumGain,
			discr: realGain-sumGain,
			literalsAndPropsGain,
			undeclared_globals_Gain,
			all_variables_Gain,
			debugInfo,
			debug_insufficientGainFor,
		});
	}
	
	return resultCode
}
module.exports = Shrink


