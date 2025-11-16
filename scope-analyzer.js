// fixed scope-analyzer ========================================================================================================================
var assert = require('assert')

var kScope = Symbol('scope')
var kBinding = Symbol('bind')
var kIsDefinition = Symbol('def')

exports.bindingKey = kBinding
exports.createScope = createScope
exports.visitScope = visitScope
exports.visitBinding = visitBinding
exports.crawl = crawl
exports.analyze = crawl // old name
exports.clear = clear
exports.deleteScope = deleteScope
exports.nearestScope = getNearestScope
exports.getNearestScopeNode = getNearestScopeNode
exports.scope = getScope
exports.getBinding = getBinding
exports.binding = getDeclaredBinding
exports.isDefinition = isNodeDefinition
exports.isBlockScopeNode = isBlockScopeNode
exports.isFunctionNode = isFunctionNode
/** @typedef {import("acorn").Node} Node */
/** @typedef {Binding} Binding */
/** @typedef {Scope} Scope */

/** @returns {Binding} */
function getDeclaredBinding(node) {
	return node[kBinding]
}
function isNodeDefinition(node) {
	return node[kIsDefinition]
}


function Binding (name, definition, isConst, isBlockScoped, isHoisted) {
	/** @type {string} */
	this.name = name
	/** @type {Node} */
	this.definition = definition
	/** @type {Set<Node>} */
	this.references = new Set()
	if(isConst) this.isConst = true
	if(isBlockScoped) this.isBlockScoped = true
	if(isHoisted) this.isHoisted = true
	/** @type {Scope} */
	this.scope = null
  
	if (definition){
		this.add(definition)
		definition[kIsDefinition] = true
	}
  }
  
  Binding.prototype.add = function (node) {
	this.references.add(node)
	node[kBinding] = this
	return this
  }
  
  Binding.prototype.remove = function (node) {
	if (!this.references.has(node)) {
	  throw new Error('Tried removing nonexistent reference')
	}
	this.references.delete(node)
	return this
  }
  
  Binding.prototype.isReferenced = function () {
	var definition = this.definition
	var isReferenced = false
	this.each(function (ref) {
	  if (ref !== definition) isReferenced = true
	})
	return isReferenced
  }
  
  Binding.prototype.getReferences = function () {
	var arr = []
	this.each(function (ref) { arr.push(ref) })
	return arr
  }
  
  Binding.prototype.each = function (cb) {
	this.references.forEach(function (ref) { cb(ref) })
	return this
  }
  
function Scope (/** @type {Scope} */ parent, scopeNode) {
	/** @type {Scope} */
	this.parent = parent
	/** @type {Map<Node, Binding>} */
	this.bindings = new Map()
	/** @type {Map<Node, Binding>} */
	this.undeclaredBindings = new Map()
	if (parent) {
	  if (!parent.children) {
			parent.children = []
		}
		parent.children.push(this)
	}
	/** @type {Node} */
	this.scopeNode = scopeNode
	/** @type {Scope[]?} */
	this.children = null
	// hasFunctionDeclarations
}

Scope.prototype.define = function (binding) {
	var existing = this.bindings.get(binding.name)
	if (existing) {
		binding.getReferences().forEach(function (ref) {
			existing.add(ref)
		})
	} else {
		this.bindings.set(binding.name, binding)
		binding.scope = this
	}
	return this
}

Scope.prototype.has = function (name) {
  return this.bindings.has(name)
}

Scope.prototype.add = function (name, ref) {
  var binding = this.bindings.get(name)
  if (binding) {
    binding.add(ref)
  }
  return binding
}
Scope.prototype.depth = function (functions) {
	var scope = this
	var depth = 1
	while (scope = scope.parent) (!functions || functions && !this.isBlock) && ++depth
	return depth
}
Scope.prototype.functionScope = function () {
	let scope = this
	while (scope?.isBlock) scope = scope.parent
	return scope
}
Scope.prototype.addUndeclared = function (name, ref) {
	var binding = this.undeclaredBindings.get(name)
	if (!binding) {
		var binding = new Binding(name)
		this.undeclaredBindings.set(name, binding)
	}

	binding.add(ref)
	return binding
}

Scope.prototype.getBinding = function (name) {
  return this.bindings.get(name)
}

Scope.prototype.getReferences = function (name) {
  return this.has(name) ? this.bindings.get(name).getReferences() : []
}


Scope.prototype.forEach = function () {
  this.bindings.forEach.apply(this.bindings, arguments)
}

Scope.prototype.forEachAvailable = function (cb) {
  var seen = new Set()
  this.bindings.forEach(function (binding, name) {
    seen.add(name)
    cb(binding, name)
  })
  this.parent && this.parent.forEachAvailable(function (binding, name) {
    if (!seen.has(name)) {
      seen.add(name)
      cb(binding, name)
    }
  })
}



function createScope (node, bindings) {
  assert.ok(typeof node === 'object' && node && typeof node.type === 'string', 'scope-analyzer: createScope: node must be an ast node')
  let scope = node[kScope]
  if (!scope) {
    var parent = getParentScope(node)
	scope = new Scope(parent, node)
	node[kScope] = scope
	scope.n = node
	if(isBlockScopeNode(node)) scope.isBlock = true
  }
  if (bindings) {
    for (var i = 0; i < bindings.length; i++) {
		scope.define(new Binding(bindings[i]))
    }
  }
  return scope
}
	

function visitScope (node) {
  assert.ok(typeof node === 'object' && node && typeof node.type === 'string', 'scope-analyzer: visitScope: node must be an ast node')
  registerScopeBindings(node)
}
function visitBinding (node) {
	assert.ok(typeof node === 'object' && node && typeof node.type === 'string', 'scope-analyzer: visitBinding: node must be an ast node')
	if(isLabel(node)){
		var scopeNode = getNearestScopeNode(node.parent, false)
		var scope = createScope(scopeNode)
		if(!scope.labels) scope.labels = {}
		if(!scope.labels[node.name]) scope.labels[node.name] = []
		scope.labels[node.name].push(node)
	}
	else if (isVariable(node)) {
		registerReference(node)
	}
}

var isInStrict
var currentFunctionContext
var rootNode 
const functionContextStack = []
const withStack = []
const allBindings = []
function crawl (ast, 
	/** @type {{leaveEmptyBlockScopes?:any, rootIsStrictMode?:any}} */
	options
) {
	assert.ok(typeof ast === 'object' && ast && typeof ast.type === 'string', 'scope-analyzer: crawl: ast must be an ast node')
	var toLeaveEmpyBlockScopes = options && "leaveEmptyBlockScopes" in options? options.leaveEmptyBlockScopes : false
	isInStrict = options && "rootIsStrictMode" in options? options.rootIsStrictMode : false
	currentFunctionContext = {uses_this:false, isStrictMode:isInStrict}
	functionContextStack.push(currentFunctionContext)
	rootNode = ast
	rootNode.isStrictMode = isInStrict
	
	try {
		dash(ast, {
			enter(node, parent){
				node.parent = parent
				setContext_enter(node)
				visitScope(node)
			},
			leave(node, parent){
				setContext_leave(node)
				if (!toLeaveEmpyBlockScopes) {
					removeEmptyBlockScope(node)
				}
			}
		})
		withStack.length = 0
		dash(ast, {
			enter(node){
				if(node.type === "WithStatement"){
					withStack.push(node)
				}
				visitBinding(node)
			},
			leave(node){
				if(node.type === "WithStatement"){
					withStack.pop(node)
				}
			}
		})
		for (const binding of allBindings) {
			if (binding.hasRefsInWith !== true) {
				binding.hasRefsInWith = false
			}
		}
	} finally {
		functionContextStack.length = 0
		withStack.length = 0
		allBindings.length = 0
		rootNode = null
		currentFunctionContext = null
	}

	return ast
}
function setContext_enter(node) {
	if (isFunctionNode(node)) {
		let becameStrict = false
		if (!currentFunctionContext.isStrictMode) {
			let body = node.body
			if (body.type === 'BlockStatement' && body.body.length) {
				let first = body.body[0]
				if (first.type === 'ExpressionStatement' && first.expression.type === 'Literal' && first.expression.value === 'use strict') {
					becameStrict = true
				}
			}
		}
		currentFunctionContext = {isStrictMode: currentFunctionContext.isStrictMode || becameStrict}
		functionContextStack.push(currentFunctionContext)
	}
	else if(node.type === "ClassBody"){
		currentFunctionContext = {isStrictMode: true}
		functionContextStack.push(currentFunctionContext)
	}
	else if(node.type === "WithStatement"){
		withStack.push(node)
	}
}
function setContext_leave(node) {
	if (isFunctionNode(node)) {
		if (currentFunctionContext.uses_this) node.uses_this = true
		if (currentFunctionContext.isStrictMode) node.isStrictMode = true
		functionContextStack.pop()
		currentFunctionContext = functionContextStack[functionContextStack.length-1]
		if (node.type === 'ArrowFunctionExpression' && node.uses_this) currentFunctionContext.uses_this = true
	}
	else if(node.type === "ClassBody"){
		functionContextStack.pop()
		currentFunctionContext = functionContextStack[functionContextStack.length-1]
	}
	else if(node.type === "ThisExpression"){
		currentFunctionContext.uses_this = true
	}
	else if(node.type === "WithStatement"){
		withStack.pop(node)
	}
}

function removeEmptyBlockScope(node) {
	var scope = getScope(node)
	if (!scope) {
		return
	}
	if (!isBlockScopeNode(node)) {
		return
	}
	if(!scope.bindings.size && !scope.hasFunctionDeclarations){
		if (scope.children) {
			for (const c of scope.children) {
				c.parent = scope.parent
			}
		}
		delete node[kScope]
	}
}

function clear (ast) {
  assert.ok(typeof ast === 'object' && ast && typeof ast.type === 'string', 'scope-analyzer: clear: ast must be an ast node')
  dash(ast, deleteScope)
}

function deleteScope (node) {
  if (node) {
    delete node[kScope]
  }
}
/** @returns {Scope} */
function getScope (node) {
  if (node && node[kScope]) {
    return node[kScope]
  }
  return null
}

function getBinding (identifier) {
  assert.strictEqual(typeof identifier, 'object', 'scope-analyzer: getBinding: identifier must be a node')
  assert.strictEqual(identifier.type, 'Identifier', 'scope-analyzer: getBinding: identifier must be an Identifier node')

  var scopeNode = getDeclaredScope(identifier)
  if (!scopeNode) return null
  var scope = getScope(scopeNode)
  if (!scope) return null
  return scope.getBinding(identifier.name) || scope.undeclaredBindings.get(identifier.name)
}

function registerScopeBindings (node) {
  if (node.type === 'Program') {
    createScope(node)
  }
  else if (node.type === 'VariableDeclaration') {
	let isVar = node.kind === 'var'
    var scopeNode = getNearestScopeNode(node, !isVar)
    var scope = createScope(scopeNode)
    node.declarations.forEach(function (decl) {
      getAssignedIdentifiers(decl.id).forEach(function (id) {
		if (!(isVar && scope.bindings.get(id.name))) {
			let canDeclare = scopeNode === rootNode && isIdentifierASpecialValue(id)? false : true
			if (canDeclare) {
				let binding = new Binding(id.name, id, node.kind === "const", !isVar, isVar)
				allBindings.push(binding)
				binding.hasRefsInWith = withStack[withStack.length-1]
				scope.define(binding)
			}
		}
      })
    })
  }
  else if (node.type === 'ClassDeclaration') {
    var scopeNode = getNearestScopeNode(node, true)
    var scope = createScope(scopeNode)
    if (node.id && node.id.type === 'Identifier') {
		let canDeclare = scopeNode === rootNode && isIdentifierASpecialValue(node.id)? false : true
		if (canDeclare) {
			let binding = new Binding(node.id.name, node.id, false, true)
			allBindings.push(binding)
			binding.hasRefsInWith = withStack[withStack.length-1]
			scope.define(binding)
		}
    }
  }
  else if (node.type === 'FunctionDeclaration') {
	let id = node.id
	let validId = id && id.type === 'Identifier'
	let isSpecialValue = validId && isIdentifierASpecialValue(id)
	let isBlockScoped = currentFunctionContext.isStrictMode || isSpecialValue
    var scopeNode = getNearestScopeNode(node, isBlockScoped)
	if (!isBlockScoped) {
		let blockScopeNode = getNearestScopeNode(node, 1)
		if (blockScopeNode && blockScopeNode !== scopeNode) {
			let scope = getScope(scopeNode)
			scope.hasFunctionDeclarations = true
		}
	}
	var scope = createScope(scopeNode)
	let canDeclare = scopeNode === rootNode && isSpecialValue? false : true
	if (validId && canDeclare) {
		if (!scope.bindings.get(id.name)) { 
			let binding = new Binding(id.name, id, false, currentFunctionContext.isStrictMode, true)
			allBindings.push(binding)
			binding.hasRefsInWith = withStack[withStack.length-1]
			scope.define(binding)
		}
	}
  }
	if (isFunctionNode(node)) {
    var scope = createScope(node)
    node.params.forEach(function (param) {
      getAssignedIdentifiers(param).forEach(function (id) {
		let binding = new Binding(id.name, id)
		allBindings.push(binding)
		binding.hasRefsInWith = withStack[withStack.length-1]
		scope.define(binding)
      })
    })
  }
  else if (isBlockScopeNode(node)) {
	var scope = createScope(node)
  }
  
	if (node.type === 'FunctionExpression' || node.type === 'ClassExpression') {
    var scope = createScope(node)
    if (node.id && node.id.type === 'Identifier') {
	  let binding = new Binding(node.id.name, node.id)
	  allBindings.push(binding)
	  binding.hasRefsInWith = withStack[withStack.length-1]
	  scope.define(binding)
    }
  }
  else if (node.type === 'ImportDeclaration') {
	currentFunctionContext.isStrictMode = true
    var scopeNode = getNearestScopeNode(node, false)
    var scope = createScope(scopeNode)
    getAssignedIdentifiers(node).forEach(function (id) {
	  let binding = new Binding(id.name, id)
	  allBindings.push(binding)
	  binding.hasRefsInWith = withStack[withStack.length-1]
	  scope.define(binding)
    })
  }
  else if (node.type === 'CatchClause') {
    var scope = createScope(node)
    if (node.param) {
      getAssignedIdentifiers(node.param).forEach(function (id) {
		let binding = new Binding(id.name, id)
		allBindings.push(binding)
		binding.hasRefsInWith = withStack[withStack.length-1]
		scope.define(binding)
      })
    }
  }
}

function getParentScope (node) {
  var parent = node
  while (parent.parent) {
	parent = parent.parent
	var scope = getScope(parent)
    if (scope) return scope
  }
}

function getNearestScopeNode (node, canBeBlockScope, checkCurrent) {
  var parent = checkCurrent? node : node.parent
  while (parent) {
    if (isFunctionNode(parent)) {
      break
    }
    if (canBeBlockScope && isBlockScopeNode(parent)) {
      break
    }
    if (parent.type === 'Program') {
      break
    }
    parent = parent.parent
  }
  return parent
}
// Get the scope that the node is in
function getNearestScope (node, canBeBlockScope, checkCurrent) {
	var parent = checkCurrent? node : node.parent
	while (parent) {
		if (isFunctionNode(parent)) {
			break
		}
		if (canBeBlockScope && isBlockScopeNode(parent)) {
			let scope = getScope(parent)
			if (scope) return scope
		}
		if (parent.type === 'Program') {
			break
		}
		parent = parent.parent
	}
	let scope = getScope(parent)
	return scope
}
function isBlockScopeNode(node) {
	return node.type === 'BlockStatement' || node.type === 'ForStatement' || node.type === 'ForInStatement' || node.type === 'ForOfStatement'
}
function isIdentifierASpecialValue(identidierNode) {
	let name = identidierNode.name
	return name === "Infinity" || name === "undefined" || name === "NaN"
}
function isSpecialValueAVariable(identidierNode) {
	let name = identidierNode.name
	let scope = getNearestScope(identidierNode, 1)
	while(scope){
		if (scope.has(name)) return true
		scope = scope.parent
	}
	return false
}

// Get the scope node that this identifier has been declared in
function getDeclaredScope (id) {
  var parent = id
  if ((id.parent.type === 'FunctionDeclaration'|| id.parent.type === 'FunctionExpression') && id.parent.id === id) {
    parent = id.parent
  }
  while (parent.parent) {
    parent = parent.parent
    if (parent[kScope] && parent[kScope].has(id.name)) {
      break
    }
  }
  return parent
}

function registerReference (node) {
  var scopeNode = getDeclaredScope(node)
  var scope = getScope(scopeNode)
  var binding
  if (scope) {
	if (scope.has(node.name)) {
		binding = scope.add(node.name, node)
	}
	else {
		binding = scope.addUndeclared(node.name, node)
	}
  }
  
  if (binding) {
	  let _with2 = withStack[withStack.length-1]
	  if (binding.hasRefsInWith !== true && binding.hasRefsInWith != _with2) {
		binding.hasRefsInWith = true
	  }
  }
}

function isObjectKey (node) {
  return node.parent.type === 'Property' && !node.parent.computed &&
    node.parent.key === node &&
    node.parent.value !== node
}
function isMethodOrPropertyDefinition (node) {
  return node.parent.key === node && (node.parent.type === 'MethodDefinition' || node.parent.type === 'PropertyDefinition')
}
function isImportName (node) {
  return node.parent.type === 'ImportSpecifier' && node.parent.imported === node
}

function isVariable (node) {
	var _isVariable = node.type === 'Identifier' && 
		!isObjectKey(node) &&
		!isMethodOrPropertyDefinition(node) &&
		!isFunctionArgumentsKeyword(node) &&
		node.parent.type !== 'LabeledStatement' &&
		(node.parent.type !== 'MemberExpression' || node.parent.object === node ||
			(node.parent.property === node && node.parent.computed)) &&
		!isImportName(node) &&
		(isIdentifierASpecialValue(node)? isSpecialValueAVariable(node): true)
  	return _isVariable
}
function isLabel (node) {
  return node.type === 'Identifier' && node.parent.label === node
}

function isFunctionArgumentsKeyword (node) {
	if (node.name == "arguments") {
		var functionNode = getEnclosingFunctionNode(node)
		if (functionNode) {
			var declaredScopeInFunction = isVariableDeclaredInFunction(node)
			if(!declaredScopeInFunction){
				functionNode.uses_arguments = true
				return true
			}
		}
	}
}
function getEnclosingFunctionNode (node, includingArrow) {
	var n = node
	while (n = n.parent) {
		if(n.type === 'FunctionDeclaration' || n.type === 'FunctionExpression'){
			return n
		}
		if(n.type === 'ArrowFunctionExpression'){
			return includingArrow? n : false
		}
	}
}
function isVariableDeclaredInFunction (identifierNode) { // returns the Scope if it is
	var name = identifierNode.name
	var n = identifierNode
	n = n.parent
	while (n) {
		var scope = n[kScope]
		if (scope && scope.has(name)) {
			return scope
		}
		
		if(isFunctionNode(n)){
			return false
		}
		n = n.parent
	}
}

function isFunctionNode (node) {
	return node.type === 'FunctionDeclaration' || node.type === 'FunctionExpression' || node.type === 'ArrowFunctionExpression'
}








// dash-ast ========================================================================================================================
/**
 * Call `cb` on each node in `ast`. If `cb` is an object, `cb.enter` is called before processing a Node's children,
 * and `cb.leave` is called after processing a Node's children.
 */
function dash (ast, cb) {
	assert(ast && typeof ast === 'object' && typeof ast.type === 'string',
	  'dash-ast: ast must be an AST node')
  
	if (typeof cb === 'object') {
	  assert(typeof cb.enter === 'function' || typeof cb.leave === 'function',
		'dash-ast: visitor must be an object with enter/leave functions')
  
	  walk(ast, null, cb.enter || undefined, cb.leave || undefined)
	} else {
	  assert(cb && typeof cb === 'function',
		'dash-ast: callback must be a function')
  
	  walk(ast, null, cb, undefined)
	}
	
	function walk (node, parent, enter, leave) {
	  var cont = enter !== undefined ? enter(node, parent) : undefined
	  if (cont === false) return
	
	  for (var k in node) {
		if (has(node, k)) {
		  if (k === 'parent') continue
		  if (isNode(node[k])) {
			walk(node[k], node, enter, leave)
		  } else if (Array.isArray(node[k])) {
			walkArray(node[k], node, enter, leave)
		  }
		}
	  }
	
	  if (leave !== undefined) leave(node, parent)
	}
	
	function walkArray (nodes, parent, enter, leave) {
	  for (var i = 0; i < nodes.length; i++) {
		if (isNode(nodes[i])) walk(nodes[i], parent, enter, leave)
	  }
	}
	
	function isNode (node) {
	  return typeof node === 'object' && node && typeof node.type === 'string'
	}
	
	function has (obj, prop) {
	  return Object.prototype.hasOwnProperty.call(obj, prop)
	}
  }
  
  
  
  
  
  
  
  
// fixed get-assigned-identifiers ========================================================================================================================
/**
 * Get a list of all identifiers that are initialised by this (possibly destructuring)
 * node.
 *
 * eg with input:
 *
 * var { a: [b, ...c], d } = xyz
 *
 * this returns the nodes for 'b', 'c', and 'd'
 */
function getAssignedIdentifiers (node, identifiers) {
	assert.equal(typeof node, 'object', 'get-assigned-identifiers: node must be object')
	assert.equal(typeof node.type, 'string', 'get-assigned-identifiers: node must have a type')
  
	identifiers = identifiers || []
  
	if (node.type === 'ImportDeclaration') {
	  node.specifiers.forEach(function (el) {
		getAssignedIdentifiers(el, identifiers)
	  })
	}
  
	if (node.type === 'ImportDefaultSpecifier' || node.type === 'ImportNamespaceSpecifier' || node.type === 'ImportSpecifier') {
	  node = node.local
	}
  
	if (node.type === 'RestElement') {
	  node = node.argument
	}
	if (node.type === 'Property') {
		getAssignedIdentifiers(node.value, identifiers)
	}
	
	if (node.type === 'AssignmentPattern') {
	  node = node.left
	}
  
	if (node.type === 'ArrayPattern') {
	  node.elements.forEach(function (el) {
		// `el` might be `null` in case of `[x,,y] = whatever`
		if (el) {
		  getAssignedIdentifiers(el, identifiers)
		}
	  })
	}
  
	if (node.type === 'ObjectPattern') {
	  node.properties.forEach(function (prop) {
		if (prop.type === 'Property') {
		  getAssignedIdentifiers(prop.value, identifiers)
		} else if (prop.type === 'RestElement') {
		  getAssignedIdentifiers(prop, identifiers)
		}
	  })
	}
  
	if (node.type === 'Identifier') {
	  identifiers.push(node)
	}
  
	return identifiers
  }
  
  
  
  
  

  
  
  
  
