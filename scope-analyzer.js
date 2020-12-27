// fixed scope-analyzer ========================================================================================================================
var assert = require('assert')

var kScope = Symbol('scope')
var kBinding = Symbol('bind')
var kIsDefinition = Symbol('def')

exports.createScope = createScope
exports.visitScope = visitScope
exports.visitBinding = visitBinding
exports.crawl = crawl
exports.analyze = crawl // old name
exports.clear = clear
exports.deleteScope = deleteScope
exports.nearestScope = getNearestScope
exports.scope = getScope
exports.getBinding = getBinding
exports.binding = getDeclaredBinding
exports.isDefinition = isNodeDefinition
exports.isBlockScopeNode = isBlockScopeNode


function getDeclaredBinding(node) {
	return node[kBinding]
}
function isNodeDefinition(node) {
	return node[kIsDefinition]
}


function Binding (name, definition) {
	this.name = name
	this.definition = definition
	this.references = new Set()
  
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
  
function Scope (parent) {
	this.parent = parent
	this.bindings = new Map()
	this.undeclaredBindings = new Map()
	if (parent) {
	  if (!parent.children) {
			parent.children = []
		}
		parent.children.push(this)
	}
}

Scope.prototype.define = function (binding) {
  if (this.bindings.has(binding.name)) {
    var existing = this.bindings.get(binding.name)
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
  return this
}
Scope.prototype.depth = function (functions) {
	var scope = this
	var depth = 1
	while (scope = scope.parent) (!functions || functions && !this.isBlock) && ++depth
	return depth
}

Scope.prototype.addUndeclared = function (name, ref) {
  if (!this.undeclaredBindings.has(name)) {
    this.undeclaredBindings.set(name, new Binding(name))
  }

  var binding = this.undeclaredBindings.get(name)
  binding.add(ref)
  return this
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


// create a new scope at a node.
function createScope (node, bindings) {
  assert.ok(typeof node === 'object' && node && typeof node.type === 'string', 'scope-analyzer: createScope: node must be an ast node')
  if (!node[kScope]) {
	var parent = getParentScope(node)
	let scope = new Scope(parent)
	node[kScope] = scope
	scope.n = node
	if(isBlockScopeNode(node)) scope.isBlock = true
  }
  if (bindings) {
    for (var i = 0; i < bindings.length; i++) {
      node[kScope].define(new Binding(bindings[i]))
    }
  }
  return node[kScope]
}

// Separate scope and binding registration steps, for post-order tree walkers.
// Those will typically walk the scope-defining node _after_ the bindings that belong to that scope,
// so they need to do it in two steps in order to define scopes first.
function visitScope (node) {
  assert.ok(typeof node === 'object' && node && typeof node.type === 'string', 'scope-analyzer: visitScope: node must be an ast node')
  registerScopeBindings(node)
}
function visitBinding (node) {
  assert.ok(typeof node === 'object' && node && typeof node.type === 'string', 'scope-analyzer: visitBinding: node must be an ast node')
  if (isVariable(node)) {
    registerReference(node)
  }
}

function crawl (ast) {
  assert.ok(typeof ast === 'object' && ast && typeof ast.type === 'string', 'scope-analyzer: crawl: ast must be an ast node')
  dash(ast, {
	  enter(node, parent){
		node.parent = parent
		visitScope(node)
	  },
	  leave(node, parent){
		removeEmptyBlockScope(node)
	  }
  })
  dash(ast, visitBinding)

  return ast
}
function removeEmptyBlockScope(node) {
	var scope = getScope(node)
	if (!scope) {
		return
	}
	if (!isBlockScopeNode(node)) {
		return
	}
	if(!scope.bindings.size){
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
	// Before: Scopes were created when variable declarations were encountered. This reduces the amount of scope objects (lower memory) but will break the script logic.
	// 	Problem: Child scopes aren't always assigned the correct parent.
	// EDIT: 
	// - Scopes (+every block scope) are created immediately whenever possible at the start of the node visit
	// - When a node visit is finished, it is checked if the node's scope is empty. If so then all subscopes are re-pointed to the parent scope, and the empty scope is deleted
  if (node.type === 'Program') {
    createScope(node)
  }
  else if (node.type === 'VariableDeclaration') {
    var scopeNode = getNearestScope(node, node.kind !== 'var')
    var scope = createScope(scopeNode)
    node.declarations.forEach(function (decl) {
      getAssignedIdentifiers(decl.id).forEach(function (id) {
        scope.define(new Binding(id.name, id))
      })
    })
  }
  else if (node.type === 'ClassDeclaration') {
    var scopeNode = getNearestScope(node)
    var scope = createScope(scopeNode)
    if (node.id && node.id.type === 'Identifier') {
      scope.define(new Binding(node.id.name, node.id))
    }
  }
  else if (node.type === 'FunctionDeclaration') {
    var scopeNode = getNearestScope(node, false)
    var scope = createScope(scopeNode)
    if (node.id && node.id.type === 'Identifier') {
      scope.define(new Binding(node.id.name, node.id))
    }
  }
	if (isFunction(node)) {
    var scope = createScope(node)
    node.params.forEach(function (param) {
      getAssignedIdentifiers(param).forEach(function (id) {
        scope.define(new Binding(id.name, id))
      })
    })
  }
  else if (isBlockScopeNode(node)) {
    var scope = createScope(node)
  }
  
	if (node.type === 'FunctionExpression' || node.type === 'ClassExpression') {
    var scope = createScope(node)
    if (node.id && node.id.type === 'Identifier') {
      scope.define(new Binding(node.id.name, node.id))
    }
  }
  else if (node.type === 'ImportDeclaration') {
    var scopeNode = getNearestScope(node, false)
    var scope = createScope(scopeNode)
    getAssignedIdentifiers(node).forEach(function (id) {
      scope.define(new Binding(id.name, id))
    })
  }
  else if (node.type === 'CatchClause') {
    var scope = createScope(node)
    if (node.param) {
      getAssignedIdentifiers(node.param).forEach(function (id) {
        scope.define(new Binding(id.name, id))
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

// Get the scope that a declaration will be declared in
function getNearestScope (node, blockScope) {
	// INFO: The for-statement itself is a scope
  var parent = node
  while (parent.parent) {
    parent = parent.parent
    if (isFunction(parent)) {
      break
    }
    if (blockScope && isBlockScopeNode(parent)) {
      break
    }
    if (parent.type === 'Program') {
      break
    }
  }
  return parent
}
function isBlockScopeNode(node) {
	return node.type === 'BlockStatement' || node.type === 'ForStatement' || node.type === 'ForInStatement' || node.type === 'ForOfStatement'
}

// Get the scope that this identifier has been declared in
function getDeclaredScope (id) {
  var parent = id
  // Jump over one parent if this is a function's name--the variables
  // and parameters _inside_ the function are attached to the FunctionDeclaration
  // so if a variable inside the function has the same name as the function,
  // they will conflict.
  // Here we jump out of the FunctionDeclaration so we can start by looking at the
  // surrounding scope
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
  if (scope && scope.has(node.name)) {
    scope.add(node.name, node)
  }
  if (scope && !scope.has(node.name)) {
    scope.addUndeclared(node.name, node) 
  }
}

function isObjectKey (node) {
  return node.parent.type === 'Property' &&
    node.parent.key === node &&
    // a shorthand property may have the ===-same node as both the key and the value.
    // we should detect the value part.
    node.parent.value !== node
}
function isMethodDefinition (node) {
  return node.parent.type === 'MethodDefinition' && node.parent.key === node
}
function isImportName (node) {
  return node.parent.type === 'ImportSpecifier' && node.parent.imported === node
}

function isVariable (node) {
  return node.type === 'Identifier' &&
  	node.name !== "Infinity" && node.name !== "undefined" && node.name !== "NaN" && 
	!isObjectKey(node) &&
	!isMethodDefinition(node) &&
	!isFunctionArgumentsKeyword(node) &&
	node.parent.type !== 'LabeledStatement' &&
    (node.parent.type !== 'MemberExpression' || node.parent.object === node ||
      (node.parent.property === node && node.parent.computed)) &&
    !isImportName(node)
}

function isFunctionArgumentsKeyword (node) {
	// only FunctionDeclaration & FunctionExpression have the special "arguments" keyword
	// but only if "arguments" is not declared as a local variable
	if (node.name == "arguments") {
		var functionNode = getEnclosingNormalFunctionNode(node)
		if (functionNode) {
			var declaredScopeInFunction = isVariableDeclaredInFunction(node)
			if(!declaredScopeInFunction){
				functionNode.uses_arguments = true
				return true
			}
		}
	}
}
function getEnclosingNormalFunctionNode (node) {
	var n = node
	while (n = n.parent) {
		if(n.type === 'FunctionDeclaration' || n.type === 'FunctionExpression'){
			return n
		}
		if(n.type === 'ArrowFunctionExpression'){
			return false
		}
	}
}
function isVariableDeclaredInFunction (identifierNode) { // returns the Scope if it is
	var name = identifierNode.name
	var n = identifierNode
	if ((n.parent.type === 'FunctionDeclaration'|| n.parent.type === 'FunctionExpression') && n.parent.id === n) {
		parent = id.parent
	  }
	n = n.parent
	while (n) {
		var scope = n[kScope]
		if (scope && scope.has(name)) {
			return scope
		}
		
		if(isFunction(n)){
			return false
		}
		n = n.parent
	}
}


 
  // estree-is-function ========================================================================================================================
  function isFunction (node) {
	if (typeof node !== 'object' || !node) {
	  throw new TypeError('estree-is-function: node must be an object')
	}
  
	if (typeof node.type !== 'string') {
	  throw new TypeError('estree-is-function: node must have a string type')
	}
  
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
  
  
  
  
  

  
  
  
  
