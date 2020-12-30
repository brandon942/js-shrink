# js-shrink
Supplemental javascript minifier.   
Shortens string literals, property names, variable names, builtin values.  
Basically, it turns all frequently used strings into short variables and prepends the declaration statement.  

Property names are not mangled (changed). They are preserved as they are but are still minified in the same way strings are. The minification is less effective than mangling but safer (can't break anything) and works for all property names. The downside is probably a slightly higher memory cost.

# Usage
```javascript
var shrink = require('js-shrink');

var out_code = shrink(in_code, {
	// posssible options:
	all: false, // shrink everything (enables all of the below options, in case they aren't enabled by default - they are)
	literals: true, // shrink string literals
	properties: true, // shrink all property names
	variables: true, // shrink all variable names
	undeclared: true, // shrink all undeclared globals
	values: true, // shrink null, undefined, Infinity
	this: true, // shrink all "this."
	classObjects: false, // to inline class-object properties and to remove unused properties (see below)
	allow0Gain: false, // to replace even if the character difference is 0
	quote: "`", // the quote character to use. Default ` because it is least likely to require escapes
	debug: false, // prints some debug info
})
```
   

# Class property inlining
If the option `classObjects` is set to true then class methods & properties will be inlined if they're used only once or removed if they aren't used anywhere. The comment `/* CLASS_OBJECT */` needs to be placed in front of the objects. This can only work safely for unique property names so names that are not unique are excluded from inlining.
```javascript

var myClass = /* CLASS_OBJECT */ {
	prop1: 1, // will be inlined in method2
	prop2: 1, // will be removed
	method1(){ // will be removed
		return 1
	},
	method2(){ // will be inlined in init
		return this.prop1
	},
	init(){
		this.method2()
		return "hi"
	},
}
myClass.init()


// Also works with the class syntax, no comment marker needed
class User {
	constructor(name) {}
	method1(){}
	method2(){}
}
```
