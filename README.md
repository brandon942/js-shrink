# js-shrink
Supplemental javascript minifier.   
Shortens string literals, property names, variable names, builtin values.  
It turns all frequently used strings into short variables and prepends the declaration statement.  

Property names are not mangled (changed). They are preserved as they are but they're shortened in the same way strings are. The minification is less effective than mangling but safer (can't break anything) and works for all property names. The downside might be a slightly higher memory cost.

# Usage
```javascript
var shrink = require('js-shrink');

var out_code = shrink(in_code, {
	// posssible options:
	all: false, // applies all shrinking options
	literals: true, // shrink string literals
	properties: true, // shrink all property names
	variables: true, // shrink all variable names
	undeclared: true, // shrink all undeclared globals
	values: true, // shrink null, undefined, Infinity
	this: true, // shrink all "this."
	classObjects: false, // to inline class-object properties and to remove unused properties (see below)
	allow0Gain: false, // whether to replace a string/property even if the character difference is 0
	quote: "`", // the quote character to use. Default `
	globalsToNotShrink: [], // undeclared globals which are to be excluded
	sourceMap: { // source map options if a source map is to be generated
		generateSourceMapObject: false, // whether to generate a source map object; it is written to the "options.sourceMap.map" property
		generateSourceMapInline: false, // whether to generate and add an inline source map comment to the output
		map: null, // a prior source map object; this key will hold the new source map object if generateSourceMapObject is truthy
		fileName: "", // filename of the script file; this is only used to set the "file" property of the source map object
		sourceMapUrl: "", // url of the source map file; if specified then a '//# sourceMappingURL=' comment is appended to the output
	},
	debug: false, // prints some debug information
})
```
   

# Class property inlining
If the option `classObjects` is set to true then class methods & properties will be inlined if they are used only once or removed if they aren't used anywhere. The comment `/* CLASS_OBJECT */` needs to be placed in front of the object. This can only work safely for unique property names so names that are not unique are excluded from inlining.
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
# Other comment markers
To control where declarations are inserted add the comment `/* __JSSHRINK_DECLARATIONS_HERE__ */` or `// __JSSHRINK_DECLARATIONS_HERE__`

To prevent adding outside references to a function, place `/* !EXCLUDE! */` in front of it. This leaves properties, globals and string literals unchanged within the function. Variables and `this` are still shrunk.
```javascript
/* !EXCLUDE! */ function f1(){ return 1 }
```
