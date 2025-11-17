# js-shrink
Supplemental javascript minifier.   
Shortens string literals, property names, variable names, builtin values.  
It turns all frequently used strings into short variables and prepends the declaration statement.  

Property names are not mangled (changed). They are preserved as they are but they are shortened in the same way strings are. The minification is less effective than mangling but safer (can't break anything) and works for all property names. The downside might be a slightly higher memory cost.

# Usage
```javascript
var shrink = require('js-shrink');

var out_code = shrink(in_code, {
	// posssible options:
	all: false, // shrink everything except: numbers, classObjects, functions
	literals: true, // shrink string literals
	properties: true, // shrink all property names
	variables: true, // shrink all variable names
	undeclared: true, // shrink all undeclared globals
	values: true, // shrink null, undefined, Infinity
	this: true, // shrink all "this."
	functions: false, // turns non arrow functions into arrow functions wherever possible
	numbers: false, // shrink numbers
	numbers_minLength: 3, // numbers shorter than this won't be shrunk
	numbers_minOccurrences: 5, // numbers won't be replaced with variables if they occur less often than this
	numbers_maxNumberOfVariables: 20, // make no more than this number of variables (for the most frequently occuring numbers)
	classObjects: false, // to inline class-object properties and to remove unused properties (see below)
	classObjects_classesNeedCommentMarker: false,
	classObjects_allowInliningOutsideOfTheClass: true, // whether to allow class properties to be inlined outside of the class/object
	classObjects_inlineConstantsMaxNumberOfTimes: 3, // properties holding strings/numbers won't be inlined if they're used more often than this
	allow0Gain: false, // whether to replace strings or properties even if the character difference is 0
	quote: "`", // the quote character to use (default: `)
	globalsToNotShrink: [], // undeclared globals to exclude
	minPropertyNameLength: 3, // property names shorter than this length won't be shrunk
	sourceMap: { // source map options if a source map is to be generated
		generateSourceMapObject: false, // whether to generate a source map object; it is written to the property: "options.sourceMap.map"
		generateSourceMapInline: false, // whether to generate and add an inline source map comment
		map: null, // a prior source map object; this key will hold the new source map object if generateSourceMapObject is truthy
		fileName: "", // filename of the script file; this is only used to set the "file" property of the source map object
		sourceMapUrl: "", // url of the source map file; if specified then a '//# sourceMappingURL=' comment is added at the end
	},
	debug: false, // prints some debug information if truthy
	debugInfo: false, // will hold an info object about the result if debug is truthy
	rootIsStrictMode: false, // whether the script is in strict mode from the start
})
```
   

# Class property inlining
If the option `classObjects` is set to true then class methods & properties will be inlined if they are used only once or removed if they aren't used anywhere. The comment `/* CLASS_OBJECT */` needs to be placed in front of the object. This can only work safely for unique property names so properties with names that are not unique are excluded from inlining.
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
To prevent the removal of a property add `/* JSSHRINK_KEEP_PROPERTY */` in front of the property or method.
To prevent inlining into a method add `/* JSSHRINK_DONT_INLINE_HERE */` in front of the method.
These comments can be combined.
```javascript
class User {
	prop1 = 1 
	/* JSSHRINK_KEEP_PROPERTY */
	prop2 = 2 // won't be inlined in method2
	/* JSSHRINK_KEEP_PROPERTY */
	prop3_unused = 3 // won't be removed
	/* JSSHRINK_DONT_INLINE_HERE */
	method1(x){
		return x + this.prop1 // prop1 won't be inlined in method1
	}
	method2(){
		// method1 will be inlined but prop2 will not
		this.method1(this.prop2)
	}
}
```

# Other comment markers
To control where declarations are inserted add the comment `/* __JSSHRINK_DECLARATIONS_HERE__ */` or `// __JSSHRINK_DECLARATIONS_HERE__`

To prevent adding outside references to a function, place `/* !EXCLUDE! */` in front of it. This leaves properties, globals and string literals unchanged within the function. Variables and `this` can still be shrunk.
```javascript
/* !EXCLUDE! */ function f1(){ return 1 }
```
