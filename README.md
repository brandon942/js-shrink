# js-shrink
Supplemental javascript minifier.
Shortens string literals, property names, variable names, builtin values.  
Basically, it turns all frequently used strings into short variables and prepends the declaration statement.

# Usage
<pre>
var shrink = require('js-shrink');

var out_code = shrink(in_code, {
	// posssible options:
	all: false, // shrink everything (enables all of the below options, in case they aren't enabled by default - they are)
	literals: true, // shrink string literals
	properties: true, // shrink all property names
	undeclared: true, // shrink all undeclared globals
	values: true, // shrink null, undefined, Infinity
	allow0Gain: false, // to replace even if the character difference is 0
	quote: "`", // the quote character to use. Default ` because it is least likely to require escapes
	debug: false, // prints some debug info
})
  </pre>
