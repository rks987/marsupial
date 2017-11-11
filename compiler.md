#compiler.md

Main passes us a filename, we call lexer with that to get a stream of tokens.
We process these to build an AST which we return to main for further work.

The tokens have:
* token -- the source text matched
* tokType -- the lexical type 
* indent -- the indent if first token, else -1
* gotWhite -- true if actual white space rather than a forced break
* location=(fileName,lineNum,pos) -- used for error reporting

The only supported use of indent is: if there are any operators supporting
(sub)operator of type "Indent"+digit(>0) then (a) The digit is the length of soft
tabs (only 1 such allowed); (b) If a line has increased indent equal to that
digit then 1 such type "Indent"+digit (sub)operator is generated; (c) All other indents are
ignored and the current indent stays the same; (d) If a line has decreased
indent (relative to the current indent) that is a multiple of digit then enough
(sub)operators of type "UnIndent"+digit are generated. It is recommended that
digit be 4.

* %^ to EOL arrives as a single token of type MCTcmd. Currently defined: 
  * %^import package -- which import operators and identifiers.
  * %^operator ... -- which creates new operators
* %{ to }%, multiline, is an MCTexpr that is compile time code (currently python3) that 
needs to produce an AST to slot in its location. 

[Otherwise % treated like anything else, but the system library it also goes 
up a level: %(...) accesses up a level (closure templating),
and %.(...) goes to file level. But these are handled as operators.]

The tokens are processed by the active operators to create an AST. Each operator 
will map to a standard form:
 * "call": 2 parameters
 * "tuple": list of parameters
 * "closure": 1 parameter
 * "disjoint union": 2 parameters (atom(.left or .right), value)
 * "Tuple": 1 parameter List(Type)
 * etc

We end up with an AST of entries consisting of:
 * file/line/char pos of the operator
 * parent
 * standard form type (call/tuple/...)
 * list of pointers to parameters as appropriate

....
