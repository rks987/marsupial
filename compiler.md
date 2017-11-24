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

\[Otherwise % treated like anything else, but the system library it also goes 
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
 
 _!!! the following is from marsupial overview doc, and should be reconciled with above_

Compile time commands come between %^ and end-of-line in wombat. Currently:
   * import: imports exported "operators" (including identifiers) from a wombat package. Packages are half-compiled and can't have side effects.
   * package: name of package.
   * export: list of identifiers and operators (only from a package).
   * operator: Define new operators.
   * defaultOperand: What you get for () -- assuming () operator defined sensibly.
   
There is also \%\{ ... }, which contains MCTL code that generates a bit of AST that fits into the program where any expression would.

The meaning of a program is determined left-to-right, so the identifying operator is the first suboperator. Other suboperators are only active after their operator and in places where they would be valid. The sequence of suboperators are a simple regular expression. Each suboperator can be mandatory, or optional or repeating. In addition each suboperator specifies if it has a following argument. And each can have even lower suboperators with the same rules. Each suboperator can be one of:
   * mandatory -- the operator itself is, of course, mandatory. Mandatory subops need not have an argument -- e.g. the ) subop of the ( operator -- in which case they don't output anything.
   * optional -- may or may not be present. These must have an argument. The output argument is a 0-tuple if absent, 1-tuple if present.
   * repeating -- 0 or more repeats. The output argument is a tuple. If you want 1 or more repeats then just do the same subop as mandatory, then as repeating.

An operator declaration is:
    operator "operator-string" op-output subops-declaration

A subops-declaration consists of alternating subop-entries in square brackets, and argument entries in parentheses which may be absent for mandatory subops with no following argument. If the operator has a left operand then the subops-declaration will start with an argument entry. The subop entry has the form: \["subop" mandatory|optional|repeating adjustment] -- "mandatory" is the default if omitted. The argument entry has the form: (decimal-precedence adjustment subsubops-declaration) -- all optional, so just () is common. If the subsubops-declaration is present (not allowed for left argument or right argument immediately after the actual operator) then it is lower subsubops that can (or must) follow that subop. The precedence is the left precedence for a left-argument of a suffix operator. It is the right precedence for other arguments that don't have any following mandatory suboperators.

The adjustment is code that adjusts the argument (e.g. convert a tuple to a list). The adjustment in the subop entry adjusts the combined result. For example a repeating subop produces a tuple and the argument adjustment applies to each one, but the subop adjustment applies to the combined tuple.
The op-output converts the result of the adjustment specified by the first subop (which is the operator) and makes it into the right sort of AST entry.
All this is happening at MCTL level. So when I say "converts tuple to list" that means it is code that takes the tuple AST and changes it into a call AST with the original becoming the 2nd part of the argument, and the AST for the convert function being the first part.

The same operator can have multiple meanings. It can have prefix and suffix forms. And, in either case, it can have multiple meanings based on subsequent mandatory suboperators as long as everything is the same up to that point. For example we have the list constructor \[1 2 3 4], but also the division of a list into head and tail \[1 | \[2 3 4]] (which = \[1 2 3 4]). In Wombat itself the procedure implementing an operator can be accessed as $operator\["\[" () "]"] and $operator\["\[" () "|"] where the list is of Union\[Unit String], with the units being where operands go. The strings are mandatory suboperators, with enough given to identify the operator.

-------------------------------------------------------------------------
more stuff to incorporate:
We allow overlap between operators as long as they can be read from
left to right: we don't have to go back and reparse what we've seen.
Brackets are an example. We want 3 operators defined:
%^operator "..." \["\["] ["]"]
%^operator "..." \["\["] () \[" ",repeating] () ["]"]
%^operator "..." \["\["] () \["|"] () ["]"]

Note that we allow there to be 2 operators with/without an operand
in left position, and after each mandatory subop, but not on the right
because that would lead to unsolvable ambiguity.

Note also that mandatory subops can't have subsubs (including mandatory
subops in subsubs). That's because (a) you get the same effect by moving
the subsubs up to follow the mandatory; and (b) it would then cause confusion
when comparing operators for compatibility.
