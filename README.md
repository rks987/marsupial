# marsupial
marsupial is the base language for Wombat. Wombat definitions are currently all in the file src/wombat.wh.

The components are:
* The lexer takes an input file (and included files) and produces a string of tokens
(giving the string, classification, prefix indent, trailing whitespace, filename, position).
See lexer.md.
* The compiler takes the string of tokens and produces an AST. The future plan is that all explicit closures
and primitive values will be replaced by specializations for all possible usage sites. See
compiler.md. 
* interp is intended as a debugging step, to execute the AST dynamically. But actually it
will also (with some minor improvement) do compile time type checking and compile time
optimization. The following 3 will thus be diffreent from originally envisaged.

Not implemented and will be different then envisaged:
* The typer then goes through figuring out the type of every expression and inserting
conversions from isA and convertsTo declarations as required. See typer.md.
* The coder then makes conversions from implementedBy to implement the code. It prefers to
implement by compileTime types. It then executes as much as possible at compileTime. If there
are any expressions left that haven't been translated to all desired target run time types
then it passes the AST back to typer. See coder.md.
* Then for each required target it outputs a target file, using the definitions of the
primitive procedures. See targeter.md.
