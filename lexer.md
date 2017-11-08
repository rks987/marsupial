# lexer.md

The lexer breaks the program into a stream of tuples consisting of 
* a token-type, 
* a token, 
* the following whitespace, 
* a location (for use in messages to the user). 

Initially there is just an escape character which is % by default (we assume % in the following). 
There is one regular expression that is predefined:
  %/ ...a lexer command... to end of line.

The defined lexer commands are:
* include file -- includes the specified file. Languages are defined by a specific include 
file which is included automatically. For wombat it is $WOMBAT/wombat.wh.
* token token-type priority regular-expression -- adds a possible token match.

At each point in the text, an anchored match is done against all defined regular expressions 
at each level. It is permitted for more than one to match at a level as long as the resulting 
token and token-type are the same.

In wombat only ascii characters are used, but programmers can add their own extra ones as long as 
they don’t cause conflicts. For example in wombat an identifier starting with an underscore (\_) 
has token-type freeVariable. But the programmers might like to say that sequences of greek letters 
also return a freeVariable token (thus avoiding the clunky \_). 
* FreeVariable. Starts with underscore in default wombat.
* NewFreeVariable. Precede with backquote in wombat.
* Identifier. Sequence of letters, digits, underscore but not starting with digit or underscore.
* NewIdentifier. Precede with backquote in wombat. Cannot be redeclared in same scope.
* OperatorOnly. Any sequence of characters that is allowed as a (sub) operator but not allowed 
as an identifier.
* String. Between 2 double-quotes with backslash escapes.
* Number. Digits then optionally a dot and one or more digits.

Programmers supply a non-negative decimal priority when adding token types, used only for its 
ordering (as in the Dewey-decimal library system). The lexer will check for matches in descending 
priority order. This makes it possible to add, for example, \<subscript> and \</subscript> as tokens 
without that conflicting with a bare \<. More than one match is allowed at a priority level, as long as 
they return the same result.

The lexer then returns a stream of tokens with extra information:
* token
* token type
* preceding indentation (if at start of line, else -1)
* following white space? (false if following token is adjacent)
* source file
* location (line num, char pos)
