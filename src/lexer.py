# lexer.py -- turn file into iterator of tokens

import collections as C

TokTT = C.namedtuple('TokTT',['text','tType'])
Token = C.namedtuple('Token',['tT','indent','whiteB4','location'])

import utility as U
import re
white = re.compile(r"\s*") # always matches
upSlash = re.compile(r"\%\/")

import decimal
TokenClass = C.namedtuple('TokenClass',['tokRE','adjust','tType'])
tokenClassByPrio = {}  # value for each TokenClass: list of (pattern,adjustment,tType)
tokenClassPrios = []   # keep sorted list of Prios, 
def insertTokenClass(prio, tokenClass):
    global tokenClassPrios
    if prio in tokenClassByPrio:
        tokenClassByPrio[prio].append(tokenClass)
    else:
        tokenClassByPrio[prio] = [tokenClass]
        tokenClassPrios = sorted([*iter(tokenClassByPrio.keys())],reverse=True)
    return

def lexer(fileName):
    lineNum = 0
    yield Token(tT=TokTT(text="!!SOF",tType="OperatorOnly"),indent=0,whiteB4=False,
               location=(fileName,0,0))
    # should allow %\ at end of line to split long lines (or %+ at start of next ?)
    for line in open(fileName, "r", encoding="utf-8"):
        whiteB4 = True # at a new line
        lineNum += 1
        indentM = white.match(line)
        indent = len(indentM[0]) # set to -1 after 1st token
        pos = indent
        if upSlash.match(line,indent):
            # lex command
            m = re.compile(r"include\s+(\S+)\n?").fullmatch(line,indent+2)
            if m:
                yield from lexer(m[1])  # recurse
            else:
                #e.g. %/token String 100 "U.unquote" (?P<token>"(\\"|\\\\|[^"\\])*")
                n = re.compile(r'token\s+(\w+)\s+(\d+\.?\d*)\s+("(?:[^\\"]|\\.)*")?\s*([^\n]+)')\
                      .match(line,indent+2)
                if n:
                    #print(n[4])
                    tokenClass = TokenClass(tType=n[1], tokRE=re.compile(n[4]),
                                            adjust=U.evalCallable(U.unquote(n[3])))
                    insertTokenClass(decimal.Decimal(n[2]), tokenClass)
                else:
                    raise Exception("unknown %/ cmd:"+line)
        else: # multiple ordinary tokens
            while pos!=len(line):
                Found = C.namedtuple('Found',['tokTT','length'])    
                found = None
                for p in tokenClassPrios:
                    if found!=None:
                        break # must have found one at higher priority
                    for tc in tokenClassByPrio[p]:
                        tm = tc.tokRE.match(line,pos)
                        if tm:
                            tt = tm['token'] if tc.adjust==None else tc.adjust(tm['token'])
                            tokTT = TokTT(text=tt,tType=tc.tType)
                            if found!=None:
                                if found!=Found(tokTT=tokTT,length=len(tm[0])):
                                    U.die("conflicting tokens: "+found.tokTT.text+" "+tm['token'],
                                        fileName,lineNum,pos)
                            else:
                                found = Found(tokTT=tokTT,length=len(tm[0]))
                if found:
                    wm = white.match(line, pos+found.length)
                    gotWhite = pos+found.length==len(line) or len(wm[0])>0
                    if found.tokTT.tType!='Comment':
                        yield Token(tT=found.tokTT,indent=indent,
                                    whiteB4=whiteB4, location=(fileName,lineNum,pos))
                    whiteB4 = gotWhite
                    indent = -1
                    pos += found.length+len(wm[0])
                else:
                    assert False
    yield Token(tT=TokTT(text="!!EOF",tType="OperatorOnly"),indent=0,whiteB4=True,
               location=(fileName,lineNum+1,0))
    return
# above is too complicated...FIXME

if __name__ == "__main__":
    # execute only if run as a script
    import sys
    for tok in lexer(sys.argv[1]):
        print(tok)
