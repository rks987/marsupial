# lexer.py -- turn file into iterator of tokens

import collections as C

Token = C.namedtuple('Token',['token','tokenType','indent','whiteB4','location'])

import utility as U
import re
white = re.compile(r"\s*") # always matches
upSlash = re.compile(r"\%\/")

import decimal
tokenByPrio = {}  # for each token priority, list of pat*patType
tokenPrios = []   # keep sorted list of Prios, 
def insertToken(tokenType, prio, tokRE):
    global tokenPrios
    if prio in tokenByPrio:
        tokenByPrio[prio].append((tokRE,tokenType))
    else:
        tokenByPrio[prio] = [(tokRE,tokenType)]
        tokenPrios = sorted([*iter(tokenByPrio.keys())],reverse=True)
    return

def lexer(fileName):
    lineNum = 0
    yield Token(token="!!SOF",tokenType="OperatorOnly",indent=0,whiteB4=False,
               location=(fileName,0,0))
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
                n = re.compile(r"token\s+(\w+)\s+(\d+\.?\d*)\s+([^\n]+)")  \
                      .match(line,indent+2)
                if n:
                    #print(n[3])
                    insertToken(n[1], decimal.Decimal(n[2]), re.compile(n[3]))
                else:
                    raise Exception("unknown %/ cmd:"+line)
        else: # multiple ordinary tokens
            while pos!=len(line):
                found = None
                for p in tokenPrios:
                    if found!=None:
                        break
                    for (pat,patType) in tokenByPrio[p]:
                        tm = pat.match(line,pos)
                        if tm:
                            if found:
                                if found[0]!=tm[0] or found[1]!=patType:
                                    U.die("conflicting tokens: "+found[0]+" "+tm[0],
                                        fileName,lineNum,pos)
                            else:
                                found = (tm[0],patType)
                    if found:
                        wm = white.match(line, pos+len(found[0]))
                        gotWhite = pos+len(found[0])==len(line) or len(wm[0])>0
                        if found[1]!='Comment':
                            yield Token(token=found[0],tokenType=found[1],indent=indent,
                                        whiteB4=whiteB4, location=(fileName,lineNum,pos))
                        whiteB4 = gotWhite
                        indent = -1
                        pos += len(found[0])+len(wm[0])
                    break
    yield Token(token="!!EOF",tokenType="OperatorOnly",indent=0,whiteB4=True,
               location=(fileName,lineNum+1,0))
    return
# above is too complicated...FIXME

if __name__ == "__main__":
    # execute only if run as a script
    for tok in lexer("wombat.wh"):
        print(tok)
