def die(s,fn,lineNum,pos):
    raise Exception(s+" in "+fn+"("+str(lineNum)+"/"+str(pos)+")")

import re
white = re.compile(r"\s*") # always matches
upSlash = re.compile(r"\%\/")

import decimal
tokenByPrio = {}  # for each token priority, list of pat*patType
tokenPrios = []   # keep sorted list of Prios, 
def insertToken(tokType, prio, tokRE):
    global tokenPrios
    if prio in tokenByPrio:
        tokenByPrio[prio].append((tokRE,tokType))
    else:
        tokenByPrio[prio] = [(tokRE,tokType)]
        tokenPrios = sorted([*iter(tokenByPrio.keys())],reverse=True)
    return

def lexer(fileName):
    lineNum = 0
    for line in open(fileName, "r", encoding="utf-8"):
        lineNum += 1
        indentM = white.match(line)
        indent = len(indentM[0]) # set to -1 after 1st token
        pos = indent
        if upSlash.match(line,indent):
            # lex command
            m = re.compile(r"include\s+(\S+)").fullmatch(line,indent+2)
            if m:
                yield from lexer(m[1])  # recurse
            else:
                n = re.compile(r"token\s+(\w+)\s+(\d+\.?\d*)\s+([^\n]+)").match(line,indent+2)
                if n:
                    #print(n[3])
                    insertToken(n[1], decimal.Decimal(n[2]), re.compile(n[3]))
                else:
                    raise Exception("unknown %/ cmd:"+line)
        else: # multiple ordinary tokens
            while pos!=len(line):
                found = None
                for p in tokenPrios:
                    if found:
                        break
                    for (pat,patType) in tokenByPrio[p]:
                        tm = pat.match(line,pos)
                        if tm:
                            if found:
                                if found[0]!=tm[0] or found[1]!=patType:
                                    die("conflicting tokens: "+found[0]+" "+tm[0],
                                        fileName,lineNum,pos)
                            else:
                                found = (tm[0],patType)
                    if found:
                        wm = white.match(line, pos+len(found[0]))
                        gotWhite = pos+len(found[0])==len(line) or len(wm[0])>0
                        yield dict(token=found[0],tokType=found[1],indent=indent,
                               gotWhite=gotWhite, location=(fileName,lineNum,pos))
                        indent = -1
                        pos += len(found[0])+len(wm[0])
                    break
    return

# too complicated...FIXME

if __name__ == "__main__":
    # execute only if run as a script
    for tok in lexer("wombat.wh"):
        print(tok)
