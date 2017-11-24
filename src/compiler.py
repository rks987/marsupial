# compiler.py

# A typical token:
#  {'token': 'true', 'tokType': 'Identifier', 'indent': -1, 'gotWhite': True, 
#   'location': ('src/wombat.wh', 25, 13)}

import utility as U

import moperator as op # build and parse operators
import re

operatorRE = re.compile(r'\s*"((?:[^\\"]|\\.)+)"\s+([^\n]+)\n?$')

# pairGen takes a generator and returns a generator that produces
# pairs (current,next), and also allows the return from the yield
# to insert into either the current or next value. The tricky thing
# is that the callers send gets the next yield, but we just yield None
# when there is no change.
def pairGen(gen):
    cur = None
    nexty = gen.next()
    saveNexty = None
    while True:
	ret = yield (cur,nexty) # goes to next, reurns on send
        if nexty==None:
            assert ret==None # don't allow changes at end
            return
	if ret == None:
	    toSend = None
	elif ret == (newCur,None)
	    saveNexty = nexty
            nexty = cur
	    cur = newCur
	    toSend = (cur,nexty)
	elif ret == (None,newNext)
	    saveNexty = nexty
	    nexty = newNext
	    toSend = (cur,nexty)
        else:
            assert False
        yield toSend #response to send
        if saveNexty != None:
            cur = nexty
            nexty = saveNexty
            saveNexty = None
        else:
            cur = nexty
            nexty = next(gen,None) # set to None at end of gen

def doMCTcmd(cmd):
    if 'operator '==cmd[0:9]:
        mo = operatorRE.match(cmd[9:])
        if mo:
            op.doOperatorCmd(U.unquote(mo[1]),mo[2])
        else: 
            U.die("invalid operator decl: "+cmd,*tok.location)
    elif 'defaultOperand '==cmd[0:15]:
        global defaultOperand = eval(cmd[15:]) # must be an ASTree
    elif 'import '==cmd[0:7]:
        raise Exception("import not implemented -- FIXME")
    elif 'package '==cmd[0:8]:
        raise Exception("package not implemented -- FIXME")
    elif 'export '==cmd[0:7]:
        raise Exception("export not implemented -- FIXME")
    else:
        U.die("unknown MCTcmd: "+cmd,*tok['location']) 
    return defaultOperand

def getExpr(tokPairs,left,prio,sopsExpected,upAst):
    global tok # so I don't have to pass the filename/line/pos everywhere
    (tok,nextTok) = next(tokPairs,None)
    if tok.tokType=='MCTcmd':
	assert tok.token[0:1]=='%/'
	doMCTcmd(tok.token[2:])
        return defaultOperand # unit=() in wombat


    pass
    

def compiler(tokenGen):
    global tokPairs = pairGen(tokenGen)
    doMCTcmd('operator "m.builtin[\'id\']" ["!!SOF"] () ["!!EOF"]')
    return getExpr(tokPairs,None,0,[],None)

if __name__=="__main__":
    import lexer
    global ast
    ast = compiler(lexer.lexer("src/wombat.wh"))
    print(ast)
