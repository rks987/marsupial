# compiler.py

# A typical token:
#  {'token': 'true', 'tokType': 'Identifier', 'indent': -1, 'gotWhite': True, 
#   'location': ('src/wombat.wh', 25, 13)}

# FIXME the lexer should return a token with the important characters (e.g. remove
# the ` from a new identifier). Doing stuff here is a hack.
# So operator code should check for TokenType as identifier or operatorOnly.

import utility as U
import mast as A
import lexer
import moperator as op # build and parse operators
import collections as C
import re

operatorRE = re.compile(r'\s*"((?:[^\\"]|\\.)+)"\s+([^\n]+)\n?$')

def doMCTcmd(cmd,tok):
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
        U.die("unknown MCTcmd: "+cmd,*tok.location) 
    return defaultOperand

# for the function for an operator or various adjustment functions, there
# are 2 possibilities. Either the function is callable and is applied
# at compile time, or it is an Ast that will be a run time function
def opFun(fun,ast):
    if fun==None: return ast # mostly for adjustment cases, but also ()s
    if callable(fun):
        return fun(ast)
    else:
        pp = A.AstTuple(members=[fun,ast])
        return A.AstCall(procParam=pp)
 
# At any point we are a hierarchy of operators. For each operator we are in we are
# at a position which is a list of indices into the subops, and subsubs, etc.
# From that position we know (nextPossibles) what the possible proper subops are;
# and if there is no nextMandatory then we need to also consider the nextPossibles
# at one layer up.
# opCtx points to current parentCtx and a set of (opInfo, indexList) pairs. If the 
# token is one of the nextPossibles of 1st pair then (a) fill in opt and rept params up 
# to that; (b) adjust indexList; (c) if it was mandatory then it must be same as
# nextMandatory (1st pair), so delete all the others with a different nextMandatory.
# If not in nextPossibles then (a) see if it is nextMandatory of one of other pairs,
# and if so delete all pairs that have a different nextMandatory; (b) otherwise
# it is the operator of some inner expr, so call getExpr recursively to get that.
# Also need to catch the case where there is/isn't an intervening operand.

OpCtx = namedtuple('OpCtx','upOpCtx,indx,altOpInfos') # indx is where we are in any
                                                     # of opInfos -- op.OpInfo

def posSubop(token,opCtx)
    # remember altOpInfos are all the same on opt or repeat, can only differ
    # in nextMandatory (=nextPossibles[-1] if present)
    if token in opCtx.altOpInfos[0].subops[opCtx.indx].v['nextPossibles']:
        return True
    for oi in opCtx.altOpInfos:
        if token == oi.subops[opCtx.indx].v['nextMandatory']:
            return True
    # if any of the options has no nextMandatory, then we need to look up
    for oi in opCtx.altOpInfos:
        if oi.subops[opCtx.indx].v['nextMandatory']==None:
            return posSubop(token,opCtx.upOpCtx)
    return False
# where does indx go up???

def getExpr(toks,left,prio,opCtx,noneOK):
    # toks is the token generator. Can push tokens back using prependGen
    # left is the left parameter if there is one
    # prio is the right priority if the caller has gone past mandatory subops
    # opCtx
    # noneOK -- true if we might have no expr (returning None)
    #
    # return an ast, and the token generator as possibly modified
    global defaultOperand
    tok = next(toks,None)
    if tok.tokType=='MCTcmd':
	assert tok.token[0:1]=='%^'
	doMCTcmd(tok.token[2:],tok)
        return defaultOperand,toks # unit=() in wombat
    # we're at the start here - get the relevant opInfo
    #
    # In the following: operators last forever and aren't superceded by identifers FIXME
    #
    opDict = None
    if posSubop(tok.token,opCtx) or (tok.tokenType in ['identifier','operatorOnly'] and \
       left==None and tok.token not in op.noLeft and tok.token in op.withLeft):
        # better insert defaultOperand
        assert left==None and noneOK==False
        defaultOperandTok = lexer.Token(token='!!defaultOperand',tokType='operatorOnly', \
                                        indent=None,whiteB4=False,location=tok.location)
        toks = prependGen(tok,toks) # backup a bit
        tok = defaultOperandTok
        opDict = op.noLeft # must have no right as well
        assert tok.token in opDict
    elif (tok.tokenType in ['identifier','operatorOnly']): # might be an operator
        opDict = op.withLeft if left!=None else op.noLeft
        if tok.token in opDict: # run with that
            pass # we're happy
        elif left==None and tok.token in op.withLeft: # maybe we can get a defaultOperand
            assert False # already handled this case and inserted defaultOperand
        elif left!=None: # didn't find something to pick it up, insert " " or ""
            toks = prependGen(tok,toks) # backup a bit
            tok = lexer.Token(token=(" " if tok.whiteB4 else ""),tokType='operatorOnly', \
                          indent=-1,whiteB4=False,location=tok.location)
            opDict = op.withLeft # must have a right as well
            assert tok.token in opDict
        else:
            assert left==None and tok.token not in op.withLeft
            # must be an existing identifier (or free identifier?)
            opDict = None
    if opDict==None:
        if tok.tokenType in ['String','Number','Atom']:
            return A.AstConstant(const=tok.token)
        #assert tok.tokenType in ['Identifier','NewIdentifier','FreeVariable','NewFreeVariable']
        if tok.tokenType=='Identifier':
            iden = tok.token
            IdClass = A.AstIdentifier
        elif tok.tokenType == 'NewIdentifier':
            IdClass = A.AstNewIdentifier
            iden = tok.token[1:] # HACK FIXME
            assert tok.token[0]=='`'
        elif tok.tokenType == 'FreeVariable':
            IdClass = A.AstFreeVariable
        elif tok.tokenType == 'NewFreeVariable':
            IdClass = A.AstNewFreeVariable
            iden = tok.token[1:] # HACK FIXME
            assert tok.token[0]=='`'
        else:
            assert False
        return IdClass(identifier=iden),toks
    # here ends interlude of special cases: back to operators

    # at this point we are ready to start chewing up subops. It's exactly like subsubs,
    # except that ...
    oiL = [opDict(tok.token)] if isinstance(opDict(tok.token),opInfo) else \
                                 [opDict(t) for t in opDict(tok.token)] 
    opInfo,rAsts,toks = getSubops(toks=prependGen(tok,toks),\ # want to reprocess op = 1st subop
                                  opCtx=OpCtx(upOpCtx=opCtx,indx=0,altOpInfos=oiL))
    if opInfo.left!=None and isinstance(rAsts,A.AstNode):
        pAsts = [opInfo.left,rAsts]
    elif opInfo.left!=None: # rAsts is a list of multiple params
        pAsts = [opInfo.left]+rAsts # add in left param
    elif opInfo.left==None:
        pAsts = rAsts
    opFun(opInfo.astFun,pAsts)
   return ast,toks

# we get a list of possible SSsubop lists, expecting to match one. We return a tuple
# with (1) the one we matched; (2) list of param ASTs; (3) the token generator. We will
# have pushed back the token that has lower left precedence than our right precedence.
def getSubops( toks,opCtx):
    tok = next(toks,None)
    pAstL = [] # list for param ast (right part of param if top level)
    indx = 0  # this is the index into each list in oiL
    oiL = opCtx.altOpInfos[:] # take a copy
    while True:
        # if the next sop is mandatory in any of oiL then we must have it, or we can
        # delete the entries in oiL that do. Of course for the start of a top level
        # we will have it because that's how we got here at all.
        oiL = [oiL[i] for i in range(len(oiL)) if oiL[i].subops[indx].occur!='mandatory' or \
                                                  oiL[i].subops[indx].subop==tok.token]
        assert oiL!=[]
        # -- the following special case not needed: is handled fine by the general code
        #if len(oiL[0])-1==indx and oiL[0].subops[indx].v['param']==None:
        #    # the trailing subop has no right
        #    assert len(oiL)==1 # can't have a competitor for this!
        #    assert oiL[0].subops[indx].occur=='mandatory'
        #    return oiL[0],pAstL,toks
        numMandatory = len([i for i in range(len(oiL)) \
                                if oiL[i].subops[indx].occur=='mandatory'])
        # can you have the same token as optional/repeating in one possible subops match
        # while it is mandatory in a competing one? For the moment say no. Doc it FIXME
        assert numMandatory==0 or numMandatory==len(oiL) # all in sync.
        # They all have to agree on optional and repeat params, so we can just advance
        # indx till we hit tok, adding 0 tuples to the ast till we get there.
        # so now we'll append an empty list to pAstL to get params for this sop (if any)
        pAstL.append([])
        while True:
            # come back here till past this sop
            nextSop = oiL[0].subops[indx] # all same - deleted different mandatory from oiL
            if nextSop.subop!=tok.token: # finished repeat
                if nextSop.occur=='mandatory': 
                    assert len(pAstL[-1])==1
                    pAstL[-1] = pAstL[-1][0] # un tuple it
                if nextSop.occur=='optional': assert len(pAstL[-1])<2
                if nextSop.v['param']==None: 
                    assert len(pAstL[-1])=0
                    pAstL = pAstL[:-1] # no param expected, so remove it
                break # will loop on outer 'while True' - get more missing/optional tokens
            # we match the current token. If mandatory then we might have some with a
            # following parameter, and some without. Let's count
            numWithoutParam = len([i for i in range(len(oiL))\
                                              if oiL[i].subops[indx].v['param']==None])
            noneOK = numWithoutParam > 0 # we'll disable defaultOperand
            # can't have both noneOK and a param with precedence, because noneOK requires
            # a following subop to demonstrate it, or it is a trailing mandatory.
            precedence = None if noneOK else oiL[0].subops[indx].precedence # 0th - all same
            if oiL[0].subops[indx].v['subsubs']==None: # ??? was !=
                p,toks = getExpr(toks=toks,left=None,prio=precedence,opCtx=opCtx,noneOK=noneOK)
                p = opFun(oiL[0].subops[indx].v['oneAdjust'], p)
            else: # get subsubs
                ssOpInfo = op.OpInfo(p, oiL[0].subops[indx].v['allAdjust'], \
                                     oiL[0].subops[indx].v['subsubs'] ) # faked up OpInfo
                ssOpCtx = OpCtx(upOpCtx=opCtx, indx=0 ,altOpInfos=[ssOpInfo]) # only 1 OpInfo
                oi,pl,toks = getSubops(toks,ssOpCtx) # 
                assert oi==ssOpInfo # what else?
                p = opFun(oiL[0].subops[indx].v['allAdjust'],A.AstTuple(members=pl))
            if p==None: # we eliminate oiL that require a parameter here
                # we assume that a param with no operand can't have subsubs -- document FIXME
                oiL = [oiL[i] for i in range(len(oiL)) if oiL[i].subops[indx].v['param']!=None]
            else: # we eliminate oiL that require no parameter
                oiL = [oiL[i] for i in range(len(oiL)) if oiL[i].subops[indx].v['param']==None]
            if p!=None: 
                pAstL[-1].append(p)
            tok = next(toks,None)
        indx = indx+1
        if indx==len(oiL[0]): # at end
            assert len(oiL)==1
            return oiL[0],pAstL,prepend(tok,toks))

def compiler(toks):
    #global tokPairs = pairGen(tokenGen)
    #toksBackup = iterBackup(tokenGen)
    doMCTcmd('operator "m.builtin[\'id\']" ["!!SOF"] () ["!!EOF"]')
    doMCTcmd('operator "m.builtin[\'defaultOperand\']" ["!!DefaultOperand"]')
    #return getExpr(tokPairs,None,0,[],None)
    opCtx = OpCtx(upOpCtx=None,indx=0,altOpInfos=[])
    return getExpr(toks=toks,left=None,prio=None,opCtx=opCtx,upAst=None,closure=None,noneOK=False)

if __name__=="__main__":
    import lexer
    global ast
    ast = compiler(lexer.lexer("src/wombat.wh"))
    print(ast)

# DELETED
        
#    global tok # so I don't have to pass the filename/line/pos everywhere
#    (tok,nextTok) = next(tokPairs,None)
#    if tok.tokType=='MCTcmd':
#	assert tok.token[0:1]=='%^'
#	doMCTcmd(tok.token[2:])
#        return defaultOperand # unit=() in wombat
#    # we're at the start here - get the relevant opInfo
#    opDict = op.withLeft if left else op.noLeft
#    if tok in opDict: # run with that
#        tokPairs.send(None) # we're happy
#        pass # ???
#    elif left==None and tok in op.withLeft: # maybe we can get a defaultOperand
#        (tok,nextTok) = tokPairs.send(defaultOperand,None) # backup a bit
#    elif left!=None: # didn't find something to pick it up, insert " " or ""
#    pass
    

# pairGen takes a generator and returns a generator that produces
# pairs (current,next), and also allows the return from the yield
# to insert into either the current or next value. The tricky thing
# is that the callers send gets the next yield, but we just yield None
# when there is no change.
#def pairGen(gen):
#    cur = None
#    nexty = gen.next()
#    saveNexty = None
#    while True:
#	ret = yield (cur,nexty) # goes to next, reurns on send
#        if nexty==None:
#            assert ret==None # don't allow changes at end
#            return
#	if ret == None:
#	    toSend = None
#	elif ret == (newCur,None)
#	    saveNexty = nexty
#            nexty = cur
#	    cur = newCur
#	    toSend = (cur,nexty)
#	elif ret == (None,newNext)
#	    saveNexty = nexty
#	    nexty = newNext
#	    toSend = (cur,nexty)
#        else:
#            assert False
#        yield toSend #response to send
#        if saveNexty != None:
#            cur = nexty
#            nexty = saveNexty
#            saveNexty = None
#        else:
#            cur = nexty
#            nexty = next(gen,None) # set to None at end of gen
#
#def iterBackup(gen): # maybe we don't need lookahead?
#    save = None
#    while True:
#        if save==None:
#            save = next(gen,None)
#            if save==None: return
#        ret = yield save
#        if ret==None:
#            save = None
#            continue
#        else:
#            yield ret
#            continue # will yield save again
#
#def prependBackup(hd,tl):
#    yield hd
#    assert None==toksBackup.send(None)
#    yield from tl

