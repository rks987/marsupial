# compiler.py

# A typical token:
#  {'token': 'true', 'tokenType': 'Identifier', 'indent': -1, 'gotWhite': True, 
#   'location': ('src/wombat.wh', 25, 13)}

# FIXME the lexer should return a token with the important characters (e.g. remove
# the ` from a new identifier). Doing stuff here is a hack.
# So operator code should check for TokenType as identifier or OperatorOnly.

import utility as U
import mast as A
import lexer as L
import moperator as op # build and parse operators
import collections as C
import re

operatorRE = re.compile(r'\s*("(?:[^\\"]|\\.)+")\s+([^\n]+)\n?$')

def doMCTcmd(cmd,tok):
    if 'operator '==cmd[0:9]:
        mo = operatorRE.match(cmd[9:])
        if mo:
            op.doOperatorCmd(U.unquote(mo[1]),mo[2])
        else: 
            U.die("invalid operator decl: "+cmd,*tok.location)
    #elif 'defaultOperand '==cmd[0:15]:
    #    defaultOperand = eval(cmd[15:]) # must be an ASTree
    elif 'import '==cmd[0:7]:
        raise Exception("import not implemented -- FIXME")
    elif 'package '==cmd[0:8]:
        raise Exception("package not implemented -- FIXME")
    elif 'export '==cmd[0:7]:
        raise Exception("export not implemented -- FIXME")
    else:
        U.die("unknown MCTcmd: "+cmd,*tok.location) 
    return A.zeroTuple() #?? defaultOperand

# for the function for an operator or various adjustment functions, there
# are 2 possibilities. Either the function is callable and is applied
# at compile time, or it is an Ast that will be a run time function.
# If runtime then we convert the parameter list to a tuple.
# Note we don't untuple single arguments: do explicitly with adjustment.
def opFun(fun,astOrL):
    if callable(fun):
        return fun(astOrL) # whatever it is, fun has to handle it
    if isinstance(astOrL,A.AstNode):
        ast = astOrL 
    else:
        for a in astOrL: 
            assert isinstance(a,A.AstNode)
        ast = A.AstTuple(members=astOrL)
    if fun==None: 
        return ast # mostly for adjustment cases, but also ()s
    if isinstance(fun,A.AstNode):
        pp = A.AstTuple(members=[fun,ast])
        return A.AstCall(procParam=pp)
    else: 
        assert False
 
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

OpCtx = C.namedtuple('OpCtx','upOpCtx,indx,altOpInfos') # indx is where we are in any
                                                     # of opInfos -- op.OpInfo

def posSubop(token,opCtx):
    # remember altOpInfos are all the same on opt or repeat, can only differ
    # in nextMandatory (=nextPossibles[-1] if present)
    if opCtx==None or len(opCtx.altOpInfos)==0: return False
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
# 

def getExpr(toks,left,prio,opCtx,noneOK):
    # toks is the token generator. Can push tokens back using prependGen
    # left is the left parameter if there is one
    # prio is the right priority if the caller has gone past mandatory subops
    # opCtx
    # noneOK -- true if we might have no expr (returning None)
    #
    # return an ast, and the token generator as possibly modified
    tok = next(toks,None)
    def tokT():
        return tok.tokTT.text
    def posOp():
        return tok.tokTT.tokenType in ['Identifier','OperatorOnly']

    while (tok.tokTT.tokenType=='Comment') or (tok.tokTT.tokenType=='MCTcmd'):
        if tok.tokTT.tokenType=='MCTcmd':
            doMCTcmd(tok.tokTT.text,tok)
        tok = next(toks,None)

    # we're at the start here - get the relevant opInfo
    #
    # In the following: operators last forever and aren't superceded by identifers FIXME
    #
    opDict = None
    tokPosSubop = posOp() and posSubop(tokT(),opCtx)
    if tokPosSubop or (posOp() and (left==None) and (tokT() not in op.noLeft) and \
                       (tokT() in op.withLeft)):
        # should have had a left or operand preceding subop
        if tokPosSubop and noneOK: # none it is then
            return None,U.prependGen(tok,toks)
        # better insert defaultOperand
        assert left==None and noneOK==False
        defOperandTok = L.Token(tokTT=L.TokTT(text='!!defaultOperand',tokenType='OperatorOnly'),
                                        indent=None,whiteB4=False,location=tok.location)
        toks = U.prependGen(tok,toks) # backup a bit
        tok = defOperandTok
        opDict = op.noLeft # nb. must have no right as well
        assert tokT() in opDict
    if (posOp()): # might be an operator
        opDict = op.withLeft if left!=None else op.noLeft
        if tokT() in opDict: # run with that
            pass # we're happy
        elif left==None and tokT() in op.withLeft: # maybe we can get a defaultOperand
            assert False # already handled this case and inserted defaultOperand
        elif left!=None: # didn't find something to pick it up, insert " " or "" (sub)op
            toks = U.prependGen(tok,toks) # backup a bit
            tok = L.Token(tokTT=L.TokTT(text=(" " if tok.whiteB4 else ""),
                                        tokenType='OperatorOnly'),
                          indent=-1,whiteB4=False,location=tok.location)
            opDict = op.withLeft # must have a right as well
            assert tokT() in opDict
        else:
            assert left==None and tokT() not in op.noLeft
            # must be an existing identifier (or free identifier?)
            opDict = None
    if opDict==None:
        if tok.tokTT.tokenType in ['String','Number','Atom']:
            return A.AstConstant(const=tokT(),constType=tok.tokTT.tokenType)
        #assert tok.tokTT.tokenType in ['Identifier','NewIdentifier',
        #'FreeVariable','NewFreeVariable']
        IdClasses = {'Identifier': A.AstIdentifier, 'NewIdentifier':A.AstNewIdentifier,
                     'FreeVariable':A.AstFreeVariable, 'NewFreeVariable':A.AstNewFreeVariable}
        return IdClasses[tok.tokTT.tokenType](identifier=tokT()), toks
    # here ends interlude of special cases: back to operators

    # at this point we are ready to start chewing up subops. It's exactly like subsubs,
    # except that ...
    oiL = [opDict[tokT()]] if isinstance(opDict[tokT()],op.OpInfo) else \
                                [opDict[t] for t in opDict[tokT()]]
    # in next line, want to reprocess op = 1st subop
    opInfo,pAsts,toks = getSubops(toks=U.prependGen(tok,toks),\
                                  opCtx=OpCtx(upOpCtx=opCtx,indx=0,altOpInfos=oiL))
    if opInfo.left!=None: # rAsts is a list of multiple params
        pAsts[0] = left # add in left param
    ast = opFun(opInfo.astFun,pAsts)
    # at this point the next tok might be a nextPos for our parent, otherwise we've
    # got a left and we should keep looking
    tok = next(toks,None)
    if tok==None or posSubop(tokT(),opCtx):
        return ast,U.prependGen(tok,toks)
    # only option now is that what we have is a left operand for what follows
    expr,toks = getExpr(toks=U.prependGen(tok,toks),left=ast,prio=prio,opCtx=opCtx,noneOK=False)
    return expr,toks

# we get a list of possible SSsubop lists, expecting to match one. We return a tuple
# with (1) the one we matched; (2) list of param ASTs; (3) the token generator. We will
# have pushed back the token that has lower left precedence than our right precedence.
def getSubops( toks,opCtx):
    tok = next(toks,None)
    def tokT():
        return tok.tokTT.text
    maxPL = max((oi.paramLen for oi in opCtx.altOpInfos))
    pAstL = [None]*maxPL # list for param ast (might be truncated at the end)
    indx = 0  # this is the index into each list in oiL
    oiL = opCtx.altOpInfos[:] # take a copy
    while True:
        # if the next sop is mandatory in any of oiL then we must have it, or we can
        # delete the entries in oiL that do. Of course for the start of a top level
        # we will have it because that's how we got here at all.
        oiL = [oiL[i] for i in range(len(oiL)) if oiL[i].subops[indx].occur!='mandatory' or \
                                                  oiL[i].subops[indx].subop==tokT()]
        assert oiL!=[]
        if len(oiL[0].subops)-1==indx and oiL[0].subops[indx].v['param']==None:
            # note: this special case shouldn't be needed check/FIXME
            # the trailing subop has no right
            assert len(oiL)==1 # can't have a competitor for this!
            assert oiL[0].subops[indx].occur=='mandatory'
            return oiL[0],pAstL[:oiL[0].paramLen],toks
        numMandatory = len([i for i in range(len(oiL)) \
                                if oiL[i].subops[indx].occur=='mandatory'])
        # can you have the same token as optional/repeating in one possible subops match
        # while it is mandatory in a competing one? For the moment say no. Doc it FIXME
        assert numMandatory==0 or numMandatory==len(oiL) # all in sync.
        # They all have to agree on optional and repeat params, so we can just advance
        # indx till we hit tok
        sopPs = [] # put values for next sop here (might be repeating)
        while True:
            # come back here till past this sop
            nextSop = oiL[0].subops[indx] # all same - deleted different mandatory from oiL
            if nextSop.subop!=tokT(): # finished repeat
                if nextSop.v['param']==None: 
                    assert len(sopPs)==0
                elif nextSop.occur=='mandatory':
                    assert len(sopPs)==1
                    pAstL[nextSop.v['param'].pos] = sopPs[0] # un tuple it
                else:
                    if nextSop.occur=='optional': assert len(sopPs)<2
                    pAstL[nextSop.v['param'].pos] = A.AstTuple(members=sopPs)
                break # will loop on outer 'while True' - get more missing/optional tokens
            # we match the current token. If mandatory then we might have some with a
            # following parameter, and some without. Let's count
            numWithoutParam = len([i for i in range(len(oiL))\
                                              if oiL[i].subops[indx].v['param']==None])
            noneOK = numWithoutParam > 0 # we'll disable defaultOperand
            # can't have both noneOK and a param with precedence, because noneOK requires
            # a following subop to demonstrate it, or it is a trailing mandatory.
            precedence = None if noneOK else oiL[0].subops[indx].v['param'].precedence #all same
            p = None # not needed
            # Note that a subop with no parameter must be mandatory and have no subsubs.
            # [check doc FIXME].
            curOpCtx = OpCtx(upOpCtx=opCtx.upOpCtx, indx=indx, altOpInfos=oiL)
            if noneOK or (oiL[0].subops[indx].v['param'].subsubs==None): # ??? was !=
                p,toks = getExpr(toks=toks,left=None,prio=precedence,opCtx=curOpCtx,noneOK=noneOK)
                if p!=None:
                    oiL = [oiL[i] for i in range(len(oiL)) if oiL[i].subops[indx].v['param']!=None]
                    p = opFun(oiL[0].subops[indx].v['param'].oneAdjust, p) # ??
            else: # get subsubs
                ssOpInfo = op.OpInfo(p, oiL[0].subops[indx].v['allAdjust'], \
                                     oil[0].subops[indx].v['param'].ssParamLen, \
                                     oiL[0].subops[indx].v['param'].subsubs ) # faked up OpInfo
                ssOpCtx = OpCtx(upOpCtx=opCtx, indx=0 ,altOpInfos=[ssOpInfo]) # only 1 OpInfo
                oi,pl,toks = getSubops(toks,ssOpCtx) # 
                assert oi==ssOpInfo # what else?
                p = opFun(oiL[0].subops[indx].v['allAdjust'],A.AstTuple(members=pl))
            if p==None: # we eliminate oiL that require a parameter here
                # we assume that a param with no operand can't have subsubs -- document FIXME
                oiL = [oiL[i] for i in range(len(oiL)) if oiL[i].subops[indx].v['param']==None]
            else: # we eliminate oiL that require no parameter
                oiL = [oiL[i] for i in range(len(oiL)) if oiL[i].subops[indx].v['param']!=None]
            if p!=None: 
                sopPs.append(p)
            tok = next(toks,None)
        indx = indx+1
        if indx==len(oiL[0].subops): # at end
            assert len(oiL)==1
            return oiL[0],pAstL[:oiL[0].paramLen],U.prependGen(tok,toks)

def compiler(toks):
    doMCTcmd('operator "A.AstTuple" ["!!defaultOperand"]',None)
    doMCTcmd('operator "None" ["!!SOF"] () ["!!EOF"]',None)
    #opCtx = OpCtx(upOpCtx=None,indx=0,altOpInfos=[])
    e,toks = getExpr(toks=toks,left=None,prio=None,opCtx=None,noneOK=False)
    e.fixUp(parent=None,closure=None)
    return e

if __name__=="__main__":
    import lexer
    global ast
    ast = compiler(L.lexer("test.w"))
    print(ast)
