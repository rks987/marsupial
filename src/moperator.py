# operator.py

# build operator datastructure from operator commands
# support getExpr with operator related code

# We allow overlap between operators as long as they can be read from
# left to right: we don't have to go back and reparse what we've seen.
# Brackets are an example. We want 3 operators defined:
# %^operator ("[",None,"]") "..." ["["] ["]"]
# %^operator ("[","]") "..." ["["] () [" ",repeating] () ["]"]
# %^operator ("[","|","]") "..." ["["] () ["|"] () ["]"]

import collections as C
import utility as U
import mast as A
import re
import decimal

# we have 2 dicts, noLeft and withLeft. The same operator can appear in both.
# If the operator is only in withLeft, and it gets there with no left argument
# then defaultOperand is inserted: Unit.unit in wombat.
# For each operand we have a priority (if it is left, or if it might be the last
# right sop) or we have the next mandatory sop. We also hold the list of
# expected sops (ie optional or repeating sops up to and including the next
# mandatory one).
# Operators can be defined for " " and "". These come into play when a subop
# with no right is followed by an op with no left. " " can also be used as
# a proper subop, but "" (which occurs when lexer puts in a break, but there are
# no spaces) cannot.

# FIXME: there should be severe restrictions on what subops can be used in subsubs.
# Probably shouldn't allow any that are used (active?) in the parent(etc).

# Note, when a subop has subsubs then: (a) it must be in again as the first subsub,
# but set as mandatory (whatever it is at a higher level). The adjust ast in
# the subsub applies to the immediately following param, but the adjust param
# at the higher level applies to the subop combined with all the subsusbs
 
OpInfo = C.namedtuple('OpInfo','left,astFun,paramLen,subops') # if left!=None it has pos==0
 
SSparam = C.namedtuple('SSparam','precedence,pos,oneAdjust,ssParamLen,subsubs')
SSsubop = C.namedtuple('SSsubop',
                       'subop,occur,allAdjust,v')
                       # v a dict with param,nextMandatory,nextPossibles

noLeft = {}
withLeft = {}

# Really the keys should be based on text,tokenType pairs. This would require
# some interaction with the lexer. At the moment there is a danger of mistaking
# an atom or string for an operator by looking at the text and not checking
# the tokenType. FIXME (big job)
def getKeyTuple(subops):
    # the key is the mandatory subops, plus None added after subops with no param
    # However strip a trailing None, since can't have withRight and noRight variants
    kt0 = () # zero tuple
    if subops[0].occur=="mandatory":
        if subops[0].v['param']!=None: # funny place to put this check
            assert subops[0].v['param'].subsubs==None
        kt0 = (subops[0].subop,) # 1-tuple
        if len(subops)>1 and subops[0].v['param']==None:
            kt0 = (subops[0].subop,None)
    if len(subops)==1:
        return kt0
    else:
        return kt0+getKeyTuple(subops[1:]) # + is tuple concat

def getZeroOpInfo(whichDict,partkey): # usually just first
    if isinstance(whichDict[partkey],OpInfo):
        return whichDict[partkey]
    else:
        return whichDict[whichDict[partkey]][0] # return first

def subsubEqual(ss1,ss2):
    if ss1==ss2: return
    assert ss1.subop == ss2.subop
    assert ss1.occur == ss2.occur
    if ss1.v['param'] == None:
        assert ss2.v['param'] == None
    else:
        subsubEqual(ss1.v['param'].subsubs,ss2.v['param'].subsubs)
    subsubEqual(ss1[1:],ss2[1:])

def subOpCompat(so1,so2):
    assert len(so1)!=0 and len(so2)!=0 # would be overlap (and not got here)
    if so1[0].occur=="mandatory" and so2[0].occur=="mandatory":
        if so1[0].subop != so2[0].subop: # good distinguisher
            return # we are compat
        if so1[0].v['param']==None and so2[0].v['param']!=None:
            return # one has param, one doesn't, that distinguishes
        if so1[0].v['param']!=None and so2[0].v['param']==None:
            return # one has param, one doesn't, that distinguishes
        # else: # actually nothing to do - we will go deeper
    else: # if not both mandatory then they need to be the same, same subsubs
        assert so1[0].occur==so2[0].occur # equal and not mandatory
        assert so1[0].subop==so2[0].subop
        subsubEqual(so1[0].v['param'].subsubs,so2[0].v['param'].subsubs)
    subOpCompat(so1[1:],so2[1:])

def checkCompat(oi1,oi2): # 2 OpInfo
    if oi1.left!=None:
        assert oi2.left!=None and oi1.left.precedence==oi2.left.precedence
    else:
        assert oi2.left==None
    subOpCompat(oi1.subops,oi2.subops)

def insertOp(whichDict, opInfo):
    opKey = getKeyTuple(opInfo.subops)
    assert opKey not in whichDict # overlap
    whichDict[opKey] = opInfo
    if len(opKey)==1:
        whichDict[opKey[0]] = opInfo
        return
    # now we must work backwards, creating links and checking compatibility
    # We only need to check compatibility once, since existing operators
    # are compatible with each other.
    curKey = opKey[:-1]
    compatChecked = False
    while len(curKey)>0:
        if curKey not in whichDict: # can just put a point to ourself
            whichDict[curKey] = [opKey] # start a new list of opKeys
        else:
            assert not (whichDict[curKey] is OpInfo) # would be overlap
            # so we have a list of potential overlaps
            if not compatChecked: # check against first one
                checkCompat(whichDict[opKey],whichDict[whichDict[curKey][0]])
                compatChecked = True
            whichDict[curKey].append(opKey) # add ourselves to list
        if len(curKey)==1:
            whichDict[curKey[0]] = whichDict[curKey] # HACK
        curKey = curKey[:-1] # truncate

def mctlEval(s):
    if s==None: return None
    rslt = eval(s)
    assert rslt==None or callable(rslt) or isinstance(rslt,A.AstNode)
    return rslt

# operators are defined by enough mandatory subops (incl op).
# So the key is a list of subop strings. The value is a list of follow 
# on (mandatory) subops, and opInfo which is null when the list of follow ons
# has more than one entry.

# The opInfo entries have: This is WRONG FIXME
#  'opDefine' is the list of mandatory ops that define us
#  'allMandatory' is the complete list of top level mandatory
#  'left' is the operand spec, None if in noLeft
#  'right' is the sops which is the same format as subsubs, None if no right

sopSpecRE = re.compile(r'''
    (?: # we have subops in []s and params in ()s. This covers the [] case
        \[ 
            \s*(?P<subop>"(?:[^\\"]|\\.)*") # the subop is in "s
            (?:\s*(?P<occur>mandatory|optional|repeating))? # occur optional
            (?:\s*(?P<allAdjust>"(?:[^\\"]|\\.)+"))? # adjust optional
        \s*\] # maybe whitespace before ]
    ) | # end of [], alternativel ()
    (?: # here begins the (), parameter, case
        \s*\( 
            (?:\s*(?P<precedence>\d+\.?\d*))? # optional precedence
            (?:\s*(?P<oneAdjust>"(?:[^\\"]|\\.)+"))? # optional adjust
            (?:\s*(?P<FIXME>\W)(?P<subsubs>.+)(?P=FIXME))? # opt subsubs
        \s*\)
    ) 
    ''',re.VERBOSE)
def genSopSpec(fromRE):
    # should check there is no bad stuff: end of each should go with 
    # start of next FIXME
    pos = 0
    for mss in fromRE:
        #assert mss.group('badSpec')==None # should die FIXME
        if mss.group("subop"):
            assert mss[0][0]=='['
            occur = "mandatory"
            if mss.group("occur"): occur = mss.group("occur")
            yield SSsubop(subop=U.unquote(mss.group("subop")),
                          occur=occur,
                          allAdjust=mctlEval(U.unquote(mss.group("allAdjust"))),
                          v=dict(param=None,
                          nextMandatory=None,
                          nextPossibles=None)
                        ) # param will later be set to the next SSparam
        else:
            assert re.match(r'\s*\(',mss[0])!=None
            pT = mss.group("precedence")
            dummyLeft,subsubs,ssParamLen=getSopSpec(mss.group("subsubs"))
            yield SSparam(precedence=None if pT==None else decimal.Decimal(pT),
                          pos=pos,
                          oneAdjust=mctlEval(U.unquote(mss.group("oneAdjust"))),
                          ssParamLen=ssParamLen,
                          subsubs=subsubs)
            pos = pos+1

# ssPair takes a iter of sops and operands without repeating operands,
# and generates one yield per sop, with the operand set to None if no
# following operand.
def ssPair(sopAndParam):
    sop = next(sopAndParam,None)
    assert (sop!=None) and (type(sop) is SSsubop)
    while True:
        nxt = next(sopAndParam,None)
        if nxt!=None and type(nxt) is SSparam: # normal case
            sop.v['param'] = nxt
            #sop.v['pos'] = nxt.pos
            yield sop
            sop = next(sopAndParam,None)
            if sop==None: return
        elif nxt==None:
            sop.v['param'] = None
            yield sop
            return
        else: # 2 sops in a row
            sop.v['param'] = None
            yield sop
            sop = nxt

# for each position that you can be in within an operator, we need to
# know 2 things, so we calculate them here. They are: (1) the next 
# mandatory we'll come to within this operator, or the right precedence 
# if none; and (2) the list of all possible subops that might come up
# next (since these override operator declarations) [the last of these
# will be the next mandatory if there is one].
def getMandPoss(sopSpec,i,pLen):
    if i==len(sopSpec):
        return None,[],pLen # nextMandatory,possibles
    nextNextMan,nextPoss,pLen = getMandPoss(sopSpec,i+1,pLen)
    p = sopSpec[i].v['param']
    if p!=None: pLen = max(p.pos+1,pLen)
    if p!=None and p.subsubs: # have subsubs
        subNextMan,subPoss,ssParamLen = getMandPoss(p.subsubs,0,0) # hmm, doing twice
        sopSpec[i].v['nextMandatory'] = subNextMan if subNextMan!=None else nextNextMan
        #sopSpec[i].v['nextPossibles'] = subPoss + nextPoss
        sopSpec[i].v['nextPossibles'] = subPoss if subNextMan!=None else subPoss + nextPoss
    else:
        sopSpec[i].v['nextMandatory'] = nextNextMan
        sopSpec[i].v['nextPossibles'] = nextPoss
    if sopSpec[i].occur=='mandatory':
        return sopSpec[i].subop,[sopSpec[i].subop],pLen # just me
    else:
        return sopSpec[i].v['nextMandatory'], \
           [sopSpec[i].subop]+sopSpec[i].v['nextPossibles'],pLen


def getSopSpec(sopSpecText):
    if sopSpecText==None: return None,None,None # for subsubs only
    sopSpecUnpaired = [*genSopSpec(re.finditer(sopSpecRE,sopSpecText))]
    if sopSpecText[0]=='(': # never for subsub
        left = sopSpecUnpaired[0]
        sopSpec = [*ssPair(iter(sopSpecUnpaired[1:]))]
    else:
        left = None
        sopSpec = [*ssPair(iter(sopSpecUnpaired))]
    # now need to add to each parameter, the list of possible nextSop
    # and the next mandatory if there is no precedence.
    nextMandatory,possibles,pLen = getMandPoss(sopSpec,0,(1 if left!=None else 0))
    return left,sopSpec,pLen

def doOperatorCmd(astFun,sopSpecText):
    # op is the operator being defined = first sop
    # astFun is compile time code (python3) generating an AST for the procedure
    # sopSpec: see compiler.md
    left,sopSpec,pCnt = getSopSpec(sopSpecText)
    insertOp((withLeft if left else noLeft),
             OpInfo(left=left,astFun=mctlEval(astFun),paramLen=pCnt,subops=sopSpec))

# first2rest is a common allAdjust parameter, used where we put the first part
# of a tuple operand, then have the rest as a repeating operand.
def first2rest(tup):
    assert isinstance(tup,AstTuple)
    if len(tup.members)<2: return tup
    return AstTuple(members=[tup[0],*tup[1]]) # called be parent/closure set

if __name__=="__main__":
    #import lexer
    doOperatorCmd( "A.callOp", '(100) [" "] (100)')
    doOperatorCmd("A.zeroTuple",'["["] ["]"]')
    doOperatorCmd("A.zeroTuple",'["["] () [" " repeating] () ["]"]')
    doOperatorCmd("A.zeroTuple",'["["] () ["|"] () ["]"]')
    print(noLeft)

