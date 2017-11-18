# operator.py

# build operator datastructure from operator commands
# support getExpr with operator related code
import collections as C
import utility as U
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

noLeft = {}
withLeft = {}

# operators are defined by enough mandatory subops (incl op).
# So the key is a list of subop strings. The value is a list of follow 
# on (mandatory) subops, and opInfo which is null when the list of follow ons
# has more than one entry.

# The opInfo entries have:
#  'opDefine' is the list of mandatory ops that define us
#  'allMandatory' is the complete list of top level mandatory
#  'left' is the operand spec, None if in noLeft
#  'right' is the sops which is the same format as subsubs, None if no right

sopSpecRE = re.compile(r'(?:\[\w*(?P<subop>"(?:[^\\"]|\\.)+")\w+'+
                       r'(?:(?P<occur>mandatory|optional|repeating)\w+)?'+
                       r'(?P<allAdjust>"(?:[^\\"]|\\.)+")?\w*\]\w*)|'+
                       r'(?:\(\w*(?P<precedence>\d+\.?\d*)\w+)?'+
                       r'(?:(?P<oneAdjust>"(?:[^\\"]|\\.)+")\w+)?'+
                       r'\w*(?P<FIXME>\W)(?P<subsubs>.+)(?P=FIXME)\w*)|'+
                       r'(?P<badSpec>\W)')
 
SSparam = C.namedtuple('SSparam','precedence,oneAdjust,subsubs')
SSsubop = C.namedtuple('SSsubop',
                       'subop,occur,allAdjust,param,nextMandatory,nextPossibles')

def genSopSpec(fromRE):
    for mss in fromRE:
        assert mss.group('badSpec')==None # should die FIXME
        if mss.group("subop"):
            assert mss[0][0]=='['
            yield SSsubop(subop=U.unquote(mss.group("subop")),
                          occur=mss.group("occur") or "mandatory", #FIXME
                          allAdjust=U.unquote(mss.group("allAdjust")),
                          param=None) # param will later be set to the next SSparam
        else:
            assert mss[0][0]='('
            yield SSparam(precedence=decimal.Decimal(mss.group("precedence")),
                          oneAdjust=U.unquote(mss.group("oneAdjust")),
                          subsubs=getSopSpec(mss.group("subsubs")))

# ssPair takes a iter of sops and operands without repeating operands,
# and generates one yield per sop, with the operand set to None if no
# following operand.
def ssPair(sopAndParam):
    sop = next(sopAndParam,None)
    assert sop!=None and type(sop) is SSsubop
    while True:
        nxt = next(sopAndParam,None)
        if nxt!=None and type(nxt) is SSparam: # normal case
            sop.param = nxt
            yield sop
            sop = next(sopAndParam,None)
        elif nxt==None:
            sop.param = None
            yield sop
            return
        else: # 2 sops in a row
            sop.param = None
            yield sop
            sop = nxt

# for each position that you can be in within an operator, we need to
# know 2 things, so we calculate them here. They are: (1) the next 
# mandatory we'll come to within this operator, or the right precedence 
# if none; and (2) the list of all possible subops that might come up
# next (since these override operator declarations) [the last of these
# will be the next mandatory if there is one].
def getManPos(sopSpec,i):
    if i==len(sopSpec):
        return None,[] # nextMandatory,possibles
    nextNextMan,nextPoss = getManPos(sopSpec,i+1)
    p = sopSpec[i].param
    if p and p.subsubs: # have subsubs
        subNextMan,subPoss = getManPos(p.subsubs,0) # hmm, doing twice
        sopSpec[i].nextMandatory = subNextMan if subNextMan!=None else 
                                      nextNextMan
        sopSpec[i].nextPossibles = subPoss + nextPoss
    else:
        sopSpec[i].nextMandatory = nextNextMan
        sopSpec[i].nextPossibles = nextPoss
    if sopSpec[i].occur=='mandatory':
        return sopSpec[i].subop,[sopSpec[i].subop] # just me
    return sopSpec[i].nextMandatory,
           [sopSpec[i].subop]+sopSpec[i].nextPossibles


def getSopSpec(sopSpecText):
    if sopSpecText==None: return None # for subsubs only
    sopSpecUnpaired = [*genSopSpec(re.finditer(sopSpecRE,sopSpecText))]
    if sopSpecText[0]=='(': # never for subsub
        left = sopSpecUnpaired[0]
        sopSpec = [*ssPair(sopSpecUnpaired[1:])]
    else:
        left = None
        sopSpec = [*ssPair(sopSpecUnpaired)]
    # now need to add to each parameter, the list of possible nextSop
    # and the next mandatory if there is no precedence.
    nextMandatory,possibles = getManPos(sopSpec,0)
    return left,sopSpec

def doOperatorCmd(op,astGen,sopSpecText):
    # op is the operator being defined = first sop
    # astGen is compile time code (python3) generating an AST for the procedure
    # sopSpec: see compiler.md
    left,sopSpec = getSopSpec(sopSpecText)

