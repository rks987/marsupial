# primitive.py has the primitve values for the interpreter
#
#import cttypes as T
import mhierarchy as H
#import combine

# TFam objects are the primitive parts of types or families of types
# tCode has to do with: (a) conversions; ???
class TFam:
    def __init__(self,tCode):
        assert callable(tCode)
        self.tCode = tCode

# Type
def mTypeCode(**kwargs):
    pass
mType = TFam(mTypeCode)

# Proc
def mProcCode(**kwargs):
    pass
mProc = TFam(mProcCode)

# Any
def mAnyCode(**kwargs):
    pass
mAny = TFam(mAnyCode)

## Discard
#def mDiscardCode(**kwargs):
#    pass
#mDiscard = TFam(mDiscardCode)

def mEmptyCode(**kargs):
    pass
mEmpty = TFam(mEmptyCode)

# The following take paramT=pt,rsltT=rt,caller=primRunner params
# and generate and return a PVrun object that responds to rsltChange and
# paramChange messages and also generates messages to caller from procedures
# controlled.

class PVrun:
    def __init__(self,paramT,rsltT,caller):
        #self.owner = owner
        self.paramT = paramT
        selt.rsltT = rsltT
        self.caller = caller
    def run(self): # commonly used default
        return self
    def paramChanged(self,newType):
        assert False # must override
    def rsltChanged(self,newType):
        assert False # must override

# statements -- Any x _X => _X
# The param should be a tuple -- assert that (??).
# The result and the 2nd component of param stay the same.
# We don't influence the first component.
# NB if rslt and 2nd param can't be unified then fail -- FIXME
class PvRstatements(PVrun):
    def __init__(self,paramT,rsltT,caller):
        super().__init__(self,paramT,rsltT,caller)
        assert paramT.tMfamily == mfTuple and len(paramT.tMindx)==2
        pCh,rCh = self.unifyP1R(False,False)
        #if pCh: self.caller.paramChanged(self.paramT)
        #if rCh: self.caller.rsltChanged(self.rsltT)
    def paramChanged(self,newType):
        pCh,rCh = unifyP1R(True,False)
        if pCh: return self.paramT
    def rsltChanged(self,newType):
        pCh,rCh = self.unifyP1R(False,True)
        if rCh: return self.rsltT
    def unifyP1R(self,isP,isR):
        # here is the logic of statements, which is just that the result is 2nd param
        intersect = H.intersection2(self.paramT.tMindx[1],self.rsltT)
        if intersect==None or intersect==T.mvtEmpty: raise mFail # fail
        pCh = rCh = False
        if not H.isEqual(intersect,self.paramT):
            self.paramT = intersect
            if not isP: self.caller.paramChanged(self.paramT)
            pCh = True
        if not H.isEqual(intersect,self.rsltT):
            self.rsltT = intersect
            if not isR: self.caller.rsltChanged(self.rsltT)
            rCh = True
        return pCh,rCh

# equal -- _X x _Y => Intersection[_X _Y]
# unify 2 params and result
# NB if rslt and/or params can't be unified then fail -- FIXME
class PvRequal(PVrun):
    def __init__(self,paramT,rsltT,caller):
        super().__init__(self,paramT,rsltT,caller)
        assert paramT.tMfamily == mfTuple and len(paramT.tMindx)==2
        self.unifyPPR(False,False)
    def paramChanged(self,newType):
        pCh,rCh = self.unifyPPR(True,False)
        if pCh: return self.paramT
    def rsltChanged(self,newType):
        pCh,rCh = self.unifyPPR(False,True)
        if rCh: return self.rsltT
    def unifyPPR(self,isP,isR):
        intersect = H.intersection3(self.paramT.tMindx[0],self.paramT.tMindx[1],self.rsltT)
        if intersect==None or intersect==T.mvtEmpty: raise mFail # fail
        if not H.isEqual(intersect,self.paramT.tMindx[0]) or \
                not H.isEqual(intersect,self.paramT.tMindx[1]):
                    self.paramT = T.MtVal(mfTuple,(intersect,intersect), \
                            None if intersect.tMsubset==None else \
                               [(intersect.tMsubset[0],intersect.tMsubset[0])]) 
                    if not isP: self.caller.paramChanged(self.paramT)
                    pCh = True
        if not H.isEqual(intersect,self.rsltT):
            self.rsltT = intersect
            if not isR: self.caller.rsltChanged(self.rsltT)
            rCh = True
        return pCh,rCh

# casePswap -- _X x SemiSet(_X=>_Y) => _Y
# This looks hard... We won't try to cope with changes to the 2nd parameter!
# We fire off the procedures with our param and rslt. We fake being closure
# and closureRun. When rslt or param changes then we restart all procs that
# haven't failed yet. This includes when any of our procs succeeds (which must
# change param or rslt. If all fail or inconsistent results (same thing) then
# we fail.
# Hmm, maybe not so hard. To restart (no side-effects) just ignore current Et
# and start a new one from scratch.
class PvRcasePswap(PVrun):
    def __init__(self,paramT,rsltT,caller):
        super().__init__(self,paramT,rsltT,caller)
        assert H.isA(paramT,T.mvtTupleAnyListProcAnyAny)
        self.cases = paramT.tMsubset[0][1]
        self.param4case = paramT.tMsubset[0][0]
    def run(self):
        self.caseControl = combine.caseP(self,self.cases,self.param4case,self.rsltT)
    def paramChanged(self,newType):
        assert False
    def rsltChanged(self,newType):
        assert False

# toType -- Any x t:Type => t (t is the Type parameter)
class PvRtoType(PVrun):
    def __init__(self,paramT,rsltT,caller):
        super().__init__(self,paramT,rsltT,caller)
    def paramChanged(self,newType):
        assert False
    def rsltChanged(self,newType):
        assert False

# tuple2list -- Tuple[lt:List(Type)] => List(Union(lt))
class PvRtuple2list(PVrun):
    def __init__(self,paramT,rsltT,caller):
        super().__init__(self,paramT,rsltT,caller)
    def paramChanged(self,newType):
        assert False
    def rsltChanged(self,newType):
        assert False

# greaterOrFail -- Nat x Nat => Nat
class PvRgreaterOrFail(PVrun):
    def __init__(self,paramT,rsltT,caller):
        super().__init__(self,paramT,rsltT,caller)
    def paramChanged(self,newType):
        assert False
    def rsltChanged(self,newType):
        assert False

# starOp -- Nat x Nat => Nat
class PvRstarOp(PVrun):
    def __init__(self,paramT,rsltT,caller):
        super().__init__(self,paramT,rsltT,caller)
    def paramChanged(self,newType):
        assert False
    def rsltChanged(self,newType):
        assert False

# subtract -- Nat x Nat => Nat
class PvRsubtract(PVrun):
    def __init__(self,paramT,rsltT,caller):
        super().__init__(self,paramT,rsltT,caller)
    def paramChanged(self,newType):
        assert False
    def rsltChanged(self,newType):
        assert False

# print -- _X => _X
# We need a better system for interacting with the world, but for the
# moment this prints once, as soon as param=rslt gets set. We only know
# how to print Decimal.
class PvRprint(PVrun):
    def __init__(self,paramT,rsltT,caller):
        super().__init__(self,paramT,rsltT,caller)
        self.printed = False
        self.tryPrint()
    def paramChanged(self,newType):
        self.paramT = H.intersection2(self.paramT,newType)
        self.tryPrint()
    def rsltChanged(self,newType):
        self.rsltT = H.intersection2(self.rsltT,newType)
        self.tryPrint()
    def tryPrint(self):
        if self.printed: return
        self.paramT = self.rsltT = H.intersection2(self.paramT,self.rsltT)
        if self.paramT.tMsubset != None:
            assert len(self.paramT.tMsubset)==1
            print(self.paramT.tMsubset[0])
            self.printed = True

# Decimal
def mDecimalCode(**kwargs):
    pass
mDecimal = TFam(mDecimalCode)

# Nat
def mNatCode(**kwargs):
    pass
mNat = TFam(mNatCode)

# Tuple
def mTupleCode(**kwargs):
    pass
mTuple = TFam(mTupleCode)

# List
def mListCode(**kwargs):
    pass
mList = TFam(mListCode)

# Union
def mUnionCode(**kwargs):
    pass
mUnion = TFam(mUnionCode)

# Set
def mSetCode(**kwargs):
    pass
mSet = TFam(mSetCode)

if __name__=="__main__":
    pass
