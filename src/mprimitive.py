# primitive.py has the primitve values for the interpreter
#
# Note that parameters might come in from a lower type. This wouldn't
# matter if we were doing things properly and only using the properties
# since lower types will have all the higher types properties.
#
import cttypes as T
import mhierarchy as H
import lenses as L
#import combine

# TFam objects are the primitive parts of types or families of types
# tCode has to do with: (a) conversions; ???
# NB don't currently use this, nor do I know how I would.
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

def mEmptyCode(**kargs):
    pass
mEmpty = TFam(mEmptyCode)

# A PVrun object will get a series of (1 or more) parameter-result pairs.
# Each time it returns a parameter-result pair. The incoming pairs get
# smaller. The object can take advantage of that, or it can just recompute 
# each time. 
class PVrun: 
    def __init__(self,caller):
        self.caller = caller # a PrimitiveRun in interp.py
        self.pt = None # param type
        self.rt = None # result type
        self.txt = None
    def pTrT(self,pt,rt): # take parameter and result and return new ones
        assert False # must override

# statements -- Any x _X => _X
# The param should be a tuple -- assert that (??).
# The result and the 2nd component of param stay the same.
# We don't influence the first component.
# NB if rslt and 2nd param can't be unified then fail -- FIXME
class PvRstatements(PVrun):
    def __init__(self,caller):
        super().__init__(caller)
        self.txt='(;)'
    def pTrT(self,pt,rt):
        assert pt.tMfamily==T.mfTuple and len(pt.tMindx)==2
        self.rt = H.intersection2(pt.tMindx[1],rt)
        self.pt = L.bind(pt).tMindx[1].set(self.rt)
        ch,self.pt = T.tupleFixUp(self.pt)
        return self.pt,self.rt

# equal -- _X x _Y => Intersection[_X _Y]
# unify 2 params and result
# NB if rslt and/or params can't be unified then fail -- FIXME
class PvRequal(PVrun):
    def __init__(self,caller):
        super().__init__(caller)
        self.txt = '(=)'
    def pTrT(self,pt,rt):
        assert pt.tMfamily == T.mfTuple and len(pt.tMindx)==2
        self.rt = H.intersection3(pt.tMindx[0],pt.tMindx[1],rt)
        ch,self.pt = T.tupleFixUp(T.MtVal(T.mfTuple,(self.rt,self.rt),None))
        return self.pt,self.rt

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
        super().__init__(paramT,rsltT,caller)
        self.txt = '(case)'
        assert H.isA(paramT,T.mvtTupleAnyListProcAnyAny)
        self.cases = paramT.tMsubset[0][1]
        self.param4case = paramT.tMsubset[0][0]
    def run(self):
        self.caseControl = combine.caseP(self,self.cases,self.param4case,self.rsltT)
        return self
    def paramChanged(self,newType):
        assert False
    def rsltChanged(self,newType):
        assert False

# toType -- Any x t:Type => t (t is the Type parameter)
class PvRtoType(PVrun):
    def __init__(self,paramT,rsltT,caller):
        super().__init__(paramT,rsltT,caller)
        self.txt = '(:)'
    def run(self):
        assert False
        return self
    def paramChanged(self,newType):
        assert False
    def rsltChanged(self,newType):
        assert False

# tuple2list -- Tuple[lt:List(Type)] => List(Union(lt))
class PvRtuple2list(PVrun):
    def __init__(self,paramT,rsltT,caller):
        super().__init__(paramT,rsltT,caller)
        self.txt = '(t2l)'
    def run(self):
        assert False
        return self
    def paramChanged(self,newType):
        assert False
    def rsltChanged(self,newType):
        assert False

# greaterOrFail -- Nat x Nat => Nat
class PvRgreaterOrFail(PVrun):
    def __init__(self,paramT,rsltT,caller):
        super().__init__(paramT,rsltT,caller)
        self.txt = '(>?)'
    def run(self):
        assert False
        return self
    def paramChanged(self,newType):
        assert False
    def rsltChanged(self,newType):
        assert False

# starOp -- Nat x Nat => Nat
class PvRstarOp(PVrun):
    def __init__(self,paramT,rsltT,caller):
        super().__init__(paramT,rsltT,caller)
        self.txt = '(*)'
    def run(self):
        assert False
        return self
    def paramChanged(self,newType):
        assert False
    def rsltChanged(self,newType):
        assert False

# subtract -- Nat x Nat => Nat
class PvRsubtract(PVrun):
    def __init__(self,paramT,rsltT,caller):
        super().__init__(paramT,rsltT,caller)
        self.txt = '(-)'
    def run(self):
        assert False
        return self
    def paramChanged(self,newType):
        assert False
    def rsltChanged(self,newType):
        assert False

# print -- _X => _X
# We need a better system for interacting with the world, but for the
# moment this prints once, as soon as param=rslt gets set. We only know
# how to print Decimal.
class PvRprint(PVrun):
    def __init__(self,caller):
        super().__init__(caller)
        self.txt = '(p)'
        self.printed = False
    def pTrT(self,pt,rt):
        self.pt = self.rt = H.intersection2(pt,rt)
        self.tryPrint()
        return self.pt,self.rt
    def tryPrint(self):
        if self.printed: return
        if self.pt.tMsubset != None:
            assert len(self.pt.tMsubset)==1
            print(self.pt.tMsubset[0])
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
