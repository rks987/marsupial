# primitive.py has the primitve values for the interpreter
#
# Note that parameters might come in from a lower type. This wouldn't
# matter if we were doing things properly and only using the properties
# since lower types will have all the higher types properties.
#
# TFam objects are the primitive parts of types or families of types
# tCode has to do with: (a) conversions; ???
# NB don't currently use this, nor do I know how I would.

import cttypes as T
import mhierarchy as H
import lenses as L
import interp as I
#import combine

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
# NB if rslt and 2nd param can't be unified then fail 
class PvRstatements(PVrun):
    def __init__(self,caller):
        super().__init__(caller)
        self.txt='(;)'
    def pTrT(self,pt,rt):
        assert pt.tMfamily==T.mfTuple and len(pt.tMindx)==2
        if pt.tMindx[0]==T.mvtEmpty: return T.mvtAny,T.mvtEmpty # fail
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
        self.rt = H.intersectionList([pt.tMindx[0],pt.tMindx[1],rt])
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
#NOTE this is a temp version doing firstCase 
class PvRcasePswap(PVrun):
    def __init__(self,caller):
        super().__init__(caller)
        self.txt = '(case)'
        self.cases = None
        self.param4case = None
    def pTrT(self,pt,rt):
        assert pt.tMfamily == T.mfTuple and len(pt.tMindx)==2
        #if pt.tMsubset==None: return pt,rt # we could do a bit more than this??
        cases = pt.tMindx[1].tMsubset[0]
        p4c = pt.tMindx[0]
        if p4c.tMsubset==None and rt.tMsubset==None: return pt,rt
        pts = [None]*len(cases)
        rts = [None]*len(cases)
        for i in range(len(cases)):
            #assert isinstance(cases[i],I.EtClosure) # don't allow primitive FIXME
            cr = I.ClosureRun(None,cases[i]) # I don't think callEt param is used????
            didSomething,pts[i],rts[i] = cr.changePR(p4c,rt)
        # Now we have possible params and results, we put together
        # The parameters we are consistent with is the Union of pts, results is Union of rts
        return L.bind(pt).tMindx[0].set(H.intersectionList(pts)),H.unionList(rts) # tupleFixUp?FIXME

        # our input must be the lowest (intersection) of all cases inputs.
        # The output must be the union of all outputs, intersected with required type.
        # For the moment we'll just set it to rt and see FIXME

# toType -- Any x t:Type => t (t is the Type parameter)
class PvRtoType(PVrun):
    def __init__(self,caller):
        super().__init__(caller)
        self.txt = '(:)'
    def pTrT(self,pt,rt):
        assert pt.tMfamily == T.mfTuple and len(pt.tMindx)==2
        if pt.tMindx[1].tMsubset==rt.tMsubset==None: return pt,rt
        assert pt.tMindx[1].tMfamily==T.mfType and len(pt.tMindx[1].tMsubset)==1
        reqT = pt.tMindx[1].tMsubset[0]
        irt = H.intersectionList([pt.tMindx[0],reqT,rt]) # irt must have the value ?!?
        return T.tupleFixUp(L.bind(pt).tMindx[0].set(irt))[1], T.fixIfTuple(irt)
        #if pt.tMindx[0].tMsubset!=None:
        #    nv = H.conv(pt.tMindx[0].tMsubset[0],pt.tMindx[0],irt)
        #    irtWithVal = T.typeWithVal(irt,val)
        #    return L.bind(pt).tMindx[0].set(irtWithVal), irtWithVal
        ## if here then rt has a val but pt doesn't, and we go backwards
        #nv = H.conv(irt.tMsubset[0],irt,pt.tMindx[0])

# isType -- Any x t:Type => t (t is the Type parameter)
class PvRisType(PVrun):
    def __init__(self,caller):
        super().__init__(caller)
        self.txt = '(::)'
    def pTrT(self,pt,rt):
        assert pt.tMfamily == T.mfTuple and len(pt.tMindx)==2
        if pt.tMindx[1].tMsubset==None: return pt,rt
        assert pt.tMindx[1].tMfamily==T.mfType and len(pt.tMindx[1].tMsubset)==1
        reqT = pt.tMindx[1].tMsubset[0]
        updown = H.isA(pt.tMindx[0],reqT)
        if updown==None:
            assert pt.tMindx[0].tMsubset==None
            r = L.bind(pt).tMindx[0].set(reqT)
        else:
            if pt.tMindx[0].tMsubset==None:
                r = L.bind(pt).tMindx[0].set(reqT)
            else:
                up,down = updown
                val = up(pt.tMindx[0].tMsubset[0])
                r = L.bind(pt).tMindx[0].set(T.typeWithVal(reqT,val))
                r = T.tupleFixUp(r)[1]
        return r, r.tMindx[0]

# tuple2list -- Tuple[lt:List(Type)] => List(Union(lt))
class PvRtuple2list(PVrun): # this only needs to run forwards
    def __init__(self,caller):
        super().__init__(caller)
        self.txt = '(t2l)'
    def pTrT(self,pt,rt): # 
        assert pt.tMfamily==T.mfTuple #and rt.tMfamily==T.mfList
        # we cheat and only work if all elements same base type
        t = T.tNoSub(pt.tMindx[0]) # first and only type
        assert all(H.isA(tt,t)!=None for tt in pt.tMindx)
        if pt.tMsubset==None: return pt,T.MtVal(T.mfList,t,None)
        return pt,\
               T.MtVal(T.mfList,t,tuple((conv(pt.tMsubset[0][i],pt.tMindx[i],t)\
                                         for i in range(len(pt.tMindx)))))

# consTuple2list -- (hd,(t1,t2,...) --> [hd t1 t2 ...] -- operasator support
class PvRconsTuple2list(PVrun): # this only needs to run forwards
    def __init__(self,caller):
        super().__init__(caller)
        self.txt = '(ct2l)'
    def pTrT(self,pt,rt): 
        if pt.tMsubset==None: return pt,rt
        assert pt.tMfamily==T.mfTuple
        # we cheat and only work if all elements same base type
        hd = pt.tMindx[0] # first type is in hd
        tl = pt.tMindx[1] # an mfTuple with 0 or more members
        t = T.tNoSub(hd) # first and only type
        for tt in tl.tMindx: t = H.union2(t,T.tNoSub(tt))
        return pt,\
               T.MtVal(T.mfList,t,(((H.conv(hd.tMsubset[0],hd,t),)+\
               tuple((H.conv(tl.tMindx[i].tMsubset[0],tl.tMindx[i],t)\
                                         for i in range(len(tl.tMindx))))),))

# geOrFail -- Nat x Nat => Nat
class PvRgeOrFail(PVrun):
    def __init__(self,caller):
        super().__init__(caller)
        self.txt = '(>?)'
    def pTrT(self,pt,rt):
        assert pt.tMfamily == T.mfTuple and len(pt.tMindx)==2
        leftT = H.intersection2(T.mvtNat,pt.tMindx[0])
        rightT = H.intersection2(T.mvtNat,pt.tMindx[1])
        grofT = H.intersection2(T.mvtNat,rt) # mvtEmpty if fail
        if grofT==T.mvtEmpty or leftT==T.mvtEmpty or rightT==T.mvtEmpty:
            return T.mvtAny,T.mvtEmpty
        left = leftT.tMsubset[0] if leftT.tMsubset!=None else None
        right = rightT.tMsubset[0] if rightT.tMsubset!=None else None
        grof = grofT.tMsubset[0] if grofT.tMsubset!=None else None
        if left!=None and right!=None:
            if grof!=None and grof!=left: return T.mvtAny,T.mvtEmpty
            if left>=right:
                grof = left
            else:
                return T.mvtAny,T.mvtEmpty
                #grofT=T.mvtEmpty # which isA Nat
        elif left!=None and grof!=None: # and right==None
            if grof!=left: return T.mvtEmpty,T.mvtEmpty
            return T.MtVal(T.mfTuple,(leftT,rightT),None), grofT
        elif right!=None and grof!=None: # and left==None
            left = grof
            if left<right: return T.mvtAny,T.mvtEmpty
        else:
            return T.MtVal(T.mfTuple,(leftT,rightT),None), grofT
        # left, right and grofT defined, maybe grof
        return T.tupleFixUp(T.MtVal(T.mfTuple,(leftT,rightT),((left,right),)))[1],\
               T.typeWithVal(T.mvtNat,grof)

# starOp -- Nat x Nat => Nat
class PvRstarOp(PVrun):
    def __init__(self,caller):
        super().__init__(caller)
        self.txt = '(*)'
    def pTrT(self,pt,rt):
        assert pt.tMfamily == T.mfTuple and len(pt.tMindx)==2
        leftT = H.intersection2(T.mvtNat,pt.tMindx[0])
        rightT = H.intersection2(T.mvtNat,pt.tMindx[1])
        prodT = H.intersection2(T.mvtNat,rt)
        left = leftT.tMsubset[0] if leftT.tMsubset!=None else None
        right = rightT.tMsubset[0] if rightT.tMsubset!=None else None
        prod = prodT.tMsubset[0] if prodT.tMsubset!=None else None
        if left!=None and right!=None:
            if prod!=None: assert prod==left*right
            prod = left*right
        elif left!=None and prod!=None: # and right==None
            if left==0: return T.mvtAny,T.mvtEmpty
            right = prod//left
        elif right!=None and prod!=None: # and left==None
            if right==0: return T.mvtAny,T.mvtEmpty
            left = prod//right
        else:
            return T.MtVal(T.mfTuple,(leftT,rightT),None), prodT
        if prod!=left*right: return T.mvtAny,T.mvtEmpty
        return T.tupleFixUp(T.MtVal(T.mfTuple,(leftT,rightT),((left,right),)))[1],\
               T.typeWithVal(T.mvtNat,prod)

# subtract -- Nat x Nat => Nat
class PvRsubtract(PVrun):
    def __init__(self,caller):
        super().__init__(caller)
        self.txt = '(-)'
    def pTrT(self,pt,rt):
        assert pt.tMfamily == T.mfTuple and len(pt.tMindx)==2
        leftT = H.intersection2(T.mvtNat,pt.tMindx[0])
        rightT = H.intersection2(T.mvtNat,pt.tMindx[1])
        diffT = H.intersection2(T.mvtNat,rt)
        left = leftT.tMsubset[0] if leftT.tMsubset!=None else None
        right = rightT.tMsubset[0] if rightT.tMsubset!=None else None
        diff = diffT.tMsubset[0] if diffT.tMsubset!=None else None
        if left!=None and right!=None:
            if diff!=None: assert diff==left-right
            diff = left-right
        elif left!=None and diff!=None: # and right==None
            right = left-diff
        elif right!=None and diff!=None: # and left==None
            left = right+diff
        else:
            return T.MtVal(T.mfTuple,(leftT,rightT),None), diffT
        if diff<0: return T.mvtAny,T.mvtEmpty # Nat has no negative
        return T.tupleFixUp(T.MtVal(T.mfTuple,(leftT,rightT),((left,right),)))[1],\
               T.typeWithVal(T.mvtNat,diff)

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
