# cttypes.py -- compile time types

import mhierarchy as H
import lenses as L
import collections as C
import mast as A
import mprimitive as P

# We treat base types as if families but with index set to None.
# so these are :Type, families are :IndxType=>Type

# The types and parameters are:
#    Decimal  (None)              type of numeric constant e.g. 3.14
#    Nat      (None)              unlimited positive integers
#    Tuple    (List Type)
#    Proc     (Tuple(Type,Type))  X=>Y
#    Union    (SemiSet Type)
#    SemiSet  (Type)
#    Option   (Type)              Option(X)=Union`[Unit Tuple(X)]
#    List     (Type)              List(X)=Option(Tuple[X List(X)])

# A lot of this should be separated out into a general types module

# For the moment a base type is just a family with index set to None
# Also Type itself has Mfamily None (should be Type in higher Universe)
# And all types/families are primitive

Mfamily = C.namedtuple('Mfamily','famObj,indxType')

# tMindx is None (for base type) or the value of type .tMfamily.indxType
MtVal = C.namedtuple('MtVal','tMfamily,tMindx,tMsubset') # a .value for types

def tNoSub(t):
    if t.tMsubset==None: return t
    return MtVal(t.tMfamily,t.tMindx,None)

# this doesn't look right when there are isA relations around. FIXME
#def typeEqual(t1,t2):
#    if t1.tMfamily != t2.tMfamily: return False
#    if not typeEqual(t1.tMindx,t2.tMindx): return False
#    return t1.tMsubset == t2.tMsubset

#class Mfamily: 
#    def __init__(self,famObj,indxType):
#        self.famObj = famObj # inverse pair gen/ungen this type
#        self.indxType = indxType # an Mval of the type of the param

# A value OR might be unknown with type saying what we do know.
# Note that if there is a value then the type indicates the format of
# the type, but isn't necessarily restricted (tMsubset) to just that value
# There have been places in the code that assumed that - hopefully all fixed.
Mval = C.namedtuple('Mval','mtVal,value') # mtVal is the type, an MtVal
#class Mval:
    #def __init__(self,family,indx,value=None):
        #self.family = family # an Mfamily
        #self.indx = indx # an Mval -- must be val if .value not None
        #self.value = value # set when has known value
    #def toType(self): # create equivalent MtVal
        #return MtVal(self.family,self.indx,[self.value] if self.value!=None else None)
def valToType(v): # v is an Mval
    valList = [v.value] if v.value != None else None
    return L.bind(v.mtVal).tMsubset.set(valList) # MtVal(v.mtVal.famObj,v.mtVal.indxType,[v.value])
def typeWithVal(t,v):
    return L.bind(t).tMsubset.set([v]) if v!=None else t
def typeToVal(t):
    return Mval(t,t.tMsubset[0] if t.tMsubset!=None else None)

# Note that types are values of type Type. So in mfList below, the 2nd
# parameter is mvType meaning that the List family of types is indexed
# by type. In mvListOfType the mvType in the 2nd parameter means that
# the specific Type that this is a list of, is Type.

# there is a type Type, whose values are types 
mfType = Mfamily(famObj=P.mType, indxType=None)
mvtType = MtVal(mfType,None,None)
mvType = Mval(mvtType,mvtType) # Type:Type (missing universe level FIXME)
# mvtType is a type, and other types belong to it, mvType is a specific value
mfList = Mfamily(P.mList,indxType=mvtType)
mvtListOfType = MtVal(mfList,mvType,None)
mfTuple = Mfamily(P.mTuple,mvtListOfType)

mfSet = Mfamily(P.mSet,mvtType)
#aSetOfNats = Mval(mfSet,mvDecimal,{Decimal(33),Decimal(77)})
mvtSetOfType = MtVal(mfSet,mvtType,None)
mfUnion = Mfamily(P.mUnion,mvtSetOfType)
#
mfDecimal = Mfamily(P.mDecimal,None)
mvtDecimal = MtVal(mfDecimal,None,None)
mfNat = Mfamily(P.mNat,None)
mvtNat = MtVal(mfNat,None,None)
mfAny = Mfamily(P.mAny,None)
mvtAny = MtVal(mfAny,None,None)
# ClosureType = Proc((Any,Any):Tuple([Any Any]:List(Type))
mvListTwoTypes = Mval(mvtListOfType,(mvType,mvType)) # [Type Type] : List Type 
mvtTupleTwoTypes = MtVal(mfTuple,mvListTwoTypes,None)
mvTupleTwoAnys = Mval(mvtTupleTwoTypes,(mvtAny,mvtAny)) # (Any,Any) : Tuple[Any Any]
mfProc = Mfamily(P.mProc,mvtTupleTwoTypes)
mvtProcAnyAny = MtVal(mfProc,mvTupleTwoAnys,None)
mvtClosureT = mvtProcAnyAny

def mvMakeDecimal(d):
    return Mval(mvtDecimal,d)

# statements : Tuple[Discard Any] => Any
mfDiscard = Mfamily(P.mDiscard,None)
mvtDiscard = MtVal(mfDiscard,None,None)
mvListDiscardAny = Mval(mvtListOfType,(mvtDiscard,mvtAny))
mvtTupleDiscardAny = MtVal(mfTuple,mvListDiscardAny,None)
mvListTupleDiscardAnyAndAny = Mval(mvtListOfType,(mvtTupleDiscardAny,mvtAny))
mvTstatements = MtVal(mfProc,mvListTupleDiscardAnyAndAny,None)
mVstatements = Mval(mvTstatements,P.wPstatements)

mVdiscard = Mval(mvtDiscard,P.mDiscard) # value of type Discard -- should it just be unit?

mfEmpty = Mfamily(P.mEmpty,None)
mvtEmpty = MtVal(mfEmpty,None,None)

# equal -- _X x _Y => Intersection[_X _Y] -- just Tuple[Any Any]=>Any for moment
mvListAnyAny = Mval(mvtListOfType,(mvtAny,mvtAny))
mvtTupleTwoAnys = MtVal(mfTuple,mvListAnyAny,None)
mvListTwoAnyAndAny = Mval(mvtListOfType,(mvtTupleTwoAnys,mvtAny))
mvTupleTwoAnyAndAny = Mval(MtVal(mfTuple,mvListTwoAnyAndAny,None),((mvtAny,mvtAny),mvtAny))
mvtProcTwoAnyToAny = MtVal(mfProc,mvTupleTwoAnyAndAny,None)
mvTequal = mvtProcTwoAnyToAny
mVequal = Mval(mvTequal,P.wPequal)

# casePswap -- _X x SemiSet(_X=>_Y) => _Y, but just Tuple[Any Set(Proc(Any,Any))]=>Any here
# CHECK THIS FIXME
mvListAnyClosureT = Mval(mvtListOfType,(mvtAny,mvtClosureT))
mvtTupleAnyClosureT = MtVal(mfTuple,mvListAnyClosureT,None)
mvListTupleAnyClosureTAndAny = Mval(mvtListOfType,(mvtTupleAnyClosureT,mvtAny))
mvtTupleTupleAnyClosureTAny = MtVal(mfTuple,mvListTupleAnyClosureTAndAny,None)
mvTupleTupleAnyClosureTAny = Mval(mvtTupleTupleAnyClosureTAny,(mvtAny,mvtTupleAnyClosureT))
mvTcasePswap = MtVal(mfProc,mvTupleTupleAnyClosureTAny,None)
mVcasePswap = Mval(mvTcasePswap,P.wPcasePswap)

# toType -- Any x t:Type => t (t is the Type parameter), but just Tuple[Any Type]=>Any here
# but the Mval will have the required type after
mvListAnyType = Mval(mvtListOfType,(mvtAny,mvtType))
mvtTupleAnyType = MtVal(mfTuple,mvListAnyType,None)
mvListTupleAnyTypeAny = Mval(mvtListOfType,(mvtTupleAnyType,mvtAny))
mvTupleTupleAnyTypeAny = Mval(MtVal(mfTuple,mvListTupleAnyTypeAny,None),((mvtAny,mvtType),mvtAny))
mvTtoType = MtVal(mfProc,mvTupleTupleAnyTypeAny,None)
mVtoType = Mval(mvTtoType,P.wPtoType)

# tuple2list -- Tuple[lt:List(Type)] => List(Union(lt)) // Any => Any
mvTtuple2list = MtVal(mfProc,mvTupleTwoAnys,None)
mVtuple2list = Mval(mvTtuple2list,P.wPtuple2list)

# greaterOrFail -- Nat x Nat => Nat
mvListTwoNats = Mval(mvtListOfType,(mvtNat,mvtNat))
mvtTupleTwoNats = MtVal(mfTuple,mvListTwoNats,None)
mvListTupleTwoNatsNat = Mval(mvtListOfType,(mvtTupleTwoNats,mvtNat))
mvtTupleTupleTwoNatsNat = MtVal(mfTuple,mvListTupleTwoNatsNat,None)
mvTupleTupleTwoNatsNat = Mval(mvtTupleTupleTwoNatsNat,((mvtNat,mvtNat),mvtNat))
mvTgreaterOrFail = MtVal(mfProc,mvTupleTupleTwoNatsNat,None)
mVgreaterOrFail = Mval(mvTgreaterOrFail,P.wPgreaterOrFail)

# starOp -- Nat x Nat => Nat
mvTstarOp = MtVal(mfProc,mvTupleTupleTwoNatsNat,None)
mVstarOp = Mval(mvTstarOp,P.wPstarOp)

# subtract -- Nat x Nat => Nat
mvTsubtract = MtVal(mfProc,mvTupleTupleTwoNatsNat,None)
mVsubtract = Mval(mvTsubtract,P.wPsubtract)

# print -- _X => _X
mvTprint = MtVal(mfProc,mvTupleTwoAnys,None)
mVprint = Mval(mvTprint,P.wPprint)


def unknownAny():
    return Mval(mfAny,None,None)

# the famAst will mostly be an identifier that is hacked for the moment
#
# 'Decimal'  Decimal
# 'Nat'      Int (? just a value)
# 'Tuple'    ptuple - include unit=0-tuple=() in python
# 'Proc'     EtClosure or ???
# 'Union'    mtype with value
# 'SemiSet'  ?? maybe just a ptuple?
# 'Option'   0 or 1 ptuple
# 'List'     ptuple
# 'Type'     (Mfamily,indx,restrict) # indx==None if Mfamily is base
             # restrict is None, or a list of values

# We also need some isA relations:
# Nat isA Decimal
# A isA B ==> List A isA List B
# Tuple lt1 isA Tuple lt2 whenever all (zip ...) etc
# etc

# This is wrong because an MtVal is immutable FIXME
def tupleFixUp(t): # t:MtVal
    assert t.tMfamily.famObj == P.mTuple
    # Only handle case where tMsubset has 1 element FIXME
    # t.tMindx is an MtVal for List(Type). So its tMsubset must have length 1
    tTypes = t.tMindx.tMsubset[0]
    if all (tt.value.tMsubset!=None for tt in tTypes):
        newtMsubset = [Mval(mfTuple,t.tMindx,tuple(tt.value.tMsubset[0] for tt in tTypes))]
        return True,L.bind(t).tMsubset.set(newtMsubset) # MtVal(t.tMfamily,t.tMindx,newtMsubset)
    return False,t

def vEqual(t,v1,v2): # check equality of .value for type t
    if v1==v2: return True
    if t in [mvtDecimal,mvtNat]: return v1==v2 # only False because of previus line
    # probably there aren't any Any values actually
    if t==mvtAny: return v1.mtVal==v2.mtVal and vEqual(v1.mtVal,v1.value,v2.value)
    if t.tMfamily==mfList: return len(v1)==len(v2) and all(vEqual(t.tMindx,v1[i],v2[i]) for i in len(v1))
    if t.tMfamily==mfTuple: # .tMindx is List Type
        return len(t.tMindx)==len(v1)==len(v2) and all(vEqual(t.tMindx[i],v1[i],v2[i]) for i in len(v1))
    assert False # don't think we need other cases yet FIXME

if __name__=="__main__":
    pass
