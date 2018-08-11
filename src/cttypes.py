# cttypes.py -- compile time types

import mhierarchy as H
import lenses as L
import collections as C
import mast as A
import mprimitive as P
#import interp as I

# We treat base types as if families but with index set to None.
# so these are :Type, families are :IndxType=>Type

# The types and parameters are:
#    Decimal  (None)              type of numeric constant e.g. 3.14
#    Nat      (None)              unlimited positive integers
#    Tuple    (List Type)
#    Proc     (Tuple(Type,Type))  X=>Y
#    Union    (Set Type)
#    Set      (Type)
#    Option   (Type)              Option(X)=Union`[Unit Tuple(X)]
#    List     (Type)              List(X)=Option(Tuple[X List(X)])

# A lot of this should be separated out into a general types module

# For the moment a base type is just a family with index set to None
# And all types/families are primitive

Mfamily = C.namedtuple('Mfamily','txt,famObj,indxType')

# tMindx is None (for base type) or some value of type .tMfamily.indxType
MtVal = C.namedtuple('MtVal','tMfamily,tMindx,tMsubset') # a .value for types

# sometimes we want the type without any subset
def tNoSub(t):
    if t.tMsubset==None: return t
    return MtVal(t.tMfamily,t.tMindx,None)

# A value OR might be unknown with type saying what we do know.
# Note .tMindx and .value should not be of this form unless type is Any
Mval = C.namedtuple('Mval','mtVal,value') # mtVal is the type, an MtVal
Mprim = C.namedtuple('Mprim','txt,runner')

def ppT(x,xs):
    if x in xs:
        return "...."
    #if isinstance(x,I.Et):
    #    return type(x).__name__
    if isinstance(x,Mval):
        return ppT(x.mtVal,xs+(x,))+':'+ppT(x.value,xs+(x,))
    elif isinstance(x,Mfamily):
        return x.txt
    elif isinstance(x,MtVal):
        return ppT(x.tMfamily,xs+(x,))+'('+ppT(x.tMindx,xs+(x,))+')'+ \
                ("" if x.tMsubset==None else ('/'+ppT(x.tMsubset,xs+(x,))))
    elif isinstance(x,C.abc.Sequence):
        return '['+(','.join(ppT(xi,xs+(x,)) for xi in x))+']'
    elif isinstance(x,Mprim):
        return x.txt
    else: return str(x)

def valToType(v): # v is an Mval
    valList = (v.value,) if v.value != None else None
    return L.bind(v.mtVal).tMsubset.set(valList) # MtVal(v.mtVal.famObj,v.mtVal.indxType,(v.value,))
def typeWithVal(t,v):
    assert v==None or t.tMsubset==None or (len(t.tMsubset)==1 and T.vEqual(t,v,t.tMsubset[0]))
    return L.bind(t).tMsubset.set((v,)) if v!=None else t
def typeToVal(t):
    return Mval(t,t.tMsubset[0] if t.tMsubset!=None else None)

# Note that types are values of type Type. So in mfList below, the 2nd
# parameter is mvType meaning that the List family of types is indexed
# by type. In mvListOfType the mvType in the 2nd parameter means that
# the specific Type that this is a list of, is Type.

# there is a type Type, whose values are types 
mfType = Mfamily(txt='Type',famObj=P.mType, indxType=None)
mvtType = MtVal(mfType,None,None)
mvType = typeWithVal(mvtType,mvtType) # Type:Type (missing universe level FIXME)
# mvtType is a type, and other types belong to it, mvType is a specific value
mfList = Mfamily('List',P.mList,indxType=mvtType)
mvtListOfType = MtVal(mfList,mvtType,None)
mfTuple = Mfamily('Tuple',P.mTuple,mvtListOfType)

mfSet = Mfamily('Set',P.mSet,mvtType)
#aSetOfNats = Mval(mfSet,mvDecimal,{Decimal(33),Decimal(77)})
mvtSetOfType = MtVal(mfSet,mvtType,None)
mfUnion = Mfamily('Union',P.mUnion,mvtSetOfType)
#
mfDecimal = Mfamily('Decimal',P.mDecimal,None)
mvtDecimal = MtVal(mfDecimal,None,None)
mfNat = Mfamily('Nat',P.mNat,None)
mvtNat = MtVal(mfNat,None,None)
mVnat = typeWithVal(mvtType,mvtNat)
mfAny = Mfamily('Any',P.mAny,None)
mvtAny = MtVal(mfAny,None,None)
# ClosureType = Proc((Any,Any):Tuple([Any Any]:List(Type))
#mvListTwoTypes = Mval(mvtListOfType,(mvtType,mvtType)) # [Type Type] : List Type 
mvtTupleTwoTypes = MtVal(mfTuple,(mvtType,mvtType),None)
#mvTupleTwoAnys = Mval(mvtTupleTwoTypes,(mvtAny,mvtAny)) # (Any,Any) : Tuple[Any Any]
mfProc = Mfamily('Proc',P.mProc,mvtTupleTwoTypes)
mvtProcAnyAny = MtVal(mfProc,(mvtAny,mvtAny),None)
#mvtProcAnyAny = MtVal(mfProc,mvTupleTwoAnys,None)
mvtClosureT = mvtProcAnyAny

#mvListProcAnyAnyAndAny = Mval(mvtTupleTwoTypes,(mvtProcAnyAny,mvtAny))
mvtTupleProcAnyAnyAndAny = MtVal(mfTuple,(mvtProcAnyAny,mvtAny),None)
mvtGenProcParam = mvtTupleProcAnyAnyAndAny

def mvMakeDecimal(d):
    return Mval(typeWithVal(mvtDecimal,d),d)

## statements : Tuple[Discard Any] => Any
#mfDiscard = Mfamily(P.mDiscard,None)
#mvtDiscard = MtVal(mfDiscard,None,None)
#mvListDiscardAny = Mval(mvtListOfType,(mvtDiscard,mvtAny))
#mvtTupleDiscardAny = MtVal(mfTuple,mvListDiscardAny,None)
#mvListTupleDiscardAnyAndAny = Mval(mvtListOfType,(mvtTupleDiscardAny,mvtAny))
#mvTstatements = MtVal(mfProc,mvListTupleDiscardAnyAndAny,None)
#mVstatements = Mval(mvTstatements,P.PvRstatements)

#mVdiscard = Mval(mvtDiscard,P.mDiscard) # value of type Discard -- should it just be unit?

mfEmpty = Mfamily('Empty',P.mEmpty,None)
mvtEmpty = MtVal(mfEmpty,None,None)

# equal -- _X x _Y => Intersection[_X _Y] -- just Tuple[Any Any]=>Any for moment
#mvListAnyAny = Mval(mvtListOfType,(mvtAny,mvtAny))
mvtTupleTwoAnys = MtVal(mfTuple,(mvtAny,mvtAny),None)
#mvListTwoAnyAndAny = Mval(mvtListOfType,(mvtTupleTwoAnys,mvtAny))
#mvTupleTwoAnyAndAny = Mval(MtVal(mfTuple,mvListTwoAnyAndAny,None),((mvtAny,mvtAny),mvtAny))
mvtProcTwoAnyToAny = MtVal(mfProc,(mvtTupleTwoAnys,mvtAny),None)
mPequal = Mprim('(=)',P.PvRequal)
mvTequal = typeWithVal(mvtProcTwoAnyToAny,mPequal)
mVequal = Mval(mvTequal,mPequal)

# statements : Tuple[Any Any] => Any
mPstatements = Mprim('(;)',P.PvRstatements)
mvTstatements = typeWithVal(mvtProcTwoAnyToAny,mPstatements)
mVstatements = Mval(mvTstatements,mPstatements)

# casePswap -- _X x SemiSet(_X=>_Y) => _Y, but just Tuple[Any List(Proc(Any,Any))]=>Any here
# CHECK THIS FIXME
mvtListProcAnyAny = MtVal(mfList,mvtProcAnyAny,None)
mvtTupleAnyListProcAnyAny = MtVal(mfTuple,(mvtAny,mvtListProcAnyAny),None)
#mvtTupleTupleAnyListProcAnyAnyAndAny = MtVal(mfTuple,(mvtTupleAnyListProcAnyAny,mvtAny),None)
#mvtProc4casePswap = MtVal(mfProc,mvtTupleTupleAnyListProcAnyAnyAndAny,None)
#mvListAnyClosureT = Mval(mvtListOfType,(mvtAny,mvtClosureT))
#mvtTupleAnyClosureT = MtVal(mfTuple,mvListAnyClosureT,None)
#mvListTupleAnyClosureTAndAny = Mval(mvtListOfType,(mvtTupleAnyClosureT,mvtAny))
#mvtTupleTupleAnyClosureTAny = MtVal(mfTuple,mvListTupleAnyClosureTAndAny,None)
#mvTupleTupleAnyClosureTAny = Mval(mvtTupleTupleAnyClosureTAny,(mvtAny,mvtTupleAnyClosureT))
#mvTcasePswap = MtVal(mfProc,mvTupleTupleAnyClosureTAny,None)
mPcasePswap = Mprim('(case)',P.PvRcasePswap)
mvTcasePswap = MtVal(mfProc,(mvtTupleAnyListProcAnyAny,mvtAny),(mPcasePswap,))
mVcasePswap = Mval(mvTcasePswap,mPcasePswap)

# toType -- Any x t:Type => t (t is the Type parameter), but just Tuple[Any Type]=>Any here
# but the Mval will have the required type after
#mvListAnyType = Mval(mvtListOfType,(mvtAny,mvtType))
mvtTupleAnyType = MtVal(mfTuple,(mvtAny,mvtType),None)
#mvListTupleAnyTypeAny = Mval(mvtListOfType,(mvtTupleAnyType,mvtAny))
mvtTupleTupleAnyTypeAny = MtVal(mfTuple,(mvtTupleAnyType,mvtAny),None)
mPtoType = Mprim('(:)',P.PvRtoType)
mvTtoType = typeWithVal(mvtTupleTupleAnyTypeAny,mPtoType)
mVtoType = Mval(mvTtoType,mPtoType)

# tuple2list -- Tuple[lt:List(Type)] => List(Union(lt)) // Any => Any
mPtuple2list = Mprim('(t2l)',P.PvRtuple2list)
mvTtuple2list = MtVal(mfProc,(mvtAny,mvtAny),(mPtuple2list,))
mVtuple2list = Mval(mvTtuple2list,Mprim('(t2l)',mPtuple2list))

# greaterOrFail -- Nat x Nat => Nat
#mvListTwoNats = Mval(mvtListOfType,(mvtNat,mvtNat))
mvtTupleTwoNats = MtVal(mfTuple,(mvtNat,mvtNat),None)
#mvListTupleTwoNatsNat = Mval(mvtListOfType,(mvtTupleTwoNats,mvtNat))
#mvtTupleTupleTwoNatsNat = MtVal(mfTuple,mvListTupleTwoNatsNat,None)
#mvTupleTupleTwoNatsNat = Mval(mvtTupleTupleTwoNatsNat,((mvtNat,mvtNat),mvtNat))
mPgreaterOrFail = Mprim('(>?)',P.PvRgreaterOrFail)
mvTgreaterOrFail = MtVal(mfProc,(mvtTupleTwoNats,mvtNat),(mPgreaterOrFail,))
mVgreaterOrFail = Mval(mvTgreaterOrFail,mPgreaterOrFail)

# starOp -- Nat x Nat => Nat
mPstarOp = Mprim('(*)',P.PvRstarOp)
mvTstarOp = MtVal(mfProc,(mvtTupleTwoNats,mvtNat),(mPstarOp,))
mVstarOp = Mval(mvTstarOp,mPstarOp)

# subtract -- Nat x Nat => Nat
mPsubtract = Mprim('(-)',P.PvRsubtract)
mvTsubtract = MtVal(mfProc,(mvtTupleTwoNats,mvtNat),(mPsubtract,))
mVsubtract = Mval(mvTsubtract,mPsubtract)

# print -- _X => _X
mPprint = Mprim('(print)',P.PvRprint)
mvTprint = MtVal(mfProc,(mvtAny,mvtAny),(mPprint,))
mvTprintDecimal = MtVal(mfProc,(mvtDecimal,mvtDecimal),(mPprint,))
mVprint = Mval(mvTprint,mPprint)


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

#  an MtVal is immutable...
def tupleFixUp(t): # t:MtVal
    assert t.tMfamily.famObj == P.mTuple
    # Only handle case where tMsubset has 1 element FIXME
    # t.tMindx is an MVal for List(Type).
    tTypes = t.tMindx
    if all (tt.tMsubset!=None for tt in tTypes):
        newtMsubset = (tuple(tt.tMsubset[0] for tt in tTypes),)
        return True,L.bind(t).tMsubset.set(newtMsubset) # MtVal(t.tMfamily,t.tMindx,newtMsubset)
    return False,t

def vEqual(t,v1,v2): # check equality of .value for type t
    if v1==v2: return True
    if t in [mvtDecimal,mvtNat]: return v1==v2 # only False, because of previus line
    # probably there aren't any Any values actually
    if t==mvtAny: return v1.mtVal==v2.mtVal and vEqual(v1.mtVal,v1.value,v2.value)
    if t.tMfamily==mfList: 
        return len(v1)==len(v2) and all(vEqual(t.tMindx,v1[i],v2[i]) for i in len(v1))
    if t.tMfamily==mfTuple: # .tMindx is List Type
        return len(t.tMindx)==len(v1)==len(v2) and all(vEqual(t.tMindx[i],v1[i],v2[i]) 
                                                       for i in len(v1))
    assert False # don't think we need other cases yet FIXME

if __name__=="__main__":
    pass
