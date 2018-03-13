# primitive.py has the primitve values for the interpreter
#
#import cttypes as T

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

# Discard
def mDiscardCode(**kwargs):
    pass
mDiscard = TFam(mDiscardCode)

# statements -- Discard x _X => _X
def wPstatements(**kwargs):
    pass

# equal -- _X x _Y => Intersection[_X _Y]
def wPequal(**kwargs):
    pass

# casePswap -- _X x SemiSet(_X=>_Y) => _Y
def wPcasePswap(**kwargs):
    pass

# toType -- Any x t:Type => t (t is the Type parameter)
def wPtoType(**kwargs):
    pass

# tuple2list -- Tuple[lt:List(Type)] => List(Union(lt))
def wPtuple2list(**kwargs):
    pass

# greaterOrFail -- Nat x Nat => Nat
def wPgreaterOrFail(**kwargs):
    pass

# starOp -- Nat x Nat => Nat
def wPstarOp(**kwargs):
    pass

# subtract -- Nat x Nat => Nat
def wPsubtract(**kwargs):
    pass

# print -- _X => _X
def wPprint(**kwargs):
    pass

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
