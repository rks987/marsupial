# cttypes.py -- compile time types

import mast as A

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

class Mfamily: 
    def __init__(self,famAst,indxType):
        self.famAst = famAst # inverse pair gen/ungen this type
        self.indxType = indxType # an Mval of the type of the param, None if base

# A value OR might be unknown with type saying what we do know.
class Mval:
    def __init__(self,family,indx,value=None):
        self.family = family # an Mfamily
        self.indx = indx # an Mval -- must be val if .value not None
        self.value = None # set when has known value

# Note that types are values of type Type. So in mfList below, the 2nd
# parameter is mvType meaning that the List family of types is indexed
# by type. In mvListOfType the mvType in the 2nd parameter means that
# the specific Type that this is a list of, is Type.

# there is a type Type, whose values are types 
mfType = Mfamily(A.AstIdentifier('Type'),None)
mvType = Mval(mfType,None,(mfType,None,None)) # Type:Type (missing universe level FIXME)
mfList = Mfamily(A.AstIdentifier('List'),mvType)
#mvListTypeType = mtypeOrVal(mfList,mvTupleTypeType,(mfTuple,(mtvType,mtvType)))
#mtvList = mtypeOrVal(mfProc,mtvTuple)#??????
mvListOfType = Mval(mfList,mvType,(mfList,mvType,None))
mfTuple = Mfamily(A.AstIdentifier('Tuple'),mvListOfType)
#
mfDecimal = Mfamily(A.AstIdentifier('Decimal'),None)
mvDecimal = Mval(mfType,None,(mfDecimal,None,None))
mfNat = Mfamily(A.AstIdentifer('Nat'),None)
mvNat = Mval(mfType,None,(mfNat,None,None))
mfAny = Mfamily(A.AstIdentifier('Any'),None)
mvAny = Mval(mfType,None,(mfAny,None,None))

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

def tupleFixUp(t):
    pass # FIXME

#def constToVal(constAst):
#    assert isinstance(constAst,A.AstConstant)
#    if constAst.constType == 'Decimal':
#        v = mtype(
