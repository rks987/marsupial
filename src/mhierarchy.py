# mhierarchy.py implements the marsupial isA hierarchy for compile time types

# When interpreting the AST we need to insert conversions based on isA relations (convertsTo
# not yet supported). As we interpret the types get more specific. Conversion only needs to
# happen when one end or the other becomes a value (I think). As the destination gets narrower
# we change the conversion.

import lenses as L
import cttypes as T
import decimal

def isABase(t1,t2): # returns up-down pair, or None
    assert t1.tMsubset == t2.tMsubset == None
    if t1==t2: return ( (lambda x: x), (lambda y: y))
    elif t1==T.mvtEmpty: return ( assertFalse, assertFalse )
    elif t2==T.mvtEmpty: return None
    elif t1==T.mvtNat and t2==T.mvtDecimal: return ( natToDecimal, decimalToNat)
    elif t1==T.mvtDecimal and t2==T.mvtNat: return None
    #elif t1==T.mvtDecimal: assert False #FIXME
    elif t1==T.mvtAny: return None
    elif t2==T.mvtAny: return ( toAny(t1), fromAny(t1))
    elif t1.tMfamily==T.mfList: # lists
        if t2.tMfamily!=T.mfList: return None
        assert t1.tMindx.tMsubset==None and t2.tMindx.tMsubset==None # else weird
        convpair = isABase(t1.tMindx,t2.tMindx)
        if convpair==None: return None
        return listTo(convpair[0]),listFrom(convpair[1])
    elif t1.tMfamily==T.mfTuple:
        if t2.tMfamily!=T.mfTuple or len(t1.tMindx)!=len(t2.tMindx): return None
        # tMindx is a List Type value (i.e. a pytuple of MtVal)
        isAs = tuple(isA(t1.tMindx[i],t2.tMindx[i]) for i in range(len(t1.tMindx)))
        if any(isAs[i]==None for i in range(len(isAs))): return None
        return (mtupleTo(tuple(isAs[i][0] for i in range(len(isAs)))),\
                   mtupleFrom(tuple(isAs[i][1] for i in range(len(isAs)))))
    elif t1.tMfamily==T.mfProc:
        if t2.tMfamily!=T.mfProc: return None
        pUpDown = isA(t2.tMindx[0],t1.tMindx[0])
        rUpDown = isA(t1.tMindx[1],t2.tMindx[1])
        if pUpDown==None or rUpDown==None: return None
        #assert False # we don't yet convert procedures, do we???
        return ( (lambda x: x), (lambda y: y)) # horrible HACK FIXME
        # FIXME A=>B isA X=>Y if X isA A and B isA Y -- then figure out convs
    else:
        assert False # I think that's all we need at the moment FIXME

def isA(t1,t2):
    updown = isABase(T.tNoSub(t1),T.tNoSub(t2))
    if updown==None: return None
    up,down = updown
    # if we get here, we have up,down linking t1,t2. Now sort out tMsubset.
    if t1.tMsubset!=None and t2.tMsubset!=None:
        assert len(t1.tMsubset)==1 and len(t2.tMsubset)==1 # current restriction FIXME
        if not T.vEqual(t2,up(t1.tMsubset[0]),t2.tMsubset[0]): return None
        assert T.vEqual(t1,t1.tMsubset[0],down(t2.tMsubset[0]))
    elif t1.tMsubset==None and t2.tMsubset!=None:
        return None # can't determine if t1 always lands on specific t2 -- unless unit??
    elif t1.tMsubset!=None and t2.tMsubset==None:
        # up will still work, need to change down
        return (up,downCheck(down,t1.tMsubset))
    return up,down

def downCheck(down,reqList):
    def checkv(v):
        r = down(v)
        if r not in reqList: return None
        return r
    return checkv

def isEqual(t1,t2):
    if t1==t2: return True
    if t1.tMfamily==t2.tMfamily==T.mfProc: return True # HORRIBLE HACK FIXME
    assert not (isA(t1,t2)!=None and isA(t2,t1)!=None) # expensive debug test FIXME
    return False # or should it be: (isA(t1,t2)!=None and isA(t2,t1)!=None)

# We convert to the intersection, then to the destination. Here are the non-Empty intersections
# NB Intersection is abbreviated I, `[...] is a (semi)set
# Nat           Decimal         Nat
# Tuple[T1...]  Tuple[T2...]    Tuple[I`[T1 T2]...]
# Union A       Union B         Union(I`[a b] where a in A and b in B)
# SemiSet T1    SemiSet T2      SemiSet (I `[T1 T2])
# other covariant: Option, List

# Get proper intersection when higher has a restriction and lower doesn't!!

# Note that intersection should return T.mvtEmty not None for empty intersection
# Then need to fix other code.

def intersection2Base(t1,t2): # 2 MtVal, not subset
    assert t1.tMsubset==None and t2.tMsubset==None
    #if t1==T.mvtEmpty or t2==T.mvtEmpty: return T.mvtEmpty # not needed
    isA12 = isABase(t1,t2)
    if isA12!=None: return t1
    isA21 = isABase(t2,t1)
    if isA21!=None: return t2
    if t1.tMfamily==T.mfTuple: # intersect componentwise
        if t2.tMfamily!=T.mfTuple or len(t1.tMindx)!=len(t2.tMindx): return T.mvtEmpty
        intsecs = tuple(intersection2Base(T.tNoSub(t1.tMindx[i]),T.tNoSub(t2.tMindx[i]))\
                for i in range(len(t1.tMindx)))
        if any(intsecs[i]==T.mvtEmpty for i in range(len(intsecs))): return T.mvtEmpty
        return T.MtVal(T.mfTuple,intsecs,None)
    return None #T.mvtEmpty # need to handle more complex cases FIXME

def intersection2(t1,t2):
    t1NS = T.tNoSub(t1)
    t2NS = T.tNoSub(t2)
    base = intersection2Base(t1NS,t2NS)
    if base==T.mvtEmpty: return T.mvtEmpty # shouldn't need this if isA works??
    # subsets must be converted to base and be equal there
    if t1.tMsubset==None and t2.tMsubset==None: return base
    updown1 = isA(base,t1NS)
    updown2 = isA(base,t2NS)
    if updown1==None or updown2==None: return T.mvtEmpty # val not in base
    if t1.tMsubset==None: # so t2.tMsubset!=None
        return T.typeWithVal(base,updown2[1](t2.tMsubset[0]))
    elif t2.tMsubset==None:
        return T.typeWithVal(base,updown1[1](t1.tMsubset[0]))
    else: # 2 values
        v2 = updown2[1](t2.tMsubset[0]) # possible base value
        v1 = updown1[1](t1.tMsubset[0])
        return T.mvtEmpty if not T.vEqual(base,v1,v2) else T.typeWithVal(base,v1)
        
def intersection3(t1,t2,t3):
    i2 = intersection2(t2,t3)
    if i2==None: return None
    return intersection2(t1,i2) # probably unwise

# unless one is less than other we return Any. FIXME
def union2(t1,t2):
    if isA(t1,t2)!=None: return t2
    if isA(t2,t1)!=None: return t1
    return T.mvtAny

def unionList(t):
    if len(t)==0: return T.mvtEmpty
    if len(t)==1: return t[0]
    r = union2(t[0],t[1])
    for i in range(3,len(t)): r = union2(r,t[i])
    return r

def conv(val,valType,reqType): # val's python type depends on valType
    intsec = intersection2(valType,reqType)
    if intsec==T.mvtEmpty: return None
    updown0 = isA(intsec,valType)
    updown1 = isA(intsec,reqType)
    assert updown0!=None and updown1!=None
    return updown1[0](updown0[1](val))

# isA procedures
def assertFalse(v): # for conversions that can't actually happen
    assert False

def natToDecimal(v):
    return decimal.Decimal(v)

def decimalToNat(v):
    rat = v.as_integer_ratio()
    if rat[1]!=1: return None
    return rat[0]

def listTo(conv):
    def vListTo(v): # v is a tuple of t1 = input of conv
        return tuple(conv(vs) for vs in v)
    return vListTo

def listFrom(conv):
    def vListFrom(v):
        rslt = tuple(conv(vs) for vs in v)
        if any(r==None for r in rslt): return None
        return rslt
    return vListFrom

def mtupleTo(convs): # this is a list of up conv
    def vMtupleTo(v):
        return tuple(convs[i](v[i]) for i in range(len(convs)))
    return vMtupleTo

def mtupleFrom(convs):
    def vMtupleFrom(v):
        rslt = tuple(convs[i](v[i]) for i in range(len(convs)))
        if any(r==None for r in rslt): return None
        return rslt
    return vMtupleFrom

def toAny(t1):
    # should memoize this FIXME
    def vToAny(v): # v will be value of type t1
        ##assert T.vEqual(t1,t1.tMsubset[0],v)
        return T.typeWithVal(t1,v) ##T.Mval(t1,v)
    return vToAny

def fromAny(t1):
    def vFromAny(v):
        # v is some mvtAny, so it is an MtVal will the value in the tMsubset
        conv(v.tMsubset[0],v,t1)
    return vFromAny
    #def vFromAny(v): # v is an Mval, can we get to t1?
    #    intersect = intersection2(v.mtVal,t1)
    #    convPair = isA(v.mtVal,t1) # try up
    #    if convPair==None:
    #        revPair = isA(t1,v.mtVal)
    #        if revPair==None: assert False # programmer error I think


if __name__=="__main__":
    pass
