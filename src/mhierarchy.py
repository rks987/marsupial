# mhierarchy.py implements the marsupial isA hierarchy for compile time types

# When interpreting the AST we need to insert conversions based on isA relations (convertsTo
# not yet supported). As we interpret the types get more specific. Conversion only needs to
# happen when one end or the other becomes a value (I think). As the destination gets narrower
# we change the conversion.

import lenses as L
import cttypes as T
import decimal

def isA(t1,t2): # returns up-down pair, or None
    if t1==t2: up,down = ( (lambda x: x), (lambda y: y))
    #elif t1==T.mvtDiscard: assert False #return None # Discard is outside the hierarchy.
    #elif t2==T.mvtDiscard: assert False #return ( anyDiscard, None ) #  This is really a convertTo
    elif t1==T.mvtEmpty: return ( assertFalse, assertFalse )
    elif t2==T.mvtEmpty: return None
    elif t1==T.mvtNat and t2==T.mvtDecimal: up,down = ( natToDecimal, decimalToNat)
    elif t1==T.mvtDecimal and t2==T.mvtNat: return None
    #elif t1==T.mvtDecimal: assert False #FIXME
    elif t1==T.mvtAny: return None
    elif t2==T.mvtAny: # everything isA Any
        # for Any (and all Unions), the .value of an Mval is another Mval
        up,down = ( toAny(t1), fromAny(t1))
    elif t1.tMfamily==T.mfList: # lists
        if t2.tMfamily!=T.mfList: return None
        convpair = isA(t1.tMindx,t2.tMindx)
        if convpair==None: return None
        up,down = listTo(convpair[0]),listFrom(convpair[1])
    elif t1.tMfamily==T.mfTuple:
        if t2.tMfamily!=T.mfTuple or len(t1.tMindx)!=len(t2.tMindx): return None
        # tMindx is a List Type value (i.e. a pytuple of MtVal)
        isAs = tuple(isA(t1.tMindx[i],t2.tMindx[i]) for i in range(len(t1.tMindx)))
        if any(isAs[i]==None for i in range(len(isAs))): return None
        up,down = (mtupleTo(tuple(isAs[i][0] for i in range(len(isAs)))),\
                   mtupleFrom(tuple(isAs[i][1] for i in range(len(isAs)))))
    elif t1.tMfamily==T.mfProc:
        if t2.tMfamily!=T.mfProc: return None
        pUpDown = isA(t2.tMindx[0],t1.tMindx[0])
        rUpDown = isA(t1.tMindx[1],t2.tMindx[1])
        if pUpDown==None or rUpDown==None: return None
        up,down = ( (lambda x: x), (lambda y: y)) # horrible HACK FIXME
        #assert False # FIXME A=>B isA X=>Y if X isA A and B isA Y -- then figure out convs
    else:
        assert False # I think that's all we need at the moment FIXME
    # if we get here, we have up,down linking t1,t2. Now sort out tMsubset.
    if t1.tMsubset!=None and t2.tMsubset!=None:
        assert len(t1.tMsubset)==1 and len(t2.tMsubset)==1 # current restriction FIXME
        if not T.vEqual(t2,up(t1.tMsubset[0]),t2.tMsubset[0]): return None
        assert T.vEqual(t1,t1.tMsubset[0],down(t2.tMsubset[0]))
    elif t1.tMsubset==None and t2.tMsubset!=None:
        return None # can't determine if t1 always lands on specific t2 -- probably not possible
    elif t1.tMsubset!=None and t2.tMsubset==None:
        # up will still work, need to change down
        return (up,assertFalse) # hopefully don't need this (might need to return None) FIXME
    return up,down

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

def intersection2(t1,t2): # 2 MtVal
    if t1.tMsubset==None and t2.tMsubset==None:
        isA12 = isA(t1,t2)
        if isA12!=None:
            if isA12[1]!=None: return t1
            return None # convertsTo, so no intersection
        isA21 = isA(t2,t1)
        if isA21!=None:
            if isA21[1]!=None: return t2
            return None # converts wrong way
        assert False # need to handle more complex cases FIXME
    convs = isA(T.tNoSub(t1),T.tNoSub(t2))
    if convs==None: # try other way
        t1,t2 = t2,t1
        convs = isA(T.tNoSub(t1),T.tNoSub(t2))
    if convs==None: return None # hmm, should return mvtEmpty
    # t1 must be lower
    if t2.tMsubset==None: return t1
    # t2 has a subset, and we need to conv to t1 or fail
    newv = convs[1](t2.tMsubset[0])
    if newv==None: return None # mvtEmpty?
    if t1.tMsubset != None and not T.vEqual(t1,t1.tMsubset[0],newv): return None
    return L.bind(t1).tMsubset.set((newv,))

def intersection3(t1,t2,t3):
    i2 = intersection2(t2,t3)
    if i2==None: return None
    return intersection2(t1,i2) # probably unwise

# FIXME this hack probably only works in a forward calc
def conv(val,reqT): # val:Mval, reqT:MtVal
    intsec = intersection2(val.mtVal,reqT)
    updown0 = isA(intsec,val.mtVal)
    updown1 = isA(intsec,reqT)
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
        # if Union we just return v FIXME
        ##assert T.vEqual(t1,t1.tMsubset[0],v)
        return T.typeWithVal(t1,v) ##T.Mval(t1,v)
    return vToAny

def fromAny(t1):
    # There shouldn't be any Any values if interpreting (just use actual value) ????
    return (assertFalse,assertFalse)
    #def vFromAny(v): # v is an Mval, can we get to t1?
    #    intersect = intersection2(v.mtVal,t1)
    #    convPair = isA(v.mtVal,t1) # try up
    #    if convPair==None:
    #        revPair = isA(t1,v.mtVal)
    #        if revPair==None: assert False # programmer error I think


if __name__=="__main__":
    pass
