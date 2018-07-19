# interp.py is a debugging step, to make sure we understand how execution works.

# [[Rewriten so that there is less use of values, mostly only types.
# A value is just a type restricted to a single value. In a wildly optimistic
# way, I see this as a step towards a language where we are interested in types as
# spaces and the arrows linking them, while often avoiding getting down and
# dirty and looking at actual values within those types.]]

# Execution is easy (???). We create an execution tree where at each point
# the up result is unified with the calculation. Tuples do it in parallel.
# A call creates a new execution node.
#
# Since there are no primitive types or operations in the interpreter, we are
# restricted to compile-time types, and identifiers which aren't actually
# defined are interpreted here.

# The Et have to send messages to each other. Logically these can only be about types.
# I.e. when an Et finds out that its type is narrower than it previously thought
# it should let its neighbors know. Of course the most exact thing it can know is
# that it has a certain specific value. (i.e. tMsubset has length 1)
#
# Primitive procedures each have their own way of handling this stuff. Consider = (equal):
# It expects a 2-tuple of Ets. It unifies each, and the result (though that is often Any).
# Whenever it gets an improved type from one of the 3 it passes it to the other 2, so
# they stay in sync.
#
# Or consider tuple creation (AstTuple in the ast). The first thing (as always) is
# whether the required result is compatible with the tuple of the given size. Then
# We tell the rslt guy that we have a Tuple[Any Any Any] (say)

# There are situations (particularly the case/combine) where we want to execute some
# code, but only accept the effects if it succeeds. The way we do this is with shadow Et.
# If the shadow field is set then it points to a (closer to) real version of the Et.
# Parents and children will be initially set to None. When we want to send a message to
# them, then we find the real one by following the shadow link, and we create a new
# shadow of that, and send the message to that shadow. When we decide to accept the
# shadow calculation we just move the shadows to the real (or at least up a shadow level).
# To unshadow we unshadow connected stuff to our new level, then:
# If the shadowLevel>0 but shadowing is None, then we can unshadow by reducing
# shadowLevel and unshadowing connected stuff, and returning self. If shadowing does 
# point to something then we fix that and return it.

import lenses as L
import mast as A
import cttypes as T
import mhierarchy as H
import collections as C
import decimal as D

# The execution tree follows the ast tree. The rslt is the parent et that we are
# unifying with.
# When we get a message (like fromChild or fromParent) that narrows down our type
# then we should actually narrow it to the intersection, and if that is different
# from the modification we should let the caller know (by returning the new value).
#
# Note that ast and type and values are immutable, but Et aren't.
class Et:
    def __init__(self,shadowing,shadowLevel,ast,up,myChildId,closR):
        self.shadowing = shadowing
        self.shadowLevel = shadowLevel
        self.ast = ast
        self.up = up # parent Et
        self.myChildId = myChildId
        self.closR = closR # ClosureRun context
        self.curType = shadowing.curType if shadowing!=None else T.mvtAny # :T.MtVal
    def pp(self):
        if self.shadowing!=None:
            return str(self.shadowlevel)+'|'+self.shadowing.pp()+'|'
        return ('<'+T.ppT(self.curType)+'>')
    def run(self,rsltT):
        # will create children, send them updates, receive updates from them
        assert False # must be overridden
    def fromChild(self,childId,newType):
        assert False # to be overridden -- children know their id.
        # return intersection type if different from newType, else None
    def fromParent(self,newType): # curType/newType are T.MtVal
        # parent tells us our improved partial value
        # This default is ok if we don't have to tell our children about it
        self.curType = H.intersection2(self.curType,newType)
        return None if H.isEqual(newType, self.curType) else self.curType
    def shadow(self,level): # default ok for Et with no children ???
        if level==self.shadowLevel: 
            return self
        assert level>self.shadowLevel
        return type(self)(shadowing=self,shadowlLevel=level,ast=self.ast,up=None,\
                myChildId=self.myChildId,closR=None)

# utility routine for newType notifications like fromChild
def gotNewType(newType,curType): # return new curType, result to return, result to send up/down or None
    if H.isA(newType,curType)==None and not H.isEqual(newType,curType): print('!') # ??? FIXME
    newCur = H.intersection2(newType,curType)
    sendNew = None if H.isEqual(newCur,curType) else newCur
    returnNew = None if H.isEqual(newType,newCur) else newCur
    return newCur, returnNew, sendNew

class EtTuple(Et):
    def __init__(self,shadowing,shadowLevel,ast,up,myChildId,closR):
        super().__init__(shadowing,shadowLevel,ast,up,myChildId,closR)
        assert isinstance(ast,A.AstTuple)
        self.members = None # filled in below
    def pp(self):
        if self.shadowing!=None: return super().pp()
        return super().pp()+'('+','.join(m.pp() for m in self.members)+')'
    def run(self,rsltT):
        assert self.shadowing==None
        assert H.isA(rsltT,self.curType) # can only move down
        self.curType = rsltT
        if self.curType.tMfamily==T.mfTuple: 
            assert len(self.ast.members)==len(self.curType.tMindx)
        elif H.isEqual(self.curType,T.mvtAny): # conver Any to tuple of Anys
            self.curType = T.MtVal(T.mfTuple,len(self.ast.members)*(T.mvtAny,),None)
        else:
            assert False # we can probably handle other things FIXME
        # at this point curType is a tuple type
        self.members = tuple((newEt(self.ast.members[i],self,i,self.closR).run(self.curType.tMindx[i]) \
                            for i in range(len(self.ast.members))))
        self.curType = T.MtVal(T.mfTuple,tuple(m.curType for m in self.members),None)
        ch,newCt = T.tupleFixUp(self.curType) # if babies all restricted, build our restriction
        if ch: self.curType = newCt
        return self
    def fromChild(self,childId,newChildType):
        newChildType, returnNew, sendNew = gotNewType(newChildType,self.curType.tMindx[childId])
        #intersect = H.intersection2(newChildType, self.curType.tMindx[childId])
        ctChanged,self.curType = T.tupleFixUp(L.bind(self.curType).tMindex.value[childId].set(newChildType))
        if ctChanged or sendNew!=None:
            self.up.fromChild(self.myChildId,self.curType) # check shadowing!! FIXME
        return returnNew
    def fromParent(self,newType):
        newCur, returnNew, sendNew = gotNewType(newType,self.curType)
        ctChanged,self.curType = T.tupleFixUp(newCur)
        # NB the type of tuple is List(Type) so the only (index [0]) value in tMsubset is a pytuple of MtVal
        for i in range(len(self.members)):
            # should assert that both .tMindx.tMsubset have length 1
            if not H.isEqual(self.curType.tMindx.tMsubset[0][i],newCurType.tMindx.tMsubset[0][i]):
                self.members[i].fromParent(newCurType.tMindx.tMsubset[0][i]) # check shadowing!! FIXME
        return self.curType if ctChanged else returnNew

# myIds is an IdValReg with an mval:Mval and a registry list
# extIds are just Mval, with .value None if not defined yet
def needIdVal(k,closR): # return an Mval
    if k in closR.myIds: return closR.myIds[k].mval
    if k in closR.closure.extIds: return closR.closure.extIds[k]
    assert False

# Note that a closure can be created multiple times (setting the value of external ids).
# That creates an EtClosure. Then that EtClosure can be called multiple times (e.g. recursively)
# creating multiple EtClosureRun.
# EtClosure only produces a closure object (an Any=>Any). So the closure rslt and param and
# values of local variable belong with the call Et.
class EtClosure(Et):
    def __init__(self,shadowing,shadowLevel,ast,up,myChildId,closR):
        super().__init__(shadowing,shadowLevel,ast,up,myChildId,closR)
        assert isinstance(ast,A.AstClosure)
        self.extIds = None # filled in below
    def pp(self):
        if self.shadowing!=None: return super().pp()
        return super().pp()+'{'+'~~'.join(k+':'+T.ppT(v) for k,v in self.extIds.members)+'}'
    def closCallable(self): # a counter would be more efficient
        if self.gotAllEIs: return True # never changes from True to False, so memo when True
        self.gotAllEIs = All ((self.extIds[ei].mval.value != None) for ei in self.extIds)
        return self.gotAllEIs
    def fromClosR(self,iden,newType):
        if self.extIds[iden].value != None or newType.tMsubset==None: return
        self.extIds[iden].value = T.typeToVal(newType)
        self.gotAllEIs = All ((self.extIds[ei].mval.value != None) for ei in self.extIds)
    def run(self,rsltT):
        # Set all extIds to current values. Note that they must all have values "soon".
        # The closure is only callable after all values filled in. We register self with any
        # such "forward/future" references.
        self.curType = H.intersection2(rsltT,T.typeWithVal(T.mvtProcAnyAny,self))
        self.extIds = {k:needIdVal(k,self.closR) for k in self.ast.extIds} # Ids seen but not newId
        self.gotAllEIs = True
        for k,ei in self.extIds.items():
            if ei.mval.value==None:
                self.closR.myIds[k].registry.append(self)
                self.gotAllEIs = False
        return self
        # the body is relevant to ClosureRun, but not to us

# The following also covers AstNewIdentifier, AstClParam and AstClRslt
class EtIdentifier(Et):
    def __init__(self,shadowing,shadowLevel,ast,up,myChildId,closR):
        super().__init__(shadowing,shadowLevel,ast,up,myChildId,closR)
        self.ident = ast.identifier if isinstance(ast,A.AstIdentifier) or \
                                       isinstance(ast,A.AstNewIdentifier) \
                     else ' $' if isinstance(ast,A.AstClParam) else ' `$' # assert needed FIXME
        if self.ident in closR.myIds:
            self.curType = closR.myIds[self.ident].mval.mtVal # ??
            closR.myIds[self.ident].registry.append(self)
            self.isLocal = True
        else:
            assert self.ident in closR.closure.extIds
            self.curType = closR.closure.extIds[ast.identifier].mval.mtVal
            self.isLocal = False
    def pp(self):
        if self.shadowing!=None: return super().pp()
        q = "'" if self.isLocal else '"'
        return super().pp()+q+self.ident+q
    def run(self,rsltT):
        self.fromParent(rsltT) # caller should check self.curType FIXME
        return self
    def fromClosR(self,iden,newType):
        assert iden==self.ident
        if H.isEqual(newType,self.curType): return None
        intersect = H.intersection2(newType,self.curType)
        self.curType = intersect
        up.fromChild(self.myChildId,intersect) # check up!=None ??
        return intersect
    def fromParent(self,newType):
        # update our entry
        if not self.isLocal: # better agree
            assert H.isEqual(self.curType,newType)
            return None # not sure why parent is telling me this for a non local
        else:
            self.curType, returnNew, sendNew = gotNewType(newType,self.curType)
            if sendNew!=None: self.closR.updateAnId(self.ast.identifier,self.curType)
            return returnNew

# the "new" is compile time flag. At execution time it is just EtIdentifier???
EtNewIdentifier = EtIdentifier

class EtFreeVariable(Et): # from compile time only ast
    pass #assert False

class EtNewFreeVariable(Et): # from compile time only ast
    pass #assert False

# For a call to be run we need to have func set to be an EtClosure or an EtPrimitive.
# For the current debugging version of interp all unassigned identifiers are primitive
# and handled in the interpreter. If it is an EtClosure we build an ClosureRun to
# hold the myIds, clRslt=myIds[' `$'], clParam=myIds[' $']
# We don't currently allow for the function to be incompletely specified FIXME
class EtCall(Et):
    def __init__(self,shadowing,shadowLevel,ast,up,myChildId,closR):
        super().__init__(shadowing,shadowLevel,ast,up,myChildId,closR)
        self.procParam = newEt(ast.procParam,self,None,closR)
        self.runner = None
    def pp(self):
        if self.shadowing!=None: return super().pp()
        return '%'+self.procParam.pp()+'@'+self.runner.pp()+'!'
    def run(self,rsltT):
        self.procParam.run(T.mvtGenProcParam)
        funcT = self.procParam.curType.tMindx[0]
        paramT = self.procParam.curType.tMindx[1]
        assert funcT.tMfamily == T.mfProc and len(funcT.tMsubset)==1
        f = funcT.tMsubset[0]
        fPT,fRT = funcT.tMindx # I think -- should be a pytuple of mtypes
        # convert param to fPT and result to fRT before we start
        p = H.conv(T.typeToVal(paramT),fPT)
        if p==None or H.isEqual(p.mtVal,T.mvtEmpty): raise mFail
        paramT = p.mtVal
        self.curType = fRT # assert was Any before set by super()..
        if isinstance(f,EtClosure):
            self.runner = ClosureRun(self,f,paramT,self.curType).run()
        else:
            self.runner = PrimitiveRun(self,f,paramT,self.curType).run()
        return self
    def fromParent(self,newType):
        # this is the type of the result
        self.curType,returnNew,sendNew = gotNewType(newType,self.curType)
        if self.runner!=None and sendNew!=None: self.runner.rsltChange(self.curType)
        return returnNew
    def fromChild(self,childId,newType):
        # procParam is our child. childId is none. Only 2nd field (param) can change.
        assert childId == None and self.procParam.curType.members[0]==newType.members[0]
        newParam,returnNewP,sendNewP = gotNewType(self.procParam.curType.members[1],newType.members[1])
        L.bind(self.curType).members[1].set(newParam) # check first?
        if sendNewP!=None:
            self.up.fromChild(self.myChildId,self.curType)
            if self.runner!=None: 
                newParam = self.runner.paramChange(newType.members[1])
        return returnNewP

class Mrun: # either PrimitiveRun or ClosureRun
    def __init__(self,callEt):
        self.callEt = callEt
        #gevent.sleep(0) # if greenthreading then give others a go
    def rsltChange(self,newType):
        assert False
    def paramChange(self,newType):
        assert False

IdValReg = C.namedtuple('IdValReg','mval,registry') # registry of uses

# handles fake ids: ' $' and ' `$'
class ClosureRun(Mrun): # an EtCall turns into this if func is a closure. up is the EtCall
    def __init__(self,callEt,closure,paramT,rsltT):
        super().__init__(callEt)
        self.closure = closure
        self.initialparamT = paramT # for debug
        self.initialrsltT = rsltT   # for debug
        self.myIds = {k:IdValReg(mval=T.Mval(T.mvtAny,None),registry=[]) for k in closure.ast.myIds} # our ids
        self.myIds[' $'] = IdValReg(mval=T.typeToVal(paramT),registry=[])
        self.myIds[' `$'] = IdValReg(mval=T.typeToVal(rsltT),registry=[])
    def pp(self):
        return '^^'.join(k+':'+T.ppT(v.mval) for k,v in self.myIds.items())
    def updateAnId(self,name,newType):
        ivr = self.myIds[name]
        if H.isEqual(ivr.mval.mtVal,newType): return None
        intersect = H.intersection2(ivr.mval.mtVal,newType)
        if H.isEqual(intersect,ivr.mval.mtVal): return intersect
        for r in ivr.registry: 
            r.fromClosR(name,intersect)
        return intersect
    def rsltChange(self,newType):
        return self.updateAnId(' `$',newType)
    def paramChange(self,newType):
        return self.updateAnId(' $',newType)
    def run(self):
        assert self.closure.closCallable()
        self.body = newEt(self.closure.ast.expr,self.callEt,None,self).run(self.myIds[' `$'].mval.mtVal)
        return self

EtClParam = EtIdentifier # fake id ' $'

EtClRslt = EtIdentifier # fake id ' `$'

class PrimitiveRun(Mrun):
    def __init__(self,callEt,primClass,paramT,rsltT):
        super().__init__(callEt)
        #assert callable(primVal)
        self.primClass = primClass
        self.paramT = paramT
        self.rsltT = rsltT
    def pp(self):
        return self.primClass.txt
    def rsltChange(self,newType):
        r = self.pvRun.rsltChange(newType)
        if r==None: return None
        self.rsltT = r
        return r
    def paramChange(self,newType):
        p = self.pvRun.paramChange(newType)
        if p==None: return None
        self.paramT = p
        return p
    def run(self):
        self.pvRun = self.primClass(self.paramT,self.rsltT,self).run()
        #assert False # FIXME
        return self

class EtConstant(Et):
    def __init__(self,shadowing,shadowLevel,ast,up,myChildId,closR):
        super().__init__(shadowing,shadowLevel,ast,up,myChildId,closR)
    def run(self,rsltT):
        if self.ast.constType=='Number':
            v = D.Decimal(self.ast.const)
            self.curType = T.typeWithVal(T.mvtDecimal,v)
            self.mval = T.typeToVal(self.curType)
        else:
            assert False # FIXME
        return self

astToEt = {'AstTuple':EtTuple,'AstClosure':EtClosure,'AstClParam':EtClParam, \
        'AstClRslt':EtClRslt,'AstIdentifier':EtIdentifier,'AstNewIdentifier':EtNewIdentifier, \
        'AstFreeVariable':EtFreeVariable,'AstNewFreeVariable':EtNewFreeVariable, \
        'AstCall':EtCall, 'AstConstant':EtConstant }

def newEt(ast,up,myChildId,closR):
    return astToEt[type(ast).__name__](None,0,ast,up,myChildId,closR)

# we set up and closR to None and when we reference them we need to shadow
# them first, then reference that.
def shadow(et,level):
    assert level > et.shadowLevel
    return type(et)(shadowing=et,shadowlLevel=level,ast=et.ast,up=None,myChildId=et.myChildId,closR=None)
def unShadow(et): # NOTE we assume the caller is finished with et and we can trash it
    if et.shadowing == None:
        assert et.shadowLevel == 0
        return et
    assert et.shadowLevel > 0 and et.shadowLevel > et.shadowing.shadowLevel
    if et.shadowLevel == et.shadowing.shadowLevel+1:
        return et.shadowing.unShadow(et)
    else:
        et.shadowLevel -= 1
        return et

builtins = {
            "equal":IdValReg(T.mVequal,[]),
            "statements":IdValReg(T.mVstatements,[]),
            "casePswap":IdValReg(T.mVcasePswap,[]),
            "toType":IdValReg(T.mVtoType,[]),
            "tuple2list":IdValReg(T.mVtuple2list,[]),
            "greaterOrFail":IdValReg(T.mVgreaterOrFail,[]),
            "starOp":IdValReg(T.mVstarOp,[]),
            "subtract":IdValReg(T.mVsubtract,[]),
            "print":IdValReg(T.mVprint,[])
        }

class FakeClosure(EtClosure):
    def __init__(self):
        self.extIds = builtins

class FakeClosureRun(ClosureRun):
    def __init__(self):
        self.myIds = {}
        self.closure = FakeClosure()

class FakeEt(Et):
    def __init__(self):
        pass
    def fromChild(newType):
        pass

def interp(ast):
    assert isinstance(ast,A.AstClosure) # a program always forms a closure
    assert ast.extIds=={} # nothing yet ??
    ast.extIds = builtins # HACK FIXME
    pp = A.AstTuple(members=[ast,A.zeroTuple()])
    callAst = A.AstCall(procParam=pp)
    EtCall(None,0,callAst,FakeEt(),None,FakeClosureRun()).run(T.mvtAny)

# Consider { $=`x+1; `$=`y; x=2; y=4} which should (a) check that input is
# compatible with 3 and set it to 3, and check that output is compatible with
# 4 and set it to 4.

# Consider f(`x)=6. Is equal(f(`x),6).
# Or f(`x)=`y. 

# Consider `fact:Nat=>Nat; fact = {$=0;1}; fact = {$=1;1}; fact = {$>?0;$*fact($-1)}
# declarations combined. Looks ok in free var form:
#   fact 0 = 1; fact 1 = 1; fact _n = _n * fact(_n-1)

if __name__=="__main__":
    pass
