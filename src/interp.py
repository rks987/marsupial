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
# that it has a certain specific value. (i.e. tMsubset has length 1).
# The natural way to do this would be the actor model, and if this was Erlang
# or Go that's what I'd use. I could use gevent (or one of the other python actor
# implementations), but I don't trust them. When an Et sends a message that typically 
# sets off a cascade of messages, including ones coming back. So we need to handle
# buffering and such like. We do this by: (a) we just grab incoming messages and
# store in .rcvd; (b) whenever we have anything in rcvd or toSend we run loop;
# (c) loop sends stuff from toSend whenever rcvd is empty.
#
# Note that parents know about their children and send/receive newType of the child.
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
import gevent

# myIds and extIds values -- extIds don't use closureWait, but might for "local closures"
IdTypeReg = C.namedtuple('IdTypeReg','mtval,registry') # registry of uses and waiting closures

# The execution tree follows the ast tree. The rslt is the parent Et that we are
# unifying with.
# When we get a message (like fromChild or fromParent) that narrows down our type
# then we should actually narrow it to the intersection. We keep track of: (a) what our
# neighbors have sent us that we haven't processed yet; and (b) what we need to send them. 
# On any input we loop until we have nothing to tell any neighbor.
#
# Note that ast and type and values are immutable, but Et aren't.
#
# HackAlert: childId is not allowed to be a negative integer or string. -1 is for parent, 
# other negative numbers for other special neighbors, string is an id in our ClosureRun
class Et:
    def __init__(self,shadowing,shadowLevel,ast,up,myChildId,closR):
        self.shadowing = shadowing
        self.shadowLevel = shadowLevel
        self.ast = ast
        self.up = up # parent Et
        self.myChildId = myChildId
        self.closR = closR # ClosureRun context
        self.curType = shadowing.curType if shadowing!=None else T.mvtAny # :T.MtVal
        self.rcvd = {} # waiting to process
        self.toSend = {} # stuff we plan to send
        self.looping = False
    def pp(self):
        if self.shadowing!=None:
            return str(self.shadowlevel)+'|'+self.shadowing.pp()+'|'
        return ('<'+T.ppT(self.curType,())+'>')
    def loop(self): # default
        if self.looping: return
        self.looping = True
        while True:
            if len(self.rcvd)==0 and len(self.toSend)==0:
                self.looping = False
                return
            while len(self.rcvd)!=0: #process all rcvd then do one toSend
                k,v = self.rcvd.popitem()
                # k is childId or negative number for parent/etc, v is a Neighbor rec
                if k==-1:
                    self.fromParent0(v) # do something
                elif isinstance(k,str):
                    self.fromClosR0(k,v)
                else: # must be a child
                    self.fromChild0(k,v)
            if len(self.toSend)!=0: # any of these might induce new rcvd
                k,v = self.toSend.popitem()
                if k==-1:
                    self.up.fromChild(self.myChildId,v)
                elif isinstance(k,str):
                    self.closR.updateAnId(k,v)
                else:
                    self.toChild(k,v)
    def run(self,rsltT):
        # will create children, create some toSend, run loop
        assert False # must be overridden
    def fromChild(self,childId,newType):
        self.rcvd[childId] = newType
        self.loop()
    def fromChild0(self,childId,newType):
        assert False # to be overridden -- children know their id.
    def toChild(self,childId,newType):
        assert False # sending to child varies with Et subtypes
    def fromParent(self,newType): # curType/newType are T.MtVal
        self.rcvd[-1] = newType
        self.loop()
    def fromParent0(self,newType):
        # This default is ok if we don't have to tell our children about it
        self.curType = H.intersection2(self.curType,newType)
        if H.isEqual(newType, self.curType):
            self.toSend.pop(-1,None) # remove any (unlikely) older toSend
        else:
            self.toSend[-1] = self.curType
    def fromClosR(self,iden,newType): # note EtIdentifier and EtClosure both have this
        assert isinstance(self,EtClosure) or isinstance(self,EtIdentifier)
        self.rcvd[iden] = newType
        self.loop()
    def fromClosR0(self,iden,newType):
        assert False # to be overriden by EtClosure and EtIdentifier
    def shadow(self,level): # default ok for Et with no children ???
        if level==self.shadowLevel: 
            return self
        assert level>self.shadowLevel
        return type(self)(shadowing=self,shadowlLevel=level,ast=self.ast,up=None,\
                myChildId=self.myChildId,closR=None)

# utility routine for newType notifications like fromChild
def gotNewType(newType,curType): # return new curType, if changed, if new not = intersect
    #if H.isA(newType,curType)==None and not H.isEqual(newType,curType): assert False
    newCur = H.intersection2(newType,curType)
    curCh = not H.isEqual(newCur,curType)
    newWrong = not H.isEqual(newType,newCur)
    return newCur, curCh, newWrong

# indexType is List(Type), so .tMindx will be a pytuple of :mvtType
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
        #assert H.isA(rsltT,self.curType) # can only move down
        self.curType = rsltT
        if self.curType.tMfamily==T.mfTuple: 
            assert len(self.ast.members)==len(self.curType.tMindx)
        elif H.isEqual(self.curType,T.mvtAny): # convert Any to tuple of Anys
            self.curType = T.MtVal(T.mfTuple,len(self.ast.members)*(T.mvtAny,),None)
        else:
            assert False # we can probably handle other things FIXME
        # at this point curType is a tuple type
        self.members = tuple(newEt(self.ast.members[i],self,i,self.closR)\
                             .run(self.curType.tMindx[i]) for i in range(len(self.ast.members)))
        self.curType = T.MtVal(T.mfTuple,tuple(m.curType for m in self.members),None)
        ch,newCt = T.tupleFixUp(self.curType) # if babies all restricted, build our restriction
        if ch: 
            self.curType = newCt
        self.loop() # creating babies might cause us to get messages
        return self
    def fromChild0(self,childId,newChildType): # only called from loop
        newChildType, curCh, newWrong = gotNewType(newChildType,self.curType.tMindx[childId])
        ctCh,self.curType = T.tupleFixUp(L.bind(self.curType).tMindx[childId].set(newChildType))
        if ctCh or curCh:
            self.toSend[-1] = self.curType # check shadowing!! FIXME
        #if newWrong: # could this create an oscillating loop?
        #    self.toSend[myChildId] = self.curType.tMindx[childId]
    def fromParent0(self,newType): # only called from loop
        newCur, curCh, newWrong = gotNewType(newType,self.curType)
        ctChanged,newCur = T.tupleFixUp(newCur)
        # NB type of tuple is List(Type) so only (index [0]) value in tMsubset is a pytuple of MtVal
        for i in range(len(self.members)):
            # should assert that both .tMindx have length 1
            if not H.isEqual(self.curType.tMindx[i],newCur.tMindx[i]):
                self.toSend[i] = newCur.tMindx[i] # shadowing?? FIXME
        if ctChanged:
            self.toSend[-1] = newCur
        self.curType = newCur
    def toChild(self,childId,newType):
        self.members[childId].fromParent(newType) # note that this is ouside the queue/loop system

# myIds and extIds are an IdTypeReg with an mtval and a registry list. The registry
# list has matching EtIdentifier nodes, and al EtClosure that use the id.
def needIdType(k,closR): # return an MtVal
    if k in closR.myIds: return closR.myIds[k].mtval
    if k in closR.closure.extIds: return closR.closure.extIds[k].mtval
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
        # Ids seen but not newId:
        self.extIds = {k:IdTypeReg(needIdType(k,self.closR),[]) for k in self.ast.extIds}
        self.gotAllEIs = True
        # if a closure is being evaluated then the closure it is lexically in is running, and hence
        # has all extIds defined. So if not defined it must be in closureRun's myIds
        for k,ei in self.extIds.items():
            if ei.mtval.tMsubset==None:
                self.closR.myIds[k].registry.append(self) # registry has ids and inner closures
                self.gotAllEIs = False
    def pp(self):
        if self.shadowing!=None: return super().pp()
        return super().pp()+'{'+'~~'.join((k+':'+T.ppT(v,())) for k,v in self.extIds.items())+'}'
    def closCallable(self): # a counter would be more efficient
        if self.gotAllEIs: return True # never changes from True to False, so memo when True
        self.gotAllEIs = All ((eiv.mtval.tMsubset != None) for eiv in self.extIds.values())
        return self.gotAllEIs
    def fromClosR0(self,iden,newType): # note EtIdentifier and EtClosure both have this
        newCur, curCh, newWrong = gotNewType(newType,self.extIds[iden].mtval)
        if not curCh: return # current value not changed
        self.extIds[iden] = L.bind(self.extIds[iden]).mtval.set(newCur)
        self.gotAllEIs = All ((eiv.mtval.tMsubset != None) for eiv in self.extIds.values())
        assert not newWrong
    def run(self,rsltT):
        # Set all extIds to current values. Note that they must all have values "soon".
        # The closure is only callable after all values filled in. We register self with any
        # such "forward/future" references.
        self.curType = H.intersection2(rsltT,T.typeWithVal(T.mvtProcAnyAny,self))
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
            self.curType = closR.myIds[self.ident].mtval # ??
            closR.myIds[self.ident].registry.append(self)
            self.isLocal = True
        else:
            assert self.ident in closR.closure.extIds
            self.curType = closR.closure.extIds[ast.identifier].mtval
            self.isLocal = False
    def pp(self):
        if self.shadowing!=None: return super().pp()
        q = "'" if self.isLocal else '"'
        return super().pp()+q+self.ident+q
    def run(self,rsltT):
        self.fromParent(rsltT) # caller should check self.curType FIXME
        return self
    def fromClosR0(self,iden,newType): # note EtIdentifier and EtClosure both have this
        assert iden==self.ident
        self.curType, curCh, newWrong = gotNewType(newType,self.curType)
        if curCh: # current value changed
            self.toSend[-1] = self.curType # tell parent
        #if newWrong:
        #    self.toSend[iden] = self.curType # can this happen ??
    def fromParent0(self,newType):
        # update our entry
        if not self.isLocal: # better agree
            assert H.isEqual(self.curType,newType)
            return # not sure why parent is telling me this for a non local
        else:
            self.curType, curCh, newWrong = gotNewType(newType,self.curType)
            if curCh: #self.closR.updateAnId(self.ident,self.curType)
                self.toSend[self.ident] = self.curType
            #if newWrong:
            #    self.toSend[-1] = self.curType # ???

# the "new" is compile time flag. At execution time it is just EtIdentifier???
EtNewIdentifier = EtIdentifier

class EtFreeVariable(Et): # from compile time only ast
    pass #assert False

class EtNewFreeVariable(Et): # from compile time only ast
    pass #assert False

# For a call to be run we need to have func set to be an EtClosure or an EtPrimitive.
# For the current debugging version of interp all unassigned identifiers are primitive
# and handled in the interpreter. If it is an EtClosure we build a ClosureRun to
# hold the myIds, clRslt=myIds[' `$'], clParam=myIds[' $']
# We don't currently allow for the function to be incompletely specified FIXME
#
# Note that the actual parameter and the target required by the procedure might
# not be the same type. We force both down to the intersection. Ditto for the output.
# This might mean that primitive procedures need to convert (e.g. H.conv) upwards.
# 
class EtCall(Et):
    def __init__(self,shadowing,shadowLevel,ast,up,myChildId,closR):
        super().__init__(shadowing,shadowLevel,ast,up,myChildId,closR)
        self.procEt = newEt(ast.procParam.members[0],self,True,closR) # childId is "isProc"
        self.paramEt = newEt(ast.procParam.members[1],self,False,closR)
        # actual param type is paramEt.curType
        self.runner = None
    def pp(self):
        if self.shadowing!=None: return super().pp()
        return '%'+self.procEt.pp()+'(('+self.paramEt.pp()+'))->'+T.ppT(self.curType,())
    def run(self,rsltT):
        self.curType = rsltT
        self.procEt.run(T.mvtProcAnyAny)
        funcT = self.procEt.curType
        assert funcT.tMfamily == T.mfProc and len(funcT.tMsubset)==1
        f = funcT.tMsubset[0]
        fPT,fRT = funcT.tMindx # I think -- should be a pytuple of mtypes
        self.paramEt.run(T.mvtAny)
        fPT = H.intersection2(self.paramEt.curType,fPT)
        self.toSend[False] = fPT # send to child (False=)param
        self.curType = fRT = H.intersection2(self.curType,fRT)
        if isinstance(f,EtClosure):
            self.runner = ClosureRun(self,f)
        else:
            self.runner = PrimitiveRun(self,f)
        nfPT,self.curType = self.runner.changePR(fPT,fRT)
        self.toSend[False] = nfPT
        self.toSend[-1] = self.curType
        self.loop()
        return self
    def fromParent0(self,newType):
        # this is the type of the target result
        self.curType, curCh, newWrong = gotNewType(newType,self.curType)
        assert not newWrong #??
        if not curCh: return
        fPT,self.curType = self.runner.changePR(self.paramEt.curType,self.curType) # ????
        fPT = H.intersection2(self.paramEt.curType,fPT) #???
        self.toSend[False] = fPT # send to child (False=)param
        self.toSend[-1] = self.curType # to parent ???
    def fromChild0(self,childId,newType):
        # Our children are self.procEt (childId=True) and self.aParamEt (id False).
        assert childId == False # isProc is not allowed to be true: proc can't change
        if H.isEqual(newType,self.paramEt.curType): return
        fPT,self.curType = self.runner.changePR(newType,self.curType)
        self.toSend[False] = fPT # send to child (False=)param
        self.toSend[-1] = self.curType
    def toChild(self,isProc,newType): # childId: true for proc, False for param
        (self.procEt if isProc else self.paramEt).fromParent(newType)
        

# an Mrun gets a param-result change from up and returns changed parameter
# and result. Even though a ClosureRun has an arbitrarily large expr executing,
# it can never escape into the wider context. So an Mrun is just a series of call-return
# not general message passing as with Et.
class Mrun: # either PrimitiveRun or ClosureRun
    def __init__(self,callEt):
        self.callEt = callEt
        self.running = False # just to check we don't get called while running
        #self.paramT = T.mvtAny
        #self.rsltT = T.mvtAny
        gevent.sleep(0) # if greenthreading then give others a go
    def changePR0(self,newParamT,newRsltT):
        assert False # must override
    def changePR(self,newParamT,newRsltT):
        assert not self.running # make sure not in here twice
        self.running = True
        r = self.changePR0(newParamT,newRsltT) # sub classes to implement
        self.running = False
        return r

# handles fake ids: ' $' and ' `$'
class ClosureRun(Mrun): # an EtCall turns into this if func is a closure. up is the EtCall
    def __init__(self,callEt,closure):
        super().__init__(callEt)
        self.closure = closure
        self.myIds = {k:IdTypeReg(T.mvtAny,[]) for k in closure.ast.myIds} # our ids
        self.myIds[' $'] = IdTypeReg(T.mvtAny,[]) #paramT,[])
        self.myIds[' `$'] = IdTypeReg(T.mvtAny,[]) #rsltT,[])
        self.body = None # create when needed
    def pp(self):
        return '{!'+('^^'.join(k+':'+T.ppT(v.mtval,()) for k,v in self.myIds.items()))+'!}'
    def updateAnId(self,name,newType):
        newCur, curCh, newWrong = gotNewType(newType,self.myIds[name].mtval)
        if curCh: # different from curType
            self.myIds[name] = L.bind(self.myIds[name]).mtval.set(newCur)
            for r in self.myIds[name].registry: # tell uses and closures about change
                r.fromClosR(name,newCur)
        #return self.myIds[name].mtval
    def changePR0(self,newParamT,newRsltT):
        if self.body==None:
            assert self.closure.closCallable()
            # body of closure doesn't interact with outside except through ClosureRun
            self.body = newEt(self.closure.ast.expr,FakeEt(),None,self).run(newRsltT)
        self.updateAnId(' $',newParamT)
        self.updateAnId(' `$',newRsltT)
        return self.myIds[' $'].mtval,self.myIds[' `$'].mtval

EtClParam = EtIdentifier # fake id ' $'

EtClRslt = EtIdentifier # fake id ' `$'

class PrimitiveRun(Mrun):
    def __init__(self,callEt,primClass):
        super().__init__(callEt)
        self.primClass = primClass
        self.pvRun = None # create when needed
        #self.pvRun = self.primClass.runner(self.paramT,self.rsltT,self)
    def pp(self):
        return self.primClass.txt
    def changePR0(self,newParamT,newRsltT):
        if self.pvRun == None:
            self.pvRun = self.primClass.runner(self)
        return self.pvRun.pTrT(newParamT,newRsltT)

class EtConstant(Et):
    def __init__(self,shadowing,shadowLevel,ast,up,myChildId,closR):
        super().__init__(shadowing,shadowLevel,ast,up,myChildId,closR)
    def run(self,rsltT):
        if self.ast.constType=='Number':
            v = D.Decimal(self.ast.const)
            self.curType = T.typeWithVal(T.mvtDecimal,v)
            #self.mval = T.typeToVal(self.curType) # why not T.Mval(self.curType,v) FIXME
        else:
            assert False # FIXME
        self.toSend[-1] = self.curType
        self.loop()
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
            "Nat":IdTypeReg(T.mVnat,[]),
            "equal":IdTypeReg(T.mvTequal,[]),
            "statements":IdTypeReg(T.mvTstatements,[]),
            "casePswap":IdTypeReg(T.mvTcasePswap,[]),
            "toType":IdTypeReg(T.mvTtoType,[]),
            "tuple2list":IdTypeReg(T.mvTtuple2list,[]),
            "greaterOrFail":IdTypeReg(T.mvTgreaterOrFail,[]),
            "starOp":IdTypeReg(T.mvTstarOp,[]),
            "subtract":IdTypeReg(T.mvTsubtract,[]),
            "print":IdTypeReg(T.mvTprint,[])
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
    def fromChild(self,childId,newType):
        pass

def interp(ast):
    assert isinstance(ast,A.AstClosure) # a program always forms a closure
    pp = A.AstTuple(members=(ast,A.zeroTuple()))
    callAst = A.AstCall(procParam=pp)
    return EtCall(None,0,callAst,FakeEt(),None,FakeClosureRun()).run(T.mvtAny)

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
