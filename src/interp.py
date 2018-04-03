# interp.py is a debugging step, to make sure we understand how execution works.

# [[About to completely rewrite this so that there are no values, only types.
# A value is just a type restricted to a single value. In a wildly optimistic
# way, I see this as a step towards a language where we are interested in types as
# spaces and the arrows linking them, while often avoiding getting down and
# dirty and looking at actual values within those types. Note tMindx is still
# an Mval -- too confusing otherwise.]]

# Execution is easy (???). We create an execution tree where at each point
# the up result is unified with the calculation. Tuples do it in parallel.
# A call creates a new execution node.
#
# Since there are no primitive types or operations in the interpreter, we are
# retricted to compile-time types, and identifiers which aren't actually
# defined are interpreted here.

# The Et have to send messages to each other. Logically these can only be about types.
# I.e. when an Et finds out that its type is narrower than it previously thought
# it should let its neighbors know. Of course the most exact thing it can know is
# that it has a certain specific value.
#
# Primitive procedures each have their own way of handling this stuff. Consider = (equal):
# It expects a 2-tuple of Ets. It unifies each, and the result (though that is often None).
# Whenever it gets an improved type from one of the 3 it passes it to the other 2, so
# they stay in sync.
#
# Or consider tuple creation (AstTuple in the ast). The first thing (as always) is
# whether the required result is compatible with the tuple of the given size. Then
# We tell the rslt guy that we have a Tuple[Any Any Any] (say) 

import lenses as L
import mast as A
import cttypes as T
import mhierarchy as H
import collections as C

# The execution tree follows the ast tree. The rslt is the parent et that we are
# unifying with (None if Discard).
# When we get a message (like fromChild or fromParent) that narrows down our type
# then we should actually narrow it to the intersection, and if that is different
# from the modification we should let the caller know.
class Et:
    def __init__(self,ast,up,myChildId,closR):
        self.ast = ast
        self.up = up
        self.myChildId = myChildId
        self.closR = closR # ClosureRun context
        self.curType = T.mvtAny # :T.MtVal
    def run(self):
        # will create children, send them updates about them, receive update from them
        assert False # must be overridden
    def fromChild(self,childId,newType):
        assert False # to be overridden -- children know their id.
        # return intersection type if different from newType, else None
    def fromParent(self,newType): # curType/newType are T.MtVal
        # parent tells us our improved partial value
        # This default is ok if we don't have to tell our children about it
        self.curType = H.intersection2(self.curType,newType)
        if H.isEqual(newType, self.curType): return None
        return self.curType

class EtTuple(Et):
    def __init__(self,ast,up,myChildId,closR):
        super().__init__(self,ast,up,myChildId,closR)
        assert isinstance(ast,A.AstTuple)
    def run(self):
        self.members = [newEt(ast.members[i],self,i,closR).run() for i in range(len(ast.members))]
        ti = T.Mval(T.mvtListOfType,tuple(m.curType for m in self.members))
        self.curType = T.MtVal(mfTuple,ti,None)
        ch,newCt = T.tupleFixUp(self.curType): # if babies all restricted, build our restriction
        if ch: self.curType = newCt
        return self
    def fromChild(self,childId,newType):
        ti = self.curType.tMindx # List Type
        intersect = H.intersection2(newType, ti.value[childId].value)
        if H.isEqual(newType,intersect): return None # no news
        lct = L.bind(self.curType)
        ctChanged,self.curType = T.tupleFixUp(lct.tMindex.value[childId].value.set(intersect))
        #if T.tupleFixUp(self.curType): # if babies all restricted, build our restriction
        #    self.curVal = self.curType.tMsubset[0]
        if ctChanged: self.up.fromChild(myChildId,self.curType)
        return intersect
    def fromParent(self,newType):
        intersect = super().fromParent(self,newType)
        if intersect==None: return None
        # where oldType differs from new curType, send to child
        for i in range(len(self.members)):
            # should assert that both tMindx.tMsubset have length 1
            if not T.isEqual(oldType.tMindx.tMsubset[0][i],self.curType.tMindx.tMsubset[0][i]):
                self.members[i].fromParent(self.curType.tMindx.tMsubset[0][i])
        return intersect

def needIdVal(k,closR):
    if k in closR.myIds: return closR.myIds[k].value
    if k in closR.closure.extIds: return closR.closure.extIds[k]
    assert False

# Note that a closure can be created multiple times (setting the value of external ids).
# That creates an EtClosure. Then that EtClosure can be called multiple times (e.g. recursively)
# creating multiple EtClosureRun.
# EtClosure only produces a closure object (an Any=>Any). So the closure rslt and param and
# values of local variable belong with the call Et.
class EtClosure(Et):
    def __init__(self,ast,up,myChildId,clos):
        super().__init__(self,ast,up,myChildId,clos)
        assert isinstance(ast,A.AstClosure)
        self.curType = T.typeWithVal(T.mvtClosureT,self) # procs are closure or primitive
        #self.extIds = {k:needIdVal(k,clos) for k in ast.extIds} # Ids seen but not newId
        #self.callable = False # true when all extIds have values
        #self.body = newEt(ast.expr,self,None,self) # we unify body with clRslt FIXME
    def closCallable(self):
        if self.gotAllEIs: return True # never changes from True to False, so memo when True
        self.gotAllEIs = All ((self.extIds[ei].value != None) for ei in self.extIds)
        return self.gotAllEIs
    def extIdGotValue(eigv):
        assert self.extIds[eigv].value != None
        self.gotAllEIs = All ((self.extIds[ei].value != None) for ei in self.extIds)
    def run(self):
        # Set all extIds to current values. Note that they must all have values "soon".
        # The closure is only callable after all values filled in. We register self with any
        # such "forward/future" references.
        self.extIds = {k:needIdVal(k,clos) for k in ast.extIds} # Ids seen but not newId
        self.gotAllEIs = True
        for ei in self.extIds:
            if ei.value==None: 
                ei.waitForValue(self)
                self.gotAllEIs = False
        return self
        # the body is relevant to ClosureRun, but not to us

# The following also covers AstNewIdentifier, AstClParam and AstClRslt
class EtIdentifier(Et):
    def __init__(self,ast,up,myChildId,closR):
        super().__init__(self,ast,up,myChildId,closR)
        self.ident = ast.identifier if (isinstance(ast,AstIdentifier) or isinstance(ast,AstNewIdentifier) \
                     else ' $' if isinstance(ast,AstClParam) else ' `$'
        if self.ident in closR.myIds:
            self.curType = closR.myIds[self.ident].idType # ??
            closR.myIds[self.ident].registry.append(self)
            self.isLocal = True
        else:
            assert self.ident in closR.closure.extIds
            self.curType = closR.closure.extIds[ast.identifier].idType
            self.isLocal = False
    def fromClosR(self,newType):
        if T.isEqual(newType,self.curType): return None
        intersect = T.intersection(newType,self.curType)
        self.curType = intersect
        up.fromChild(self.myChildId,intersect)
        return intersect
    def fromParent(self,newType):
        # update our entry
        if not self.isLocal: # better agree
            assert T.isEqual(self.curType,newType)
            return None # not sure why parent is telling me this for a non local
        else:
            intersect = T.intersection(newType,self.curType)
            if T.isEqual(intersect,self.curType): return None
            self.curType = intersect
            #assert T.isA(newType,self.value.mtVal) # monotonic
            #ns = intersect.tMsubset
            #self.value = Mval(mtVal=intersect,value=(None if (ns==None or len(ns)!=1) else ns[0]))
            self.closR.updateAnId(ast.identifier,self.curType)
            return intersect

# the "new" is compile time flag. At execution time it is just EtIdentifier???
EtNewIdentifier = EtIdentifier

class EtFreeVariable(Et): # from compile time only ast
    assert False

class EtNewFreeVariable(Et): # from compile time only ast
    assert False

# For a call to be run we need to have func set to be an EtClosure or an EtPrimitive.
# For the current debugging version of interp all unassigned identifiers are primitive
# and handled in the interpreter. If it is an EtClosure we build an EtClosureRun to
# hold the myIds, clRslt, clParam
# We don't currently allow for the function to be incompletely specified FIXME
class EtCall(Et):
    def __init__(self,ast,up,myChildId,closR):
        super().__init__(self,ast,up,myChildId,closR)
        self.procParam = newEt(ast.procParam,self,None,closR)
        self.runner = None
        #self.func = newEt(ast.procParam.members[0],self,'func',clos)
        #self.param = newEt(ast.procParam[1],self,'param',clos)
        #self.clParam = newEt(A.AstParam(),self,'clParam',self.func)
        #self.clRslt = newEt(A.AstRslt(),self,'clRslt',self.func)
        #self.myIds = {} # newIdentifier goes here
    def run(self):
        self.procParam.run()
        funcT = self.procParam.curType.members[0]
        paramT = self.procParam.curType.members[1]
        assert funcT.tMfamily == mfProc and len(funcT.tMsubset)==1
        f = funcT.tMsubset[0]
        if isinstance(f,EtClosure):
            self.runner = ClosureRun(self,f,paramT,curType).run()
        else:
            assert callable(f)
            self.runner = PrimitiveRun(self,f,param,curType).run()
        return self
    def fromParent(self,newType):
        # this is the type of the result
        intersect = T.intersection(newType,self.curType)
        if T.isEqual(intersect,newType): return None # no change
        if self.runner!=None: self.runner.rsltChange(intersect)
        return intersect
    def fromChild(self,childId,newType):
        # procParam is our child. childId is none. Only 2nd field (param) can change.
        assert childId == None and self.procParam.curType.members[0]==newType.members[0]
        intersect = T.intersection(self.procParam.curType.members[1],newType.members[1])
        if not T.isEqual(intersect,self.procParam.curType.members[1]):
            if self.runner!=None: self.runner.paramChange(newType.members[1])
        return None # if T.isEqual(intersect,newType.members[1]) else \
                # L.bind(self.procParam)[1].set(intersect) # tell child of change. Can this happen?

class Mrun: # either PrimitiveRun or ClosureRun
    def __init__(self,callEt):
        self.callEt = callEt
    def restart(self):
        assert False # allow parent to restart me (if rslt or param not yet set)
    def rsltChange(self,newType):
        assert False
    def paramChange(self,newType):
        assert False

IdTypeReg = C.namedtuple('IdTypeReg','idType,registry') # registry of uses

# need to handle fake ids: ' $' and ' `$' FIXME
class ClosureRun(Mrun): # an EtCall turns into this if func is a closure. up is the EtCall
    def __init__(self,callEt,closure,paramT,rsltT):
        super().__init__(self,callEt)
        self.callEt = callEt
        self.closure = closure
        self.initialparamT = paramT # for debug
        self.initialrsltT = rsltT   # for debug
        self.myIds = {k:IdTypeReg(idType=T.mvtAny,registry=[]) for k in closure.ast.myIds} # our ids
        self.myIds[' $'] = IdTypeReg(T.typeToVal(paramT),registry=[])
        self.myIds[' `$'] = IdTypeReg(T.typeToVal(rsltT),registry=[])
    def updateAnId(self,name,newType):
        ivr = self.myIds[name]
        if T.isEqual(ivr.idType,newType): return None
        intersect = T.intersection(ivr.idType,newType)
        if T.isEqual(intersect,ivr.idType): return intersect
        for ei in ivr.registry: ei.fromClosR(intersect)
        return intersect
    def rsltChange(self,newType):
        return self.updateAnId(' `$',newType)
    def paramChange(self,newType):
        return self.updateAnId(' $',newType)
    def run(self):
        assert self.closure.closCallable()
        self.body = newEt(closure.ast.expr,self,None,self).run()
        return self

EtClParam = EtIdentifier # fake id ' $'

EtClRslt = EtIdentifier # fake id ' `$'

class PrimitiveRun(Mrun):
    def __init__(self,callEt,primVal,paramT,rsltT):
        super().__init__(self,callEt)
        self.primVal = primVal
        self.paramT = paramT
        self.rsltT = rsltT
    def run(self):
        rslt = self.primVal(run=(paramT,rsltT))
        assert False # FIXME
        return self

class EtConstant(Et):
    def __init__(self,ast,up,myChildId,closR):
        super().__init__(self,ast,up,myChildId,closR)

astToEt = {'AstTuple':EtTuple,'AstClosure':EtClosure,'AstClParam':EtClParam, \
        'AstClRslt':EtClRslt,'AstIdentifier':EtIdentifier,'AstNewIdentifier':EtNewIdentifier, \
        'AstFreeVariable':EtFreeVariable,'AstNewFreeVariable':EtNewFreeVariable, \
        'AstCall':EtCall, 'AstConstant':EtConstant }

def newEt(ast,up,myChildId,closR):
    return astToEt[type(ast).__name__](ast,up,myChildId,closR)

def interp(ast):
    assert isinstance(ast,A.AstClosure) # a program always forms a closure
    pp = A.AstTuple(members=[ast,A.zeroTuple()])
    EtCall(pp,None,None,None).run()

# Consider { $=`x+1; `$=`y; x=2; y=4} which should (a) check that input is
# compatible with 3 and set it to 3, and check that output is compatible with
# 4 and set it to 4.

# Consider f(`x)=6. Is equal(f(`x),6).
# Or f(`x)=`y. 

if __name__=="__main__":
    pass
