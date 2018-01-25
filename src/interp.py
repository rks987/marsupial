# interp.py is a debugging step, to make sure we understand how execution works.

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
# We tell the rslt guy that we have a Tuple[Any,Any,Any] (say) 

import mast as A
import cttypes as T

# The execution tree follows the ast tree. The rslt is the parent et that we are
# unifying with (None if Discard). The need is a list of other constraints that we know??.
class Et:
    def __init__(self,ast,up,myChildId,clos):
        self.ast = ast
        self.up = up
        self.myChildId = myChildId
        self.clos = clos # closure context
        self.curType = T.mvAny
        self.curVal = None
    def fromChild(self,childId,newType):
        assert False # to be overridden -- children know their id.
    def fromParent(self,newType):
        # parent tells us our improved partial value
        assert False
    def run(self):
        # will create children, send them updates about them, receive update from them
        assert False # must be overridden

class EtTuple(Et):
    def __init__(self,ast,up,myChildId,clos):
        super().__init__(self,ast,up,myChildId,clos)
        assert isinstance(ast,A.AstTuple)
        self.members = [newEt(ast.members[i],self,i,clos) for i in range(len(ast.members))]
        ti = T.Mval(T.mfList,T.mfType,[m.curType for m in self.members])
        self.curType = T.Mval(T.mfType,None,(mfTuple,ti,None))
    def fromChild(self,childId,newType):
        ti = self.curType.value[1]
        ti.value[childId] = newType # assume monotonic ??
        T.tupleFixUp(self.curType) # if babies all restricted, build our restriction
        self.up.fromChild(myChildId,self.curType)
    def fromParent(self,newType):
        pass # FIXME
    def run(self):
        # we run the parts, theoretically in parallel
        for mEt in self.members: mEt.run()

# EtClosure only produces a closure object (an Any=>Any). So the closure rslt and param and
# values of local variable belong with the call Et.
class EtClosure(Et):
    def __init__(self,ast,up,myChildId,clos):
        super().__init__(self,ast,up,myChildId,clos)
        assert isinstance(ast,A.AstClosure)
        self.extIds = {} # Ids seen but not newId
        self.body = newEt(ast.expr,self,None,self) # we unify body with clRslt FIXME

class EtClParam(Et):
    pass

class EtClRslt(Et):
    pass

class EtIdentifier(Et):
    pass

class EtNewIdentifier(Et):
    pass

class EtFreeVariable(Et):
    pass

class EtNewFreeVariable(Et):
    pass

class EtCall(Et):
    def __init__(self,ast,up,myChildId,clos):
        super().__init__(self,ast,up,myChildId,clos)
        self.clParam = newEt(A.AstParam(),self,'param',self)
        self.clRslt = newEt(A.AstRslt(),self,'rslt',self)
        self.myIds = {} # newIdentifier goes here


class EtConstant(Et):
    pass

astToEt = {'AstTuple':EtTuple,'AstClosure':EtClosure,'AstClParam':EtClParam, \
        'AstClRslt':EtClRslt,'AstIdentifier':EtIdentifier,'AstNewIdentifier':EtNewIdentifier, \
        'AstFreeVariable':EtFreeVariable,'AstNewFreeVariable':EtNewFreeVariable, \
        'AstCall':EtCall, 'AstConstant':EtConstant }

def newEt(ast,up,myChildId,clos):
    return astToEt[type(ast).__name__](ast,up,myChildId,clos)

def interp(ast):
    et = newEt(ast,None)
    et.run()
