# combine.py implements the case primitive which is used in various
# places -- including the case statement.

import gevent
import interp as I
#from interp import Et, ClosureRun
import mast as A
#import lenses as L

# CaseControl takes (1) the primitive runner that called us (for up communication);
# (2) a list of procedures; (3) a parameter (which may contain holes); (4) a result 
# that is likely to contain holes. It returns a CaseControl object that allows
# further communication (?).

# The idea is that we run each case in its own green thread. When any of them finish
# we check if they are really done: both param and rslt have unique values. Then
# (A) If any are really done then: (A1) stop any that are still running; (A2) Check
# that all that are really done agree (params equal, results combine); (A3) restart 
# all others with param set to be the same as the ones that finished.
# (B) If all finish but not really done then we just wait for paramChange or rsltChange
# from above, then continue cases with changed info.

# Note that we really should be asking for the result of a branch to be potentially
# combinable into the required result. Instead we are going to pretend that we want
# equal, which will probably be the case for anything that can actually run backwards.

class CaseControl():
    def __init__(self,caller,procs,paramT,rsltT):
        self.caller = caller
        self.procs = procs
        self.paramT = paramT
        self.rsltT = rsltT
        self.cases = [OneCase(self,i,procs[i],paramT,rsltT).run() for i in range(len(procs))]

class FakeUpEt(I.Et):
    def __init__(self,oneCase):
        self.oneCase = oneCase
        self.ast = None
        self.up = None
        self.myChildId = None
        self.closR = None
        self.curType = T.mvtAny # :T.MtVal
    def run(self,rsltT):
        return self # what about rsltT FIXME
    def fromChild(self,childId,newType):
        assert False # FIXME

# This is the main code. The plan is that references to ids ' $' and ' `$' are shadowed along
# with everything that leads from them.
class FakeClosR(I.ClosureRun):
    def __init__(self,oneCase):
        self.oneCase = oneCase
        self.backPrimR = oneCase.caseControl.caller
        self.shadowParamT = I.shadow(oneCase.paramT)
        self.shadowRsltT = I.shadow(oneCase.rsltT)

class OneCase():
    def __init__(self,caseControl,myId,myProc,paramT,rsltT):
        self.caseControl = caseControl
        self.myId = myId
        self.myProc = myProc
        self.paramT = paramT
        self.rsltT = rsltT
        # do we really use the ast?
        caseAst = caseControl.caller.callEt.ast.procParam[1]
        self.fakeAst = A.AstCall(procParam=A.AstTuple(members=(caseAst[1].members[myId],caseAst[0])))
        self.fakeUp = FakeUpEt(self)
        self.fakeClosR = FakeClosR(self)
    def run(self):
        self.glet = gevent.spawn(I.EtCall,self.fakeAst,self.fakeUp,None,self.fakeClosR)

# fails because of import itself via mprimitive
#if __name__=="__main__":
#    pass
