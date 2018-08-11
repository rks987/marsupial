# mast.py supports the marsupial ast
#
import operator, functools

def ppFix(lines,indent): # squeeze to one line if convenient
    if sum((len(l)-indent) for l in lines) < 40:
        return [' '*indent+functools.reduce(operator.add,(l.lstrip().rstrip()+' ' for l in lines))]
    return lines

class AstNode:
    def __init__(self,parent=None,closure=None):
        self.parent = parent   # up a level
        self.closure = closure # closure we're in (None for top level)
        self.fixed = False
    def fixUp(self,parent,closure,upChain): # override if have subexpressions
        if self.fixed:
            pass #assert False
        self.fixed = True
        self.parent = parent
        self.closure = closure
        assert self not in upChain
        self.upChain = upChain
        #return self
    def gotClRslt(self):
        return False # default
    def __str__(self):
        assert False # must be overridden
    def pp(self,indent=1): # return a list of strings
        return [(' '*indent) + self.__str__()] # default

class AstTuple(AstNode):
    def __init__(self,members,parent=None,closure=None):
        self.members = (members,) if isinstance(members,AstNode) else members
        assert isinstance(members,tuple)
        super().__init__(parent,closure)
    def __str__(self):
        if self.members==(): return '()'
        rslt = '('
        for x in self.members: rslt = rslt+x.__str__()+','
        return rslt[:-1]+')'
    def gotClRslt(self):
        return any(e.gotClRslt() for e in self.members)
    def pp(self,indent=1): 
        if self.members==():
            return [(' '*indent)+'()']
        elif len(self.members)==1:
            return ppFix([(' '*indent)+'BOX('] + \
            self.members[0].pp(2+indent) + \
            [(' '*indent)+')' ],indent)
        else:
            mppl = [m.pp(indent+1) for m in self.members]
            for i in range(len(mppl)-1): mppl[i][-1] += ' ,'
            return ppFix([(' '*indent)+'('] + \
            functools.reduce(operator.add, mppl) + \
            [(' '*indent)+')'],indent)
    def fixUp(self,parent,closure,upChain):
        super().fixUp(parent,closure,upChain)
        for x in self.members: x.fixUp(self,closure,self.upChain+(self,))
        #return self

def zeroTuple():  # is Unit.unit = defaultOperand in wombat
    return AstTuple(members=()) 

#class AstDiscard(AstNode):
#    def __init__(self,parent=None,closure=None):
#        super().__init__(parent,closure)
#    def __str__(self):
#        print('_')

#def toDiscard(x):
#    return AstDiscard()

def toClosure(exprL): # param should be 1-elt list with closure expr as the 1 elt
    assert len(exprL)==1 and isinstance(exprL[0],AstNode)
    return AstClosure(expr=exprL[0])

class AstClosure(AstNode):
    def __init__(self,expr,parent=None,closure=None):
        super().__init__(parent,closure)
        self.expr = expr
        self.myIds = {}
        self.extIds = {}
        # need to make sure there is an AstClRslt
        if not self.expr.gotClRslt():
            # FIXME not the right way to do this, but ok for interp where equal is builtin
            eqProcParam = AstTuple((AstIdentifier("equal"),AstTuple((AstClRslt(),self.expr))))
            self.expr = AstCall(eqProcParam)
    def __str__(self):
        return '{'+self.expr.__str__()+'}'
    def pp(self,indent=1):
        return ppFix([' '*indent+'{'] + self.expr.pp(indent+2) + [(' '*indent)+'}'], indent)
    def fixUp(self,parent,closure,upChain):
        super().fixUp(parent,closure,upChain)
        self.expr.fixUp(self,self,upChain+(self,)) # I am up and closure
        for id in self.extIds:
            if id not in closure.extIds and id not in closure.myIds:
                closure.extIds[id] = [self]
            elif id in closure.extIds:
                closure.extIds[id].append(self)
            else:
                closure.myIds[id].append(self)
        pass #return self

class AstClParam(AstNode): # i.e. $
    def __init__(self,parent=None,closure=None):
        super().__init__(parent,closure)
    def __str__(self):
        return '$'

class AstClRslt(AstNode): # i.e. `$
    def __init__(self,parent=None,closure=None):
        super().__init__(parent,closure)
    def gotClRslt(self):
        return True
    def __str__(self): 
        return '`$'

class AstIdentifier(AstNode):
    def __init__(self,identifier,parent=None,closure=None):
        super().__init__(parent,closure)
        self.identifier = identifier
    def fixUp(self,parent,closure,upChain):
        super().fixUp(parent,closure,upChain)
        id = self.identifier
        if id in closure.myIds:
            closure.myIds[id].append(self) # no known use of this?
        else:
            if id not in closure.extIds:
                closure.extIds[id] = [self]
            else:
                closure.extIds[id].append(self)
    def __str__(self): 
        return self.identifier+' '

class AstNewIdentifier(AstNode):
    def __init__(self,identifier,parent=None,closure=None):
        super().__init__(parent,closure)
        self.identifier = identifier
    def fixUp(self,parent,closure,upChain):
        super().fixUp(parent,closure,upChain)
        id = self.identifier
        assert id not in closure.myIds #and id not in closure.extIds
        closure.myIds[id] = [self] # defining use is first in list
    def __str__(self): 
        return '`'+self.identifier+' '

class AstFreeVariable(AstNode):
    def __init__(self,identifier,parent=None,closure=None):
        super().__init__(parent,closure)
        self.identifier = identifier
    def __str__(self): 
        return '_'+self.identifier+' '

class AstNewFreeVariable(AstNode):
    def __init__(self,identifier,parent=None,closure=None):
        super().__init__(parent,closure)
        self.identifier = identifier
    def __str__(self):
        return '`_'+self.identifier+' '

class AstCall(AstNode):
    def __init__(self,procParam,parent=None,closure=None):
        super().__init__(parent,closure)
        self.procParam = procParam
    def __str__(self):
        return 'CALL'+self.procParam.__str__() # ugly
    def funct(self):
        return self.procParam.members[0]
    def param(self):
        return self.procParam.members[1]
    def pp(self,indent=1):
        f = self.funct().pp(indent)
        f[-1] += '('
        return ppFix(f+self.param().pp(indent+2)+[(' '*indent)+')'], indent)
    def fixUp(self,parent,closure,upChain):
        super().fixUp(parent,closure,upChain)
        self.procParam.fixUp(self,closure,self.upChain+(self,))
    def gotClRslt(self):
        return self.procParam.gotClRslt()

def callOp(procAndParam):
    return AstCall(procParam=AstTuple(members=procAndParam))

# These constants are really wombat not marsupial. FIXME
# maybe can be Mct"ConstType".fromString(const)
class AstConstant(AstNode):
    def __init__(self,const,constType,parent=None,closure=None):
        super().__init__(parent,closure)
        self.const = const
        self.constType = constType
    def __str__(self):
        return self.const+' ' # FIXME - only right for numbers

class AstPrim(AstNode):
    def __init__(self,primVal,parent=None,closure=None):
        super().__init__(parent,closure)
        self.primVal = primVal
    def __str__(self):
        return self.primVal.__str__()

def first2rest(tupNodeOrList):
    if tupNodeOrList == None: return None # for luck
    # commonly we have the 1st param seperated where it logically
    # belongs in with the list of following ones (e.g. comma operator)
    if isinstance(tupNodeOrList, AstTuple):
        return AstTuple(members=first2rest(tupNodeOrList.members))
    # assume is a 2 entry list whose 2nd entry is a list or AstTuple
    if isinstance(tupNodeOrList[1], AstTuple):
        return (tupNodeOrList[0],)+tupNodeOrList[1].members
    return (tupNodeOrList[0],)+tupNodeOrList[1]


if __name__=="__main__":
    pass
