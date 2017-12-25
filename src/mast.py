# mast.py supports the marsupial ast
#
class AstNode:
    def __init__(self,parent=None,closure=None):
        self.parent = parent   # up a level
        self.closure = closure # closure we're in (None for top level)
    def fixUp(self,parent,closure): # override if have subexpressions
        self.parent = parent
        self.closure = closure
        #return self
    def __str__(self):
        assert False # must be overridden

class AstTuple(AstNode):
    def __init__(self,members,parent=None,closure=None):
        self.members = [members] if isinstance(members,AstNode) else members
        super().__init__(parent,closure)
    def __str__(self):
        if self.members==[]: return '()'
        rslt = '('
        for x in self.members: rslt = rslt+x.__str__()+','
        return rslt[:-1]+')'
    def fixUp(self,parent,closure):
        super().fixUp(parent,closure)
        for x in self.members: x.fixUp(self,closure)
        #return self

def zeroTuple():  # is Unit.unit = defaultOperand in wombat
    return AstTuple(members=[]) 

class AstDiscard(AstNode):
    def __init__(self,parent=None,closure=None):
        super().__init__(parent,closure)
    def __str__(self):
        print('_')

class AstClosure(AstNode):
    def __init__(self,expr,parent=None,closure=None):
        self.expr = expr
        super().__init__(parent,closure)
    def __str__(self):
        return '{'+self.expr.pp()+'}'
    def fixUp(self,parent,closure):
        super().fixUp(parent,closure)
        self.expr.fixUp(self,self) # I am up and closure
        #return self

class AstClParam(AstNode): # i.e. $
    def __init__(self,parent=None,closure=None):
        super().__init__(parent,closure)
    def __str__(self):
        return '$'

class AstClRslt(AstNode): # i.e. `$
    def __init__(self,parent=None,closure=None):
        super().__init__(parent,closure)
    def __str__(self): 
        return '`$'

class AstIdentifier(AstNode):
    def __init__(self,identifier,parent=None,closure=None):
        self.identifier = identifier
        super().__init__(parent,closure)
    def __str__(self): 
        return ' '+self.identifier+' '

class AstNewIdentifier(AstNode):
    def __init__(self,identifier,parent=None,closure=None):
        self.identifier = identifier
        super().__init__(parent,closure)
    def __str__(self): 
        return ' `'+self.identifier+' '

class AstFreeVariable(AstNode):
    def __init__(self,identifier,parent=None,closure=None):
        self.identifier = identifier
        super().__init__(parent,closure)
    def __str__(self): 
        return ' '+self.identifier+' '

class AstNewFreeVariable(AstNode):
    def __init__(self,identifier,parent=None,closure=None):
        self.identifier = identifier
        super().__init__(parent,closure)
    def __str__(self):
        return ' `'+self.identifier+' '

class AstCall(AstNode):
    def __init__(self,procParam,parent=None,closure=None):
        self.procParam = procParam
        super().__init__(parent,closure)
    def __str__(self):
        return 'CALL'+self.procParam.__str__() # ugly

def callOp(procAndParam):
    return AstCall(procParam=AstTuple(members=procAndParam))

class AstConstant(AstNode):
    def __init__(self,const,parent=None,closure=None):
        self.const = const
        super().__init__(parent,closure)
    def __str__(self):
        return ' '+self.const+' '

