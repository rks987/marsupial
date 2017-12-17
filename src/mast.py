# mast.py supports the marsupial ast
#
class AstNode:
    def __init__(self,parent=None,closure=None):
        self.parent = parent   # up a level
        self.closure = closure # closure we're in (None for top level)
    def setUp(parent,closure):
        self.parent = parent
        self.closure = closure
    def pp(self):
        assert False # must be overridden

class AstTuple(AstNode):
    def __init__(self,members,parent=None,closure=None):
        self.members = members
        super().__init__(parent,closure)
    def pp(self):
        print('(')
        for x in self.members: x.pp()
        print(')')

def zeroTuple(parent,closure):  # is Unit.unit = defaultOperand in wombat
    return AstTuple(parent=parent,closure=closure,members=[]) 

class AstDiscard(AstNode):
    def __init__(self,parent=None,closure=None):
        super().__init__(parent,closure)
    def pp(self):
        print('_')

class AstClosure(AstNode):
    def __init__(self,expr,parent=None,closure=None):
        self.expr = expr
        super().__init__(parent,closure)
    def pp(self):
        print('{')
        self.expr.pp()
        print('}')

class AstClParam(AstNode): # i.e. $
    def __init__(self,parent=None,closure=None):
        super().__init__(parent,closure)
    def pp(self): print('$')

class AstClRslt(AstNode): # i.e. `$
    def __init__(self,parent=None,closure=None):
        super().__init__(parent,closure)
    def pp(self): print('`$')

class AstIdentifier(AstNode):
    def __init__(self,identifier,parent=None,closure=None):
        self.identifier = identifier
        super().__init__(parent,closure)
    def pp(self): print(self.identifier, ' ')

class AstNewIdentifier(AstNode):
    def __init__(self,identifier,parent=None,closure=None):
        self.identifier = identifier
        super().__init__(parent,closure)
    def pp(self): print('`',self.identifier,' ')

class AstFreeVariable(AstNode):
    def __init__(self,identifier,parent=None,closure=None):
        self.identifier = identifier
        super().__init__(parent,closure)
    def pp(self): print(self.identifier, ' ')

class AstNewFreeVariable(AstNode):
    def __init__(self,identifier,parent=None,closure=None):
        self.identifier = identifier
        super().__init__(parent,closure)
    def pp(self): print('`',self.identifier,' ')

class AstCall(AstNode):
    def __init__(self,procParam,parent=None,closure=None):
        self.procParam = procParam
        super().__init__(parent,closure)
    def pp(self):
        pass #FIXME

class AstConstant(AstNode):
    def __init__(self,const,parent=None,closure=None):
        self.const = const
        super().__init__(parent,closure)
    def pp(self):
        pass # FIXME

