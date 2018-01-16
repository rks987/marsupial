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
    def pp(self,indent):
        if indent>0: print('\n'+(' '*indent))
        print(self.__str__())

class AstTuple(AstNode):
    def __init__(self,members,parent=None,closure=None):
        self.members = [members] if isinstance(members,AstNode) else members
        super().__init__(parent,closure)
    def __str__(self):
        if self.members==[]: return '()'
        rslt = '('
        for x in self.members: rslt = rslt+x.__str__()+','
        return rslt[:-1]+')'
    def pp(self,indent):
        if indent>0: print('\n'+(' '*indent))
        if self.members==[]:
            print('()')
        elif len(self.members)==1:
            print('BOX(')
            self.members[0].pp(-abs(indent))
            print(')')
        else:
            print('(')
            for m in self.members: m.pp(abs(indent)+1)
            print('\n'+(' '*abs(indent))+')')
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

def toDiscard(x):
    return AstDiscard()

def toClosure(exprL): # param should be 1-elt list with closure expr as the 1 elt
    assert len(exprL)==1 and isinstance(exprL[0],AstNode)
    return AstClosure(expr=exprL[0])

class AstClosure(AstNode):
    def __init__(self,expr,parent=None,closure=None):
        self.expr = expr
        super().__init__(parent,closure)
    def __str__(self):
        return '{'+self.expr.__str__()+'}'
    def pp(self,indent):
        if indent>0: print('\n'+(' '*indent))
        print('{')
        self.expr.pp(indent+2 if indent>=0 else -indent+2)
        print('\n'+(' '*abs(indent))+'}')
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
        return ' _'+self.identifier+' '

class AstNewFreeVariable(AstNode):
    def __init__(self,identifier,parent=None,closure=None):
        self.identifier = identifier
        super().__init__(parent,closure)
    def __str__(self):
        return ' `_'+self.identifier+' '

class AstCall(AstNode):
    def __init__(self,procParam,parent=None,closure=None):
        self.procParam = procParam
        super().__init__(parent,closure)
    def __str__(self):
        return 'CALL'+self.procParam.__str__() # ugly
    def funct(self):
        return self.procParam.members[0]
    def param(self):
        return self.procParam.members[1]
    def pp(self,indent):
        self.funct().pp(indent)
        print('\n  '+(' '*abs(indent)))
        self.param().pp(-(abs(indent)+2))
        print(')')
    def fixUp(self,parent,closure):
        super().fixUp(parent,closure)
        self.procParam.fixUp(self,closure)

def callOp(procAndParam):
    return AstCall(procParam=AstTuple(members=procAndParam))

# These constants are really wombat not marsupial. FIXME
# maybe can be Mct"ConstType".fromString(const)
class AstConstant(AstNode):
    def __init__(self,const,constType,parent=None,closure=None):
        self.const = const
        self.constType = constType
        super().__init__(parent,closure)
    def __str__(self):
        return ' '+self.const+' '

def first2rest(tupNodeOrList):
    if tupNodeOrList == None: return None # for luck
    # commonly we have the 1st param seperated where it logically
    # belongs in with the list of following ones (e.g. comma operator)
    if isinstance(tupNodeOrList, AstTuple):
        return AstTuple(members=first2rest(tupNodeOrList.members))
    # assume is a 2 entry list whose 2nd entry is a list or AstTuple
    if isinstance(tupNodeOrList[1], AstTuple):
        return [tupNodeOrList[0]]+tupNodeOrList[1].members
    return [tupNodeOrList[0]]+tupNodeOrList[1]
