from __future__ import annotations

from .term import *
from .metaproof import MetaProof

class Declaration:
    pass

    def __eq__(self, other : Declaration) -> bool:
        '''
        This is the syntactical equivalence.
        '''
        raise NotImplementedError()
    
    def __init__(self, x : Var, T : Term):
        CIC_SYS_type_check(x, Var)
        self.__x = x
        CIC_SYS_type_check(T, Term)
        self.__T = T

    @property
    def x(self) -> Var:
        return self.__x
    
    @property
    def T(self) -> Term:
        return self.__T

class VarDeclaration(Declaration):
    '''
    The declaration of a variable x
    '''
    
    def __str__(self) -> str:
        return "({} : {})".format(self.x, self.T)

class Typing(VarDeclaration):
    def __eq__(self, other: Declaration) -> bool:
        if not isinstance(other, Typing):
            return False
        return self.x == other.x and self.T == other.T

class Definition(VarDeclaration):
    def __init__(self, x : Var, t : Term, T : Term):
        super().__init__(x, T)
        CIC_SYS_type_check(t, Term)
        self.__t = t

    @property
    def t(self) -> Term:
        return self.__t
    
    def __str__(self) -> str:
        return "({} := {} : {})".format(self.x, self.t, self.T)
    
    def __eq__(self, other: Declaration) -> bool:
        if not isinstance(other, Definition):
            return False
        return self.x == other.x and self.t == other.t and self.T == other.T

##############################################################
# Local Context
###

class Context:
    def __init__(self, ls : Tuple[VarDeclaration, ...] = ()):
        CIC_SYS_type_check(ls, tuple)
        self.__ls = ls

    @property
    def ls(self) -> Tuple[VarDeclaration, ...]:
        return self.__ls
    
    def __eq__(self, other : Context):
        # this will reduce the complexity of comparing
        if self is other:
            return True
        else:
            # # for complexity reason, here we narrow the definition of `Γ1 == Γ2`
            # return False
            if not isinstance(other, Context):
                return False
            return self.ls == other.ls
        
    @property
    def is_empty(self) -> bool:
        return len(self.__ls) == 0

    def __str__(self) -> str:
        if len(self.__ls) == 0:
            return "[]"
        else:
            res = "[" + str(self.__ls[0])
            for i in range(1, len(self.__ls)):
                res += "; " + str(self.__ls[i])
            res += "]"
            return res
        
    def push(self, dec : VarDeclaration) -> Context:
        '''
        Corresponds to `Γ::(...)`
        '''
        return Context(self.__ls + (dec,))
    
    def pop(self) -> Tuple[Context, VarDeclaration]:
        if self.is_empty:
            raise CIC_SYS_Error("Cannot pop empty context.")
        return Context(self.__ls[:-1]), self.__ls[-1]
    

    def concatenate(self, other : Context) -> Context:
        '''
        Corresponds to the concatenation `Γ1; Γ2`
        '''
        return Context(self.__ls + other.__ls)
        

class MP_Cont_Not_Contain_Var(MetaProof):
    '''
    The proof object for `x ∉ Γ`.
    '''
    def __init__(self, var : Var, Gamma : Context):
        CIC_SYS_type_check(var, Var)
        CIC_SYS_type_check(Gamma, Context)

        for var_dec in Gamma.ls:
            if var_dec.x == var:
                raise CIC_SYS_Error("The variable '{}' is contained in the context.".format(var))
        
        self.__var = var
        self.__Gamma = Gamma

    @property
    def var(self) -> Var:
        return self.__var
    
    @property
    def Gamma(self) -> Context:
        return self.__Gamma
    
    def premises(self) -> str:
        return ""

    def conclusion(self) -> str:
        return "{} ∉ {}".format(self.var, self.Gamma)


class MP_Cont_Contain_Var(MetaProof):
    '''
    The proof object for `x ∈ Γ`.
    '''
    def __init__(self, var : Var, Gamma : Context):
        CIC_SYS_type_check(var, Var)
        CIC_SYS_type_check(Gamma, Context)

        contains = False
        for var_dec in Gamma.ls:
            if var_dec.x == var:
                contains = True
                break

        if not contains:
            raise CIC_SYS_Error("The variable '{}' is not contained in the context.".format(var))
        
        self.__var = var
        self.__Gamma = Gamma

    @property
    def var(self) -> Var:
        return self.__var
    
    @property
    def Gamma(self) -> Context:
        return self.__Gamma
    
    def premises(self) -> str:
        return ""

    def conclusion(self) -> str:
        return "{} ∈ {}".format(self.var, self.Gamma)


class MP_Cont_Contain_Typing(MetaProof):
    '''
    The proof object for `(x : T) ∈ Γ`.
    '''
    def __init__(self, var_typing : Typing, Gamma : Context):
        CIC_SYS_type_check(var_typing, Typing)
        CIC_SYS_type_check(Gamma, Context)

        contains = False
        for var_dec in Gamma.ls:
            if isinstance(var_dec, Typing):
                if var_dec == var_typing:
                    contains = True
                    break
            elif isinstance(var_dec, Definition):
                if var_dec.x == var_typing.x and var_dec.T == var_typing.T:
                    contains = True
                    break
            else:
                raise Exception()
                
        if not contains:
            raise CIC_SYS_Error("The typing '{}' is not contained in the context.".format(var_typing))
        
        self.__var_typing = var_typing
        self.__Gamma = Gamma

    @property
    def var_typing(self) -> Typing:
        return self.__var_typing
    
    @property
    def Gamma(self) -> Context:
        return self.__Gamma

    def premises(self) -> str:
        return ""

    def conclusion(self) -> str:
        return "{} ∈ {}".format(self.var_typing, self.Gamma)


class MP_Cont_Contain_Def(MetaProof):
    '''
    The proof object for `(x := t : T) ∈ Γ`.
    '''
    def __init__(self, var_def : Definition, Gamma : Context):
        CIC_SYS_type_check(var_def, Definition)
        CIC_SYS_type_check(Gamma, Context)

        if var_def not in Gamma.ls:
            raise CIC_SYS_Error("The definition '{}' is not contained in the context.".format(var_def))
        
        self.__var_def = var_def
        self.__Gamma = Gamma

    @property
    def var_def(self) -> Definition:
        return self.__var_def
    
    @property
    def Gamma(self) -> Context:
        return self.__Gamma

    def premises(self) -> str:
        return ""

    def conclusion(self) -> str:
        return "{} ∈ {}".format(self.var_def, self.Gamma)



##############################################################
# Global Environment
###

class Environment:
    def __init__(self, ls : Tuple[Declaration, ...] = ()):
        CIC_SYS_type_check(ls, tuple)
        self.__ls = ls

    @property
    def ls(self) -> Tuple[Declaration, ...]:
        return self.__ls
    
    def __eq__(self, other : Environment):
        # this will reduce the complexity of comparing
        if self is other:
            return True
        else:
            # # for complexity reason, here we narrow the definition of `E1 == E2`
            # return False
            if not isinstance(other, Environment):
                return False
            return self.ls == other.ls


    def __str__(self) -> str:
        if len(self.__ls) == 0:
            return "[]"
        else:
            res = "[" + str(self.__ls[0])
            for i in range(1, len(self.__ls)):
                res += "; " + str(self.__ls[i])
            res += "]"
            return res
        
    def push(self, dec : Declaration) -> Environment:
        '''
        Corresponds to `E; (...)`
        '''
        return Environment(self.__ls + (dec,))
    

class MP_Env_Not_Contain_Var(MetaProof):
    '''
    The proof object for `x ∉ E`.
    '''
    def __init__(self, var : Var, E : Environment):
        CIC_SYS_type_check(var, Var)
        CIC_SYS_type_check(E, Environment)

        for var_dec in E.ls:
            if var_dec.x == var:
                raise CIC_SYS_Error("The variable '{}' is contained in the environment.".format(var))
        
        self.__var = var
        self.__E = E

    @property
    def var(self) -> Var:
        return self.__var
    
    @property
    def E(self) -> Environment:
        return self.__E
    
    def premises(self) -> str:
        return ""

    def conclusion(self) -> str:
        return "{} ∉ {}".format(self.var, self.E)

class MP_Env_Contain_Var(MetaProof):
    '''
    The proof object for `x ∈ E`.
    '''
    def __init__(self, var : Var, E : Environment):
        CIC_SYS_type_check(var, Var)
        CIC_SYS_type_check(E, Environment)

        contains = False
        for var_dec in E.ls:
            if var_dec.x == var:
                contains = True
                break

        if not contains:
            raise CIC_SYS_Error("The variable '{}' is not contained in the environment.".format(var))
        
        self.__var = var
        self.__E = E

    @property
    def var(self) -> Var:
        return self.__var
    
    @property
    def E(self) -> Environment:
        return self.__E
    
    def premises(self) -> str:
        return ""

    def conclusion(self) -> str:
        return "{} ∈ {}".format(self.var, self.E)


class MP_Env_Contain_Typing(MetaProof):
    '''
    The proof object for `(x : T) ∈ E`.
    '''
    def __init__(self, var_typing : Typing, E : Environment):
        CIC_SYS_type_check(var_typing, Typing)
        CIC_SYS_type_check(E, Environment)

        contains = False
        for var_dec in E.ls:
            if isinstance(var_dec, Typing):
                if var_dec == var_typing:
                    contains = True
                    break
            elif isinstance(var_dec, Definition):
                if var_dec.x == var_typing.x and var_dec.T == var_typing.T:
                    contains = True
                    break
            else:
                raise Exception()
                
        if not contains:
            raise CIC_SYS_Error("The declaration '{}' is not contained in the environment.".format(var_typing))
        
        self.__var_typing = var_typing
        self.__E = E

    @property
    def var_typing(self) -> Typing:
        return self.__var_typing
    
    @property
    def E(self) -> Environment:
        return self.__E

    def premises(self) -> str:
        return ""

    def conclusion(self) -> str:
        return "{} ∈ {}".format(self.var_typing, self.E)