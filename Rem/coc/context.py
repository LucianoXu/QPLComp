'''

See (https://coq.inria.fr/refman/language/cic.html#global-environment).

'''

from __future__ import annotations

from .term import *
from ..metadef import MetaProof

@meta_term
class LocalDec(MetaTerm):
    '''
    local-dec
    ```
    _
    ```
    '''

    def __eq__(self, other : LocalDec) -> bool:
        '''
        This is the syntactical equivalence.
        '''
        raise NotImplementedError()
    
    def __init__(self, x : Var, T : Term):
        Meta_Sys_type_check(x, Var)
        self.__x = x
        Meta_Sys_type_check(T, Term)
        self.__T = T

    @property
    def x(self) -> Var:
        return self.__x
    
    @property
    def T(self) -> Term:
        return self.__T

@concrete_term
class LocalTyping(LocalDec):
    '''
    local-assum
    ```
    x : T
    ```
    '''

    def __eq__(self, other: LocalDec) -> bool:
        if not isinstance(other, LocalTyping):
            return False
        return self.x == other.x and self.T == other.T
    
    def __str__(self) -> str:
        return f"({self.x} : {self.T})"

@concrete_term
class LocalDef(LocalDec):
    '''
    local-def
    ```
    x := t : T
    ```
    '''

    def __init__(self, x : Var, t : Term, T : Term):
        super().__init__(x, T)
        Meta_Sys_type_check(t, Term)
        self.__t = t

    @property
    def t(self) -> Term:
        return self.__t
    
    def __eq__(self, other: LocalDec) -> bool:
        if not isinstance(other, LocalDef):
            return False
        return self.x == other.x and self.t == other.t and self.T == other.T
    
    def __str__(self) -> str:
        return f"({self.x} := {self.t} : {self.T})"
    

##############################################################
# Local Context
###

@concrete_term
class Context(MetaTerm):
    '''
    context
    ```
    _
    ```
    '''

    def __init__(self, ls : Tuple[LocalDec, ...] = ()):
        Meta_Sys_type_check(ls, tuple)
        self.__ls = ls

    @property
    def ls(self) -> Tuple[LocalDec, ...]:
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
        
    def push(self, dec : LocalDec) -> Context:
        '''
        Corresponds to `Γ::(...)`
        '''
        return Context(self.__ls + (dec,))
    
    def pop(self) -> Tuple[Context, LocalDec]:
        if self.is_empty:
            raise Meta_Sys_Error("Cannot pop empty context.")
        return Context(self.__ls[:-1]), self.__ls[-1]
    

    def concatenate(self, other : Context) -> Context:
        '''
        Corresponds to the concatenation `Γ1; Γ2`
        '''
        return Context(self.__ls + other.__ls)
        

@concrete_term
class MP_Cont_Not_Contain_Var(MetaProof):
    '''
    no-in-local
    ```
    x ∉ Γ
    ```
    The proof object for `x ∉ Γ`.
    '''

    def __init__(self, var : Var, Gamma : Context):
        Meta_Sys_type_check(var, Var)
        Meta_Sys_type_check(Gamma, Context)

        for var_dec in Gamma.ls:
            if var_dec.x == var:
                raise Meta_Sys_Error(f"The variable '{var}' is contained in the context.")
        
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
        return f"{self.var} ∉ {self.Gamma}"


@concrete_term
class MP_Cont_Contain_Var(MetaProof):
    '''
    var-in-local
    ```
    x ∈ Γ
    ```
    The proof object for `x ∈ Γ`.
    '''

    def __init__(self, var : Var, Gamma : Context):
        Meta_Sys_type_check(var, Var)
        Meta_Sys_type_check(Gamma, Context)

        contains = False
        for var_dec in Gamma.ls:
            if var_dec.x == var:
                contains = True
                break

        if not contains:
            raise Meta_Sys_Error(f"The variable '{var}' is not contained in the context.")
        
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
        return f"{self.var} ∈ {self.Gamma}"


@concrete_term
class MP_Cont_Contain_Typing(MetaProof):
    '''
    assum-in-local
    ```
    (x : T) ∈ Γ
    ```
    The proof object for `(x : T) ∈ Γ`.
    '''

    def __init__(self, var_typing : LocalTyping, Gamma : Context):
        Meta_Sys_type_check(var_typing, LocalTyping)
        Meta_Sys_type_check(Gamma, Context)

        contains = False
        for var_dec in Gamma.ls:
            if isinstance(var_dec, LocalTyping):
                if var_dec == var_typing:
                    contains = True
                    break
            elif isinstance(var_dec, LocalDef):
                if var_dec.x == var_typing.x and var_dec.T == var_typing.T:
                    contains = True
                    break
            else:
                raise Exception()
                
        if not contains:
            raise Meta_Sys_Error(f"The typing '{var_typing}' is not contained in the context.")
        
        self.__var_typing = var_typing
        self.__Gamma = Gamma

    @property
    def var_typing(self) -> LocalTyping:
        return self.__var_typing
    
    @property
    def Gamma(self) -> Context:
        return self.__Gamma

    def premises(self) -> str:
        return ""

    def conclusion(self) -> str:
        return f"{self.var_typing} ∈ {self.Gamma}"

@concrete_term
class MP_Cont_Contain_Def(MetaProof):
    '''
    def-in-local
    ```
    (x := t : T) ∈ Γ
    ```
    The proof object for `(x := t : T) ∈ Γ`.
    '''
    
    def __init__(self, var_def : LocalDef, Gamma : Context):
        Meta_Sys_type_check(var_def, LocalDef)
        Meta_Sys_type_check(Gamma, Context)

        if var_def not in Gamma.ls:
            raise Meta_Sys_Error(f"The definition '{var_def}' is not contained in the context.")
        
        self.__var_def = var_def
        self.__Gamma = Gamma

    @property
    def var_def(self) -> LocalDef:
        return self.__var_def
    
    @property
    def Gamma(self) -> Context:
        return self.__Gamma

    def premises(self) -> str:
        return ""

    def conclusion(self) -> str:
        return f"{self.var_def} ∈ {self.Gamma}"
