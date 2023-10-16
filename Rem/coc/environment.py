'''

See (https://coq.inria.fr/refman/language/cic.html#global-environment).

'''

from __future__ import annotations

from .term import *
from ..metadef import MetaProof


##############################################################
# Global Environment
###

@meta_term
class GlobalDec(MetaTerm):
    '''
    global-dec
    ```
    _
    ```
    '''
    def __eq__(self, other : GlobalDec) -> bool:
        '''
        This is the syntactical equivalence.
        '''
        raise NotImplementedError()
    
    def __init__(self, c : Const, T : Term):
        Meta_Sys_type_check(c, Const)
        self.__c = c
        Meta_Sys_type_check(T, Term)
        self.__T = T

    @property
    def c(self) -> Const:
        return self.__c
    
    @property
    def T(self) -> Term:
        return self.__T

@concrete_term
class GlobalTyping(GlobalDec):
    '''
    global-assum
    ```
    (c : T)
    ```
    '''

    def __eq__(self, other: GlobalDec) -> bool:
        if not isinstance(other, GlobalTyping):
            return False
        return self.c == other.c and self.T == other.T
    
    def __str__(self) -> str:
        return f"({self.c} : {self.T})"

@concrete_term
class GlobalDef(GlobalDec):
    '''
    global-def
    ```
    (c := t : T)
    ```
    '''

    def __init__(self, c : Const, t : Term, T : Term):
        super().__init__(c, T)
        Meta_Sys_type_check(t, Term)
        self.__t = t

    @property
    def t(self) -> Term:
        return self.__t
    
    def __eq__(self, other: GlobalDec) -> bool:
        if not isinstance(other, GlobalDef):
            return False
        return self.c == other.c and self.t == other.t and self.T == other.T
    
    def __str__(self) -> str:
        return f"({self.c} := {self.t} : {self.T})"
    

@concrete_term
class Environment(MetaTerm):
    '''
    global-environment
    ```
    _
    ```
    '''

    def __init__(self, ls : Tuple[GlobalDec, ...] = ()):
        Meta_Sys_type_check(ls, tuple)
        self.__ls = ls

    @property
    def ls(self) -> Tuple[GlobalDec, ...]:
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
        
    def push(self, dec : GlobalDec) -> Environment:
        '''
        Corresponds to `E; (...)`
        '''
        return Environment(self.__ls + (dec,))
    

@concrete_term
class MP_Env_Not_Contain_Const(MetaProof):
    '''
    no-in-global
    ```
    c ∉ E
    ```
    The proof object for `c ∉ E`.
    '''

    def __init__(self, const : Const, E : Environment):
        Meta_Sys_type_check(const, Const)
        Meta_Sys_type_check(E, Environment)

        for const_dec in E.ls:
            if const_dec.c == const:
                raise Meta_Sys_Error(f"The constant '{const}' is contained in the environment.")
        
        self.__const = const
        self.__E = E

    @property
    def const(self) -> Const:
        return self.__const
    
    @property
    def E(self) -> Environment:
        return self.__E
    
    def premises(self) -> str:
        return ""

    def conclusion(self) -> str:
        return f"{self.const} ∉ {self.E}"


@concrete_term
class MP_Env_Contain_Const(MetaProof):
    '''
    const-in-global
    ```
    c ∈ E
    ```
    The proof object for `c ∈ E`.
    '''

    def __init__(self, const : Const, E : Environment):
        Meta_Sys_type_check(const, Const)
        Meta_Sys_type_check(E, Environment)

        contains = False
        for const_dec in E.ls:
            if const_dec.c == const:
                contains = True
                break

        if not contains:
            raise Meta_Sys_Error(f"The constant '{const}' is not contained in the environment.")
        
        self.__const = const
        self.__E = E

    @property
    def const(self) -> Const:
        return self.__const
    
    @property
    def E(self) -> Environment:
        return self.__E
    
    def premises(self) -> str:
        return ""

    def conclusion(self) -> str:
        return f"{self.const} ∈ {self.E}"


@concrete_term
class MP_Env_Contain_Typing(MetaProof):
    '''
    assum-in-global
    ```
    (c : T) ∈ E
    ```
    The proof object for `(c : T) ∈ E`.
    '''

    def __init__(self, const_typing : GlobalTyping, E : Environment):
        Meta_Sys_type_check(const_typing, GlobalTyping)
        Meta_Sys_type_check(E, Environment)

        contains = False
        for const_dec in E.ls:
            if isinstance(const_dec, GlobalTyping):
                if const_dec == const_typing:
                    contains = True
                    break
            elif isinstance(const_dec, GlobalDef):
                if const_dec.c == const_typing.c and const_dec.T == const_typing.T:
                    contains = True
                    break
            else:
                raise Exception()
                
        if not contains:
            raise Meta_Sys_Error(f"The declaration '{const_typing}' is not contained in the environment.")
        
        self.__const_typing = const_typing
        self.__E = E

    @property
    def const_typing(self) -> GlobalTyping:
        return self.__const_typing
    
    @property
    def E(self) -> Environment:
        return self.__E

    def premises(self) -> str:
        return ""

    def conclusion(self) -> str:
        return f"{self.const_typing} ∈ {self.E}"
    

@concrete_term
class MP_Env_Contain_Def(MetaProof):
    '''
    def-in-global
    ```
    (c := t : T) ∈ E
    ```
    The proof object for `(c := t : T) ∈ E`.
    '''
    
    def __init__(self, const_def : GlobalDef, E : Environment):
        Meta_Sys_type_check(const_def, GlobalDef)
        Meta_Sys_type_check(E, Environment)

        if const_def not in E.ls:
            raise Meta_Sys_Error(f"The definition '{const_def}' is not contained in the environment.")
        
        self.__const_def = const_def
        self.__E = E

    @property
    def const_def(self) -> GlobalDef:
        return self.__const_def
    
    @property
    def E(self) -> Environment:
        return self.__E

    def premises(self) -> str:
        return ""

    def conclusion(self) -> str:
        return f"{self.const_def} ∈ {self.E}"
