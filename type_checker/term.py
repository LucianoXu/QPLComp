
from __future__ import annotations

from typing import Dict, Type, List

from .error import *
from .metaproof import MetaProof


#############################################################
# The definition for terms

class Term:

    def __eq__(self, other : Term) -> bool:
        '''
        This is the purely syntactical equivalence.
        '''
        raise NotImplementedError()

    def __str__(self) -> str:
        '''
        The printing of this term.
        '''
        raise NotImplementedError()
        
    
    def substitute(self, x : Var, t : Term) -> Term:
        '''
        Substitute the variable `x` with term `t` in the term `self`, and return the result.
        '''
        raise NotImplementedError()
    

    def dependent(self, x : Var) -> bool:
        '''
        Checks whether term `self` is dependent on the variable `x`.
        '''
        raise NotImplementedError()

############################
# The Sorts.
####

class Sort(Term):
    def __eq__(self, other : Term) -> bool:
        return isinstance(other, type(self))

    def substitute(self, x : Var, t : Term) -> Term:
        return self
    
    def dependent(self, x: Var) -> bool:
        return False

class SProp(Sort):
    def __str__(self) -> str:
        return "SProp"

class Prop(Sort):
    def __str__(self) -> str:
        return "Prop"

class Set(Sort):
    def __str__(self) -> str:
        return "Set"
        
class Type_i(Sort):
    def __init__(self, i : int):
        CIC_SYS_type_check(i, int)
        if i <= 0:
            raise CIC_SYS_Error("Invalid universe number.")
        self.__i = i

    @property
    def i(self) -> int:
        return self.__i
    
    def __eq__(self, other : Term) -> bool:
        if not isinstance(other, Type_i):
            return False
        
        return self.i == other.i
    
    def __str__(self) -> str:
        return "Type({})".format(self.i)


class MP_IsSort(MetaProof):
    '''
    The proof for `s ∈ S`.
    '''
    def __init__(self, s : Term):
        CIC_SYS_type_check(s, Term)
        self.__s = s

        if not isinstance(s, Sort):
            raise CIC_SYS_Error("The term '{}' is not a sort.".format(self.__s))
        
    @property
    def s(self) -> Term:
        return self.__s
    
    def premises(self) -> str:
        return ""
    
    def conclusion(self) -> str:
        return "{} ∈ S".format(self.s)


############################
# Other term constructions.
###

class Var(Term):
    def __init__(self, name : str):
        CIC_SYS_type_check(name, str)
        self.__name = name

    def __hash__(self) -> int:
        return self.__name.__hash__()
    
    @property
    def name(self) -> str:
        return self.__name
    
    def __eq__(self, other: Term) -> bool:
        if not isinstance(other, Var):
            return False
        
        return self.name == other.name

    def __str__(self) -> str:
        return self.name
        
    def substitute(self, x: Var, t: Term) -> Term:
        if self == x:
            return t
        else:
            return self
        
    def dependent(self, x: Var) -> bool:
        return self == x
    

class Const(Term):
    def __init__(self, data : object):
        self.__data = data

    @property
    def data(self) -> object:
        return self.__data
    
    def __eq__(self, other: Term) -> bool:
        if not isinstance(other, Const):
            return False
        
        return self.data == other.data
    
    def __str__(self) -> str:
        return str(self.data)
        
    def substitute(self, x: Var, t: Term) -> Term:
        return self
    
    def dependent(self, x: Var) -> bool:
        return False

class Prod(Term):
    def __init__(self, x : Var, T : Term, U : Term):
        CIC_SYS_type_check(x, Var)
        self.__x = x
        CIC_SYS_type_check(T, Term)
        self.__T = T
        CIC_SYS_type_check(U, Term)
        self.__U = U

    @property
    def x(self) -> Var:
        return self.__x
    
    @property
    def T(self) -> Term:
        return self.__T
    
    @property
    def U(self) -> Term:
        return self.__U
    
    def __eq__(self, other: Term) -> bool:
        if not isinstance(other, Prod):
            return False
        
        return self.x == other.x and self.T == other.T and self.U == other.U
    
    def __str__(self) -> str:

        if self.U.dependent(self.x):

            return "forall {}:{}, {}".format(self.x, self.T, self.U)
        
        else:

            return "({} -> {})".format(self.T, self.U)
    
    def substitute(self, x: Var, t: Term) -> Term:
        '''
        Note: the occurrence in `T` are always free, even for such terms:
        ```
            forall (x : x), ...
        ```
        '''
        T_sub = self.T.substitute(x, t)
        if x != self.x:
            U_sub = self.U.substitute(x, t)
        else:
            U_sub = self.U

        return Prod(self.x, T_sub, U_sub)
    
    def dependent(self, x: Var) -> bool:
        return self.T.dependent(x) or (self.U.dependent(x) and x != self.x)
        

class Abstract(Term):
    def __init__(self, x : Var, T : Term, u : Term):
        CIC_SYS_type_check(x, Var)
        self.__x = x
        CIC_SYS_type_check(T, Term)
        self.__T = T
        CIC_SYS_type_check(u, Term)
        self.__u = u

    @property
    def x(self) -> Var:
        return self.__x
    
    @property
    def T(self) -> Term:
        return self.__T
    
    @property
    def u(self) -> Term:
        return self.__u
    
    def __eq__(self, other: Term) -> bool:
        if not isinstance(other, Abstract):
            return False
        
        return self.x == other.x and self.T == other.T and self.u == other.u
    
    def __str__(self) -> str:
        return "fun({}:{})=>{}".format(self.x, self.T, self.u)


    def substitute(self, x: Var, t: Term) -> Term:
        '''
        Note: the occurrence in `T` are always free, similar to `Prod`.
        '''

        T_sub = self.T.substitute(x, t)
        if x != self.x:
            u_sub = self.u.substitute(x, t)
        else:
            u_sub = self.u

        return Prod(self.x, T_sub, u_sub)

    def dependent(self, x: Var) -> bool:
        return self.T.dependent(x) or (self.u.dependent(x) and x != self.x)

class Apply(Term):
    def __init__(self, t : Term, u : Term):
        CIC_SYS_type_check(t, Term)
        self.__t = t
        CIC_SYS_type_check(u, Term)
        self.__u = u

    @property
    def t(self) -> Term:
        return self.__t
    
    @property
    def u(self) -> Term:
        return self.__u
    
    def __eq__(self, other: Term) -> bool:
        if not isinstance(other, Apply):
            return False
        
        return self.t == other.t and self.u == other.u
    
    def __str__(self) -> str:
        return "({} {})".format(self.t, self.u)
    
    def substitute(self, x: Var, t: Term) -> Term:
        return Apply(self.t.substitute(x, t), self.u.substitute(x, t))
    
    def dependent(self, x: Var) -> bool:
        return self.t.dependent(x) or self.u.dependent(x)

    
class Let_in(Term):
    def __init__(self, x : Var, t : Term, T : Term, u : Term):
        CIC_SYS_type_check(x, Var)
        self.__x = x
        CIC_SYS_type_check(t, Term)
        self.__t = t
        CIC_SYS_type_check(T, Term)
        self.__T = T
        CIC_SYS_type_check(u, Term)
        self.__u = u

    @property
    def x(self) -> Var:
        return self.__x
    
    @property
    def t(self) -> Term:
        return self.__t
    
    @property
    def T(self) -> Term:
        return self.__T
    
    @property
    def u(self) -> Term:
        return self.__u
    
    def __eq__(self, other: Term) -> bool:
        if not isinstance(other, Let_in):
            return False
        
        return self.x == other.x and self.t == other.t and self.T == other.T and self.u == other.u
    
    def __str__(self) -> str:
        return "let {}:={}:{} in {}".format(self.x, self.t, self.T, self.u)
    
    def substitute(self, x: Var, t: Term) -> Term:
        t_sub = self.t.substitute(x, t)
        T_sub = self.T.substitute(x, t)
        if x != self.x:
            u_sub = self.u.substitute(x, t)
        else:
            u_sub = self.u

        return Let_in(self.x, t_sub, T_sub, u_sub)
    
    def dependent(self, x: Var) -> bool:
        return self.t.dependent(x) or self.T.dependent(x) or (self.u.dependent(x) and x != self.x)
