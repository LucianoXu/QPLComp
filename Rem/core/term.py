
from __future__ import annotations

from typing import Dict, Type, List, Tuple

from .error import *
from ..metaproof import MetaProof


#############################################################
# The definition for terms

class Term:

    def __eq__(self, other : Term) -> bool:
        '''
        This is the purely syntactical equivalence.
        '''
        raise NotImplementedError()

    def alpha_convertible(self, other : Term) -> bool:
        '''
        equivalence up to α-conversion

        Note: this method will inductively check whether two terms is α-convertible by an algorithm of unifying the bound variables.

        Reload this method for alpha-convertibility of extensions.
        '''
        raise NotImplementedError()

    def __str__(self) -> str:
        '''
        The printing of this term.
        '''
        raise NotImplementedError()
    
    def all_var(self) -> set[Var]:
        '''
        Return all the variables of the term `self` as a set.
        '''
        raise NotImplementedError()
    
    def free_var(self) -> set[Var]:
        '''
        Return the free variables of the term `self` as a set.
        '''
        raise NotImplementedError()
        
    
    def substitute(self, x : Var, t : Term) -> Term:
        '''
        Substitute the variable `x` with term `t` in the term `self`, and return the result.
        '''
        raise NotImplementedError()

############################
# The Sorts.
####

class Sort(Term):
    def __eq__(self, other : Term) -> bool:
        return isinstance(other, type(self))
    
    def alpha_convertible(self, other: Term) -> bool:
        return self == other
        
    def all_var(self) -> set[Var]:
        return set()

    def free_var(self) -> set[Var]:
        return set()

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
        return f"Type({self.i})"


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

    def alpha_convertible(self, other: Term) -> bool:
        return self == other

    def __str__(self) -> str:
        return self.name
    
    def all_var(self) -> set[Var]:
        return {self}

    def free_var(self) -> set[Var]:
        return {self}
        
    def substitute(self, x: Var, t: Term) -> Term:
        if self == x:
            return t
        else:
            return self
        
    count = 0
    @staticmethod
    def fresh_var(terms : Tuple[Term, ...]) -> Var:
        '''
        This staticmethod returns a fresh variable not in any of `terms`, based on `count`.
        '''
        var_set = set()
        for term in terms:
            var_set.update(term.all_var())

        name = f"#{Var.count}"
        while Var(name) in var_set:
            Var.count += 1
            name = f"#{Var.count}"

        return Var(name)
    

class Const(Term):
    def __init__(self, name : str):
        CIC_SYS_type_check(name, str)
        self.__name = name

    def __hash__(self) -> int:
        return self.__name.__hash__()
    
    @property
    def name(self) -> str:
        return self.__name
    
    def __eq__(self, other: Term) -> bool:
        if not isinstance(other, Const):
            return False
        
        return self.name == other.name
    
    def alpha_convertible(self, other: Term) -> bool:
        return self == other

    def __str__(self) -> str:
        return self.name
    
    def all_var(self) -> set[Var]:
        return set()

    def free_var(self) -> set[Var]:
        return set()
        
    def substitute(self, x: Var, t: Term) -> Term:
        return self
    
###############################################################
# Terms that contain a bound variable.
###

class BoundTerm(Term):
    def __init__(self, x : Var):
        # the bound variable
        CIC_SYS_type_check(x, Var)
        self.__x = x

    @property
    def x(self) -> Var:
        return self.__x
    
    def replace_bound(self, var : Var) -> BoundTerm:
        '''
        Replace the bound variable with a fresh `var` and return the result.
        Note: var should be fresh.
        '''
        raise NotImplementedError()


class Prod(BoundTerm):
    def __init__(self, x : Var, T : Term, U : Term):
        super().__init__(x)
        CIC_SYS_type_check(T, Term)
        self.__T = T
        CIC_SYS_type_check(U, Term)
        self.__U = U

    
    @property
    def T(self) -> Term:
        return self.__T
    
    @property
    def U(self) -> Term:
        return self.__U
    
    def __eq__(self, other: Term) -> bool:
        if not isinstance(other, Prod):
            return False
        if self is other:
            return True
        
        return self.x == other.x and self.T == other.T and self.U == other.U
    
    def alpha_convertible(self, other: Term) -> bool:
        if not isinstance(other, Prod):
            return False
        
        fresh_var = Var.fresh_var((self, other))
        self_rep = self.replace_bound(fresh_var)
        other_rep = other.replace_bound(fresh_var)
        
        return self_rep.T.alpha_convertible(other_rep.T) and self_rep.U.alpha_convertible(other_rep.U)
    
    def __str__(self) -> str:

        if self.x in self.U.free_var() or self.x in self.U.free_var():

            return f"forall {self.x}:{self.T}, {self.U}"
        
        else:

            return f"({self.T} -> {self.U})"

    def all_var(self) -> set[Var]:
        return self.T.all_var() | self.U.all_var() | {self.x}
    
    def free_var(self) -> set[Var]:
        return (self.T.free_var() | self.U.free_var()) - {self.x}
    
    def substitute(self, x: Var, t: Term) -> Term:
        '''
        Note: Substitutions in such terms:
        ```
            forall (x : x), ...
        ```
        is invalid and will not be considered.
        '''

        if x != self.x:
            T_sub = self.T.substitute(x, t)
            U_sub = self.U.substitute(x, t)
            return Prod(self.x, T_sub, U_sub)
        else:
            return self
        
    def replace_bound(self, var : Var) -> Prod:
        # security check. necessary?
        # if var in self.free_var():
        #     raise CIC_SYS_Error(f"Invalid bound replacement: variable '{var}' is free in '{self}'.")
        
        return Prod(var, self.T.substitute(self.x, var), self.U.substitute(self.x, var))
        

class Abstract(BoundTerm):
    def __init__(self, x : Var, T : Term, u : Term):
        super().__init__(x)
        CIC_SYS_type_check(T, Term)
        self.__T = T
        CIC_SYS_type_check(u, Term)
        self.__u = u
    
    @property
    def T(self) -> Term:
        return self.__T
    
    @property
    def u(self) -> Term:
        return self.__u
    
    def __eq__(self, other: Term) -> bool:
        if not isinstance(other, Abstract):
            return False
        if self is other:
            return True
        
        return self.x == other.x and self.T == other.T and self.u == other.u

    def alpha_convertible(self, other: Term) -> bool:
        if not isinstance(other, Abstract):
            return False
        
        fresh_var = Var.fresh_var((self, other))
        self_rep = self.replace_bound(fresh_var)
        other_rep = other.replace_bound(fresh_var)
        
        return self_rep.T.alpha_convertible(other_rep.T) and self_rep.u.alpha_convertible(other_rep.u)

    def __str__(self) -> str:
        return f"fun({self.x}:{self.T})=>{self.u}"
    
    def all_var(self) -> set[Var]:
        return self.T.all_var() | self.u.all_var() | {self.x}

    def free_var(self) -> set[Var]:
        return (self.T.free_var() | self.u.free_var()) - {self.x}

    def substitute(self, x: Var, t: Term) -> Term:
        '''
        Note: the occurrence of `x` in `T` are similar to the situation in `Prod`.
        '''

        if x != self.x:
            T_sub = self.T.substitute(x, t)
            u_sub = self.u.substitute(x, t)
            return Prod(self.x, T_sub, u_sub)
        else:
            return self
        
    def replace_bound(self, var : Var) -> Abstract:
        return Abstract(var, self.T.substitute(self.x, var), self.u.substitute(self.x, var))
        



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
        if self is other:
            return True
        
        return self.t == other.t and self.u == other.u
    
    def alpha_convertible(self, other: Term) -> bool:
        if not isinstance(other, Apply):
            return False
        return self.t.alpha_convertible(other.t) and self.u.alpha_convertible(other.u)

    def __str__(self) -> str:
        return f"({self.t} {self.u})"
    
    def all_var(self) -> set[Var]:
        return self.t.all_var() | self.u.all_var()

    def free_var(self) -> set[Var]:
        return self.t.free_var() | self.u.free_var()
    
    def substitute(self, x: Var, t: Term) -> Term:
        return Apply(self.t.substitute(x, t), self.u.substitute(x, t))
    

    
class Let_in(BoundTerm):
    def __init__(self, x : Var, t : Term, T : Term, u : Term):
        super().__init__(x)
        CIC_SYS_type_check(t, Term)
        self.__t = t
        CIC_SYS_type_check(T, Term)
        self.__T = T
        CIC_SYS_type_check(u, Term)
        self.__u = u

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
        if self is other:
            return True
        
        return self.x == other.x and self.t == other.t and self.T == other.T and self.u == other.u

    def alpha_convertible(self, other: Term) -> bool:
        if not isinstance(other, Let_in):
            return False
        
        fresh_var = Var.fresh_var((self, other))
        self_rep = self.replace_bound(fresh_var)
        other_rep = other.replace_bound(fresh_var)

        return self_rep.t.alpha_convertible(other_rep.t) and self_rep.T.alpha_convertible(other_rep.T) and self.u.alpha_convertible(other_rep.u)

    def __str__(self) -> str:
        return f"let {self.x}:={self.t}:{self.T} in {self.u}"
    
    def all_var(self) -> set[Var]:
        return self.t.all_var() | self.T.all_var() | self.u.all_var() | {self.x}

    def free_var(self) -> set[Var]:
        return (self.t.free_var() | self.T.free_var() | self.u.free_var()) - {self.x}
    
    def substitute(self, x: Var, t: Term) -> Term:
        if x != self.x:
            t_sub = self.t.substitute(x, t)
            T_sub = self.T.substitute(x, t)
            u_sub = self.u.substitute(x, t)
            return Let_in(self.x, t_sub, T_sub, u_sub)
        else:
            return self

    def replace_bound(self, var : Var) -> Let_in:
        return Let_in(var, self.t.substitute(self.x, var), self.T.substitute(self.x, var), self.u.substitute(self.x, var))
        



#####################################################################
# Meta proof objects
###


class MP_IsSort(MetaProof):
    '''
    The proof for `s ∈ S`.
    '''
    def __init__(self, s : Term):
        CIC_SYS_type_check(s, Term)
        self.__s = s

        if not isinstance(s, Sort):
            raise CIC_SYS_Error(f"The term '{self.__s}' is not a sort.")
        
    @property
    def s(self) -> Term:
        return self.__s
    
    def premises(self) -> str:
        return ""
    
    def conclusion(self) -> str:
        return f"{self.s} ∈ S"

