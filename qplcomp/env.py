'''
env
=====

This package provides a simple variable system. It includes:

- class `Expr`: the typed expressions of the system. More specific definition of expressions should be defined as its subclasses.
- class `Variable`: It is the expression constructed by a variable.
- class `Env`: environments for the variable system. It is a dictionary from identifiers (`str`) to its definitions (`Expr`).

'''

from __future__ import annotations

from typing import Dict, Type

DEFAULT_PREFIX = "VAL"

# TODO : type information needed.

class Expr:
    '''
    The class for expressions.
    The type checking is implemented in the construction of Expr.
    '''

    def __init__(self, env : Env):
        '''
        parameter env: ever expression lives in some particular environment.

        TODO #2
        '''
        self._env = env
    
    @property
    def T(self) -> None | Type:
        raise NotImplementedError()
    
    def eval(self) -> object:
        '''
        Calculate the value of this varible within the environment.

        Note: this is going to be a complete calculation, which is different from partial reductions.
        '''
        raise NotImplementedError()
    
    def __str__(self) -> str:
        raise NotImplementedError()
    
class Variable(Expr):
    '''
    The class for variables. Variables can be of any type, and can be replaced by alpha-reduction.
    '''
    def __init__(self, id : str, env : Env, T : None | Type = None):
        '''
        Construct a Variable expression.

        The type of it can be `None`, meaning that it's type is not determined yet.
        '''
        super().__init__(env)

        if not isinstance(id, str):
            raise TypeError("The id should be a string.")
        if not isinstance(T, Type) and T is not None:
            raise TypeError("The type T should be a Type or the None object.")
        
        self._id = id
        self._T = T

    
    @property
    def T(self) -> None | Type:
        if self._T is not None:
            return self._T
        
        elif self._id in self._env:
            return self._env[self._id].T
        
        else:
            return None

    def eval(self):
        val = self._env[self._id].eval()

        if self.T is not None:
            if not isinstance(val, self.T):
                raise TypeError("The variable '" + self._id + "' should be of type '" + str(self.T) + "', but the value defined in the environment is of type '" + str(type(val)) + "'.")
        
        return val
    
    def __str__(self) -> str:
        return self._id



def expr_type_check(expr : Expr, target_type : Type) -> None:
    '''
    The method to check the type of this expression. It will raise a TypeError if the type of expr is not target_type.
    '''
    if expr.T is not None and expr.T != target_type:
        raise TypeError("[ENV] The parameter expression '" + str(expr) + "' should be of type '" + str(target_type) + "', but is of type '"+ str(expr.T) + "'.")

class Env:
    '''
    The environment relates variable (string) to their definitions.
    '''
    def __init__(self) -> None:
        '''
        Initializing an empty value environment.
        '''
        self._lib : Dict[str, Expr] = {}

        # the number for auto naming
        self._numbering = 0

    def get_name(self, prefix : str = DEFAULT_PREFIX) -> str:
        '''
        Return a key which is not used in the environment. The key will be in the form of `prefix` + number.

        Parameters: prefix = "VAL" : str.
        Returns: a key which is not used in this environment.
        '''
        res = prefix + str(self._numbering)
        self._numbering += 1
        while res in self._lib:
            res = prefix + str(self._numbering)
            self._numbering += 1
        return res


    def append(self, expr : Expr) -> str:
        '''
        Check whether the value already exists in this environment.
        If yes, return the corresponding key.
        If not, create a new item with an auto key and return the key used.
        '''
        if not isinstance(expr, Expr):
            raise ValueError("Invalid value. Only Expr instances are allowed.")
        
        for key in self._lib:
            if self._lib[key] == expr:
                return key
            
        name = self.get_name()
        self._lib[name] = expr
        return name
    
    def __setitem__(self, key : str, expr : Expr) -> None:
        if not isinstance(expr, Expr):
            raise ValueError("Invalid value. Only quantum values are allowed.")
        self._lib[key] = expr

    def __getitem__(self, key : str) -> Expr:
        return self._lib[key]
    
    def __contains__(self, key : str) -> bool:
        return key in self._lib