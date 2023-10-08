
from typing import Type

from ..sugar import type_check

from ..qval import QVar
from ..env import Expr, Env

class EQVar(Expr):
    '''
    The expression for a literal quantum variable.

    Terminal.
    '''
    def __init__(self, qvar : QVar, env : Env):
        super().__init__(env)

        type_check(qvar, QVar)
        self._qvar = qvar

    
    ##################################
    # Expression settings

    @property
    def T(self) -> Type:
        return QVar
    
    def eval(self) -> object:
        return self._qvar
    
    def __str__(self) -> str:
        return str(self._qvar)
    
    ##################################