from __future__ import annotations
from typing import Type

from ..qval import QOpt, QVar, IQOpt

from ..env import Expr, Env, expr_type_check


from .eqopt import EQOpt
from .eqvar import EQVar

import numpy as np


class EIQOpt(Expr):
    '''
    The Expression of Indexed Quantum Operators.
    
    EIQOpt ::= EQOpt EQVar

    Nonterminal.
    '''

    def __init__(self, qopt : Expr, qvar : Expr, env : Env):
        super().__init__(env)

        expr_type_check(qopt, QOpt)
        self._qopt = qopt

        expr_type_check(qvar, QVar)
        self._qvar = qvar


    ##################################
    # Expression settings

    @property
    def T(self) -> Type:
        return IQOpt
    
    def eval(self) -> object:
        return IQOpt(self._qopt.eval(), self._qvar.eval())    # type: ignore
    
    def __str__(self) -> str:
        return str(self._qopt) + str(self._qvar)
    ##################################