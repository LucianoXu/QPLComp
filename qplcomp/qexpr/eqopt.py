from __future__ import annotations
from typing import Type

from ..sugar import type_check
from ..env import Expr, Env

from ..qval import QOpt


import numpy as np


class EQOpt(Expr):
    '''
    The expression for Quantum Operators.

    Terminal.
    '''

    def __init__(self, qopt : QOpt, env : Env):
        super().__init__(env)

        type_check(qopt, QOpt)
        self._qopt = qopt

    ##################################
    # Expression settings

    @property
    def T(self) -> Type:
        return QOpt
    
    def eval(self) -> object:
        return self._qopt
    
    def __str__(self) -> str:
        return str(self._qopt)
    
    ##################################