from __future__ import annotations
from typing import Type

from ..sugar import type_check
from ..env import Expr, Env, expr_type_check

from ..qval import QSOpt


import numpy as np


class EQSOpt(Expr):
    '''
    The expression for Quantum Super Operators.

    Terminal.
    '''

    def __init__(self, qso : QSOpt, env : Env):
        super().__init__(env)

        type_check(qso, QSOpt)
        self._qso = qso


    ##################################
    # Expression settings

    @property
    def T(self) -> Type:
        return QSOpt
    
    def eval(self) -> object:
        return self._qso
    
    def __str__(self) -> str:
        return str(self._qso)
    
    ##################################



class EQSOptAdd(Expr):
    '''
    The expression for additions of quantum superoperators.

    EQSOptAdd ::= (a : QSOpt) '+' (b : QSOpt)
    
    Nonterminal.
    '''

    def __init__(self, soA : Expr, soB : Expr, env : Env):
        super().__init__(env)

        type_check(soA, Expr)
        expr_type_check(soA, QSOpt)
        self._soA = soA

        type_check(soB, Expr)
        expr_type_check(soB, QSOpt)
        self._soB = soB

    ##################################
    # Expression settings

    @property
    def T(self) -> Type:
        return QSOpt
    
    def eval(self) -> object:
        return self._soA.eval() + self._soB.eval()    # type: ignore
    
    def __str__(self) -> str:
        return "(" + str(self._soA) + "+" + str(self._soB) + ")"
    
    ##################################
