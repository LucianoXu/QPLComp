from __future__ import annotations
from typing import Type

from ..sugar import type_check
from ..env import Expr, Env, expr_type_check

from ..qval import QOpt, QSOpt


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


class EQOptAdd(Expr):
    '''
    The expression for additions of quantum operators.

    EQOptAdd ::= (a : QOpt) '+' (b : QOpt)
    
    Nonterminal.
    '''

    def __init__(self, optA : Expr, optB : Expr, env : Env):
        super().__init__(env)

        type_check(optA, Expr)
        expr_type_check(optA, QOpt)
        self._optA = optA

        type_check(optB, Expr)
        expr_type_check(optB, QOpt)
        self._optB = optB

    ##################################
    # Expression settings

    @property
    def T(self) -> Type:
        return QOpt
    
    def eval(self) -> object:
        return self._optA.eval() + self._optB.eval()    # type: ignore
    
    def __str__(self) -> str:
        return "(" + str(self._optA) + "+" + str(self._optB) + ")"
    
    ##################################

class EQOptNeg(Expr):
    '''
    The expression for negation of a quantum operator.

    EQOptNeg ::= '(' '-' (a : QOpt) ')'
    
    Nonterminal.
    '''

    def __init__(self, opt : Expr, env : Env):
        super().__init__(env)

        type_check(opt, Expr)
        expr_type_check(opt, QOpt)
        self._opt = opt

    ##################################
    # Expression settings

    @property
    def T(self) -> Type:
        return QOpt
    
    def eval(self) -> object:
        return -self._opt.eval()    # type: ignore
    
    def __str__(self) -> str:
        return "(-" + str(self._opt) + ")"
    
    ##################################


class EQOptSub(Expr):
    '''
    The expression for subtractions of quantum operators.

    EQOptSub ::= (a : QOpt) '-' (b : QOpt)
    
    Nonterminal.
    '''

    def __init__(self, optA : Expr, optB : Expr, env : Env):
        super().__init__(env)

        type_check(optA, Expr)
        expr_type_check(optA, QOpt)
        self._optA = optA

        type_check(optB, Expr)
        expr_type_check(optB, QOpt)
        self._optB = optB

    ##################################
    # Expression settings

    @property
    def T(self) -> Type:
        return QOpt
    
    def eval(self) -> object:
        return self._optA.eval() - self._optB.eval()    # type: ignore
    
    def __str__(self) -> str:
        return "(" + str(self._optA) + "-" + str(self._optB) + ")"
    
    ##################################


class EQOptMul(Expr):
    '''
    The expression for subtractions of quantum operators.

    EQOptMul ::= (a : QOpt) (b : QOpt)
                | (a : QOpt) '*' (b : QOpt)
    
    Nonterminal.
    '''

    def __init__(self, optA : Expr, optB : Expr, env : Env):
        super().__init__(env)

        type_check(optA, Expr)
        expr_type_check(optA, QOpt)
        self._optA = optA

        type_check(optB, Expr)
        expr_type_check(optB, QOpt)
        self._optB = optB

    ##################################
    # Expression settings

    @property
    def T(self) -> Type:
        return QOpt
    
    def eval(self) -> object:
        return self._optA.eval() @ self._optB.eval()    # type: ignore
    
    def __str__(self) -> str:
        return "(" + str(self._optA) + " " + str(self._optB) + ")"
    
    ##################################

class EQOptDagger(Expr):
    '''
    The expression for the conjugate transpose of a quantum operator.

    EQOptDagger ::= (a : QOpt) '^\\dagger'
                    | (a : QOpt) '†'
    
    Nonterminal.
    '''

    def __init__(self, opt : Expr, env : Env):
        super().__init__(env)

        type_check(opt, Expr)
        expr_type_check(opt, QOpt)
        self._opt = opt

    ##################################
    # Expression settings

    @property
    def T(self) -> Type:
        return QOpt
    
    def eval(self) -> object:
        return self._opt.eval().dagger()    # type: ignore
    
    def __str__(self) -> str:
        return "(" + str(self._opt) + "†" + ")"
    
    ##################################



class EQOptTensor(Expr):
    '''
    The expression for tensor product of quantum operators.

    EQOptTensor ::= (a : QOpt) '⊗' (b : QOpt)
                    | (a : QOpt) '\\otimes' (b : QOpt)
    
    Nonterminal.
    '''

    def __init__(self, optA : Expr, optB : Expr, env : Env):
        super().__init__(env)

        type_check(optA, Expr)
        expr_type_check(optA, QOpt)
        self._optA = optA

        type_check(optB, Expr)
        expr_type_check(optB, QOpt)
        self._optB = optB

    ##################################
    # Expression settings

    @property
    def T(self) -> Type:
        return QOpt
    
    def eval(self) -> object:
        return self._optA.eval().tensor(self._optB.eval())    # type: ignore
    
    def __str__(self) -> str:
        return "(" + str(self._optA) + "⊗" + str(self._optB) + ")"
    
    ##################################


class EQOptDisjunct(Expr):
    '''
    The expression for disjunction of projective quantum operators.

    EQOptDisjunct ::= (a : QOpt) '\\vee' (b : QOpt)
                    | (a : QOpt) '∨' (b : QOpt)
    
    Nonterminal.
    '''

    def __init__(self, optA : Expr, optB : Expr, env : Env):
        super().__init__(env)

        type_check(optA, Expr)
        expr_type_check(optA, QOpt)
        self._optA = optA

        type_check(optB, Expr)
        expr_type_check(optB, QOpt)
        self._optB = optB

    ##################################
    # Expression settings

    @property
    def T(self) -> Type:
        return QOpt
    
    def eval(self) -> object:
        return self._optA.eval() | self._optB.eval()    # type: ignore
    
    def __str__(self) -> str:
        return "(" + str(self._optA) + " ∨ " + str(self._optB) + ")"
    
    ##################################

class EQOptConjunct(Expr):
    '''
    The expression for conjunction of projective quantum operators.

    EQOptConjunct   ::= (a : QOpt) '\\wedge' (b : QOpt)
                    | (a : QOpt) '∧' (b : QOpt)
    
    Nonterminal.
    '''

    def __init__(self, optA : Expr, optB : Expr, env : Env):
        super().__init__(env)

        type_check(optA, Expr)
        expr_type_check(optA, QOpt)
        self._optA = optA

        type_check(optB, Expr)
        expr_type_check(optB, QOpt)
        self._optB = optB

    ##################################
    # Expression settings

    @property
    def T(self) -> Type:
        return QOpt
    
    def eval(self) -> object:
        return self._optA.eval() & self._optB.eval()    # type: ignore
    
    def __str__(self) -> str:
        return "(" + str(self._optA) + " ∧ " + str(self._optB) + ")"
    
    ##################################

class EQOptSasakiImply(Expr):
    '''
    The expression for Sasaki implication of projective quantum operators.

    EQOptSasakiImply   ::= (a : QOpt) '\\SasakiImply' (b : QOpt)
                        | (a : QOpt) '⇝' (b : QOpt)
    
    Nonterminal.
    '''

    def __init__(self, optA : Expr, optB : Expr, env : Env):
        super().__init__(env)

        type_check(optA, Expr)
        expr_type_check(optA, QOpt)
        self._optA = optA

        type_check(optB, Expr)
        expr_type_check(optB, QOpt)
        self._optB = optB

    ##################################
    # Expression settings

    @property
    def T(self) -> Type:
        return QOpt
    
    def eval(self) -> object:
        return self._optA.eval().Sasaki_imply(self._optB.eval())    # type: ignore
    
    def __str__(self) -> str:
        return "(" + str(self._optA) + " ⇝ " + str(self._optB) + ")"
    
    ##################################

class EQOptSasakiConjunct(Expr):
    '''
    The expression for Sasaki conjunction of projective quantum operators.

    EQOptSasakiConjunct ::= (a : QOpt) '\\SasakiConjunct' (b : QOpt)
                        | (a : QOpt) '⋒' (b : QOpt)
    
    Nonterminal.
    '''

    def __init__(self, optA : Expr, optB : Expr, env : Env):
        super().__init__(env)

        type_check(optA, Expr)
        expr_type_check(optA, QOpt)
        self._optA = optA

        type_check(optB, Expr)
        expr_type_check(optB, QOpt)
        self._optB = optB

    ##################################
    # Expression settings

    @property
    def T(self) -> Type:
        return QOpt
    
    def eval(self) -> object:
        return self._optA.eval().Sasaki_conjunct(self._optB.eval())    # type: ignore
    
    def __str__(self) -> str:
        return "(" + str(self._optA) + " ⋒ " + str(self._optB) + ")"
    
    ##################################


class EQSOptApply(Expr):
    '''
    The expression for application of superoperators on operators.

    EQOptConjunct   ::= (E : QSOpt) '(' (b : QOpt) ')'
    
    Nonterminal.
    '''

    def __init__(self, so : Expr, opt : Expr, env : Env):
        super().__init__(env)

        type_check(so, Expr)
        expr_type_check(so, QSOpt)
        self._so = so

        type_check(opt, Expr)
        expr_type_check(opt, QOpt)
        self._opt = opt

    ##################################
    # Expression settings

    @property
    def T(self) -> Type:
        return QOpt
    
    def eval(self) -> object:
        return self._so.eval().apply(self._opt.eval())    # type: ignore
    
    def __str__(self) -> str:
        return "(" + str(self._so) + "(" + str(self._opt) + "))"
    
    ##################################
