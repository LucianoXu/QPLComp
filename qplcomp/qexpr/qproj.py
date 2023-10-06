from __future__ import annotations
from typing import Type

from .. import qval

from .qvar import QVar
from .qexpr import QExpr
from .qopt import QOpt

import numpy as np

class QProj(QOpt):
    '''
    Quantum projector - a special kind of quantum expression.

    A projector P satisfies P^2 = P.
    '''

    def validity_check(self) -> None:
        '''
        Here we check P^2 = P
        '''
        super().validity_check()
    
        P_2 = qval.opt_mul(self.qval, self.qval)

        if not qval.np_prec_equal(P_2, self.qval, self.valenv.precision):
            raise ValueError("The operator is not a projector.")
        

    def init_process(self) -> None:
        super().init_process()


    def disjunct(self, other : QProj) -> QProj:
        '''
        Calculate and return the disjunction of subspaces self and other.
        '''
        if not isinstance(other, QProj):
            raise ValueError("The parameter should be a QProj instance.")

        qvar_all = self.qvar + other.qvar
        P = self.extend(qvar_all).qval
        Q = other.extend(qvar_all).qval

        PorQ = qval.proj_disjunct(P, Q, self.valenv.precision)
        return QProj(PorQ, qvar_all, check = False)
    

    def __or__(self, other : QProj) -> QProj:
        return self.disjunct(other)
    
    def conjunct(self, other : QProj) -> QProj:
        '''
        Calculate and return the conjunction of subspaces self and other.
        '''
        if not isinstance(other, QProj):
            raise ValueError("The parameter should be a QProj instance.")
        
        qvar_all = self.qvar + other.qvar
        P = self.extend(qvar_all).qval
        Q = other.extend(qvar_all).qval

        PandQ = qval.proj_conjunct(P, Q, self.valenv.precision)
        return QProj(PandQ, qvar_all, check = False)

    def __and__(self, other : QProj) -> QProj:
        return self.conjunct(other)