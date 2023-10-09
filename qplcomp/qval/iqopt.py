
from __future__ import annotations

import numpy as np
from .. import linalgPP

from ..sugar import type_check

from .val import IQVal, QVal
from .qopt import QOpt
from .qvar import QVar

class IQOpt(IQVal):
    '''
    Indexed quantum operators.
    '''

    def __init__(self, qopt: QOpt, qvar: QVar):
        super().__init__(qopt, qvar)
        
        type_check(qopt, QOpt)
        self._qval : QOpt
    
    @property
    def qval(self) -> QOpt:
        return self._qval
    
    @staticmethod
    def identity() -> IQOpt:
        '''
        return the identity operator with zero qubits.
        '''
        return IQOpt(QOpt(np.array([[1.]])), QVar([]))
    
    @staticmethod
    def zero() -> IQOpt:
        '''
        return the zero operator with zero qubits.
        '''
        return IQOpt(QOpt(np.array([[0.]])), QVar([]))


    def extend(self, qvarT: QVar) -> IQOpt:
        if not qvarT.contains(self.qvar):
            raise ValueError("The extension target qvar '" + str(qvarT) + "' does not contain the original qvar '" + str(self.qvar) + "'.")
        
        dim_I = qvarT.qnum - self.qnum
        optI = QOpt.eye_opt(dim_I)

        temp_opt = self.qval.tensor(optI)

        # rearrange the indices
        count_ext = 0
        r = []
        for i in range(qvarT.qnum):
            if qvarT[i] in self.qvar:
                pos = self.qvar.index(qvarT[i])
                r.append(pos)
            else:
                r.append(self.qnum + count_ext)
                count_ext += 1

        opt = temp_opt.permute(r)
        return IQOpt(opt, qvarT)

    def extend_rho(self, qvarT: QVar) -> IQOpt:
        '''
        This special method extends this operator according to rules for partial density operators.
        '''
        if not qvarT.contains(self.qvar):
            raise ValueError("The extension target qvar '" + str(qvarT) + "' does not contain the original qvar '" + str(self.qvar) + "'.")
        
        dim_I = qvarT.qnum - self.qnum
        optI = QOpt.ket0_opt(dim_I)

        temp_opt = self.qval.tensor(optI)

        # rearrange the indices
        count_ext = 0
        r = []
        for i in range(qvarT.qnum):
            if qvarT[i] in self.qvar:
                pos = self.qvar.index(qvarT[i])
                r.append(pos)
            else:
                r.append(self.qnum + count_ext)
                count_ext += 1

        opt = temp_opt.permute(r)
        return IQOpt(opt, qvarT)
    
    def __add__(self, other : IQOpt) -> IQOpt:
        '''
        For indexed quantum operators `self` and `other`, return the addition result.
        Automatic cylinder extension is applied.
        - Parameters: `self`, `other` : `IQOpt`.
        - Returns: `IQOpt`.
        '''

        type_check(other, IQOpt)

        # the common qvar
        qvar_all = self.qvar + other.qvar

        # cylinder extension
        self_ext = self.extend(qvar_all)
        other_ext = other.extend(qvar_all)

        # return the result
        return IQOpt(self_ext.qval + other_ext.qval, qvar_all)


    def neg(self) -> IQOpt:
        '''
        Return the negation of `self`.
        - Parameters: none.
        - Returns: `IQOpt`.
        '''

        return IQOpt(-self.qval, self.qvar)
    
    def __neg__(self) -> IQOpt:
        return self.neg()
    
    def __sub__(self, other : IQOpt) -> IQOpt:
        '''
        For indexed quantum operators `self` and `other`, return the subtraction result.
        Automatic cylinder extension is applied.
        - Parameters: `self`, `other` : `IQOpt`.
        - Returns: `IQOpt`.
        '''
        return self + (- other)

    
    def dagger(self) -> IQOpt:
        '''
        Return the conjugate transpose of `self`.
        - Parameters: none.
        - Returns: `IQOpt`.
        '''

        return IQOpt(self.qval.dagger(), self.qvar)
    

    def __matmul__(self, other : IQOpt) -> IQOpt:
        '''
        For indexed quantum operators `self` and `other`, return the matrix multiplication result.
        Automatic cylinder extension is applied.
        - Parameters: `self`, `other` : `IQOpt`.
        - Returns: `IQOpt`.
        '''
        type_check(other, IQOpt)

        # the common qvar
        qvar_all = self.qvar + other.qvar

        # cylinder extension
        self_ext = self.extend(qvar_all)
        other_ext = other.extend(qvar_all)

        return IQOpt(self_ext.qval @ other_ext.qval, qvar_all)
    
    def tensor(self, other : IQOpt) -> IQOpt:
        '''
        For indexed quantum operators `self` and `other`, return the tensor result. Note that self and other should be disjoint on their quantum variables.
        - Parameters: `self`, `other` : `IQOpt`.
        - Returns: `IQOpt`.
        '''
        type_check(other, IQOpt)

        if not self.qvar.disjoint(other.qvar):
            raise ValueError("The quantum variable '" + str(self.qvar) + "' is not disjoint with '" + str(other.qvar) + "'.")
        
        qvar_all = self.qvar + other.qvar

        return IQOpt(self.qval.tensor(other.qval), qvar_all)
    
    def Loewner_le(self, other : IQOpt) -> bool:
        '''
        Decide the Loewner order `self <= other`.
        - Parameters: `self`, `other` : `IQOpt`.
        - Returns: `bool`, whether `self` is smaller than `other`.
        '''
        type_check(other, IQOpt)

        # the common qvar
        qvar_all = self.qvar + other.qvar

        # cylinder extension
        self_ext = self.extend(qvar_all)
        other_ext = other.extend(qvar_all)

        return self_ext.qval <= other_ext.qval

    def __le__(self, other : IQOpt) -> bool:
        return self.Loewner_le(other)
    
    def disjunct(self, other : IQOpt) -> IQOpt:
        '''
        For indexed quantum operators projectors `self` and `other`, return the disjunction of them.

        - Parameters: `self`, `other` : `IQOpt`.
        - Returns: `IQOpt`.
        - Error: `ValueError` when `self` or `other` is not a projector.
        '''
        type_check(other, IQOpt)

        # the common qvar
        qvar_all = self.qvar + other.qvar

        # cylinder extension
        self_ext = self.extend(qvar_all)
        other_ext = other.extend(qvar_all)

        return IQOpt(self_ext.qval | other_ext.qval, qvar_all)
    
    def __or__(self, other : IQOpt) -> IQOpt:
        return self.disjunct(other)
    
    
    def conjunct(self, other : IQOpt) -> IQOpt:
        '''
        For indexed quantum operators projectors `self` and `other`, return the conjunction of them.

        - Parameters: `self`, `other` : `IQOpt`.
        - Returns: `IQOpt`.
        - Error: `ValueError` when `self` or `other` is not a projector.
        '''
        type_check(other, IQOpt)

        # the common qvar
        qvar_all = self.qvar + other.qvar

        # cylinder extension
        self_ext = self.extend(qvar_all)
        other_ext = other.extend(qvar_all)

        return IQOpt(self_ext.qval & other_ext.qval, qvar_all)
    
    def __and__(self, other : IQOpt) -> IQOpt:
        return self.conjunct(other)
