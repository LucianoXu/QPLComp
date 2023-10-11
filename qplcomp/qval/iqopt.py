
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

    def __init__(self, qopt: QOpt, qvar: QVar, rho_extend : bool = False):
        super().__init__(qopt, qvar)
        
        type_check(qopt, QOpt)
        self._qval : QOpt

        # controls how the extension is carrried out
        # this property will pass to its calculation results in some circumstances
        self.rho_extend : bool = rho_extend

    
    @property
    def qval(self) -> QOpt:
        return self._qval
    
    def __eq__(self, other) -> bool:
        if not isinstance(other, IQOpt):
            return False
        
        # the common qvar
        qvar_all = self.qvar + other.qvar

        # cylinder extension
        self_ext = self.extend(qvar_all)
        other_ext = other.extend(qvar_all)
        
        
        return self_ext.qval == other_ext.qval
    
    @staticmethod
    def identity(is_rho : bool) -> IQOpt:
        '''
        return the identity operator with zero qubits.
        '''
        return IQOpt(QOpt(np.array([[1.]])), QVar([]), is_rho)
    
    @staticmethod
    def zero(is_rho : bool) -> IQOpt:
        '''
        return the zero operator with zero qubits.
        '''
        return IQOpt(QOpt(np.array([[0.]])), QVar([]), is_rho)


    def extend(self, qvarT: QVar) -> IQOpt:
        if not qvarT.contains(self.qvar):
            raise ValueError("The extension target qvar '" + str(qvarT) + "' does not contain the original qvar '" + str(self.qvar) + "'.")
        
        dim_I = qvarT.qnum - self.qnum

        # different approaches of extensions
        if self.rho_extend:
            opt_append = QOpt.ket0_opt(dim_I)
        else:
            opt_append = QOpt.eye_opt(dim_I)

        temp_opt = self.qval.tensor(opt_append)

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
        return IQOpt(opt, qvarT, self.rho_extend)
    
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
        return IQOpt(self_ext.qval + other_ext.qval, qvar_all,
                     self.rho_extend and other.rho_extend)


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

        return IQOpt(self_ext.qval @ other_ext.qval, qvar_all,
                     self.rho_extend or other.rho_extend)

    def scale(self, c : float) -> IQOpt:
        '''
        Calculate and return the scaling of `c * self'.

        Parameters: 
            - `self` : `IQOpt`.
            - `c` : `float`, the scalar.
        Returns: `IQOpt`, the result.
        '''

        return IQOpt(self.qval * c, self.qvar, self.rho_extend)


    def __mul__(self, other : float) -> IQOpt:
        return self.scale(other)
    def __rmul__(self, other : float) -> IQOpt:
        return self.scale(other)

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

        return IQOpt(self.qval.tensor(other.qval), qvar_all, self.rho_extend)
    
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

    def complement(self) -> IQOpt:
        '''
        Calculate and return the orthogonal complement of the subspace represented by `self`.

        Parameters: `self` : `IQOpt`, a projector.
        Returns: `IQOpt`, a projector, representing the complement subspace.
        Errors: 
            - 'ValueError' when 'self' is not a projector.
        '''

        return IQOpt(~self.qval, self.qvar)
    
    def __invert__(self) -> IQOpt:
        return self.complement()
    

    def space_sub(self, other : IQOpt) -> IQOpt:
        '''
        For indexed quantum operators projectors `self` and `other`, return the subtraction of the subspaces.

        Note: it is equivalent to `self & (~ other)`.
        
        - Parameters: `self`, `other` : `IQOpt`.
        - Returns: `IQOpt`.
        - Error: `ValueError` when `self` or `other` is not a projector.
        
        '''

        return self & (~ other)

    def support(self) -> IQOpt:
        '''
        Return the support of `self`.
        Parameters: `self` : `IQOpt`, should be Hermitian (not checked here).
        Returns: `IQOpt`, a projector.
        '''
        return IQOpt(self.qval.support(), self.qvar)

    
    def trace(self, qvar : QVar) -> IQOpt:
        '''
        Trace out the given qvar.
        '''
        idx = self.qvar.to(qvar)
        return IQOpt(self.qval.trace(idx), self.qvar - qvar)



    def initwlp(self, qvar : QVar) -> IQOpt:
        P0 = QOpt(np.array([[1., 0.], [0., 0.]]), None, True, True, True)

        temp = self
        for q in qvar:
            IP0 = IQOpt(P0, QVar([q]))
            temp = temp.conjunct(IP0).trace(QVar([q])).support()

        return temp

