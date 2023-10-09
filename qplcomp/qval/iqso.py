
from __future__ import annotations

import numpy as np
from .. import linalgPP

from ..sugar import type_check

from .val import IQVal, QVal
from .qopt import QOpt
from .iqopt import IQOpt
from .qso import QSOpt
from .qvar import QVar


class IQSOpt(IQVal):
    '''
    Indexed quantum superoperators.
    '''

    def __init__(self, qso: QSOpt, qvar: QVar):
        super().__init__(qso, qvar)

        type_check(qso, QSOpt)
        self._qval : QSOpt

    @property
    def qval(self) -> QSOpt:
        return self._qval
    

    
    def extend(self, qvarT: QVar) -> IQSOpt:
        if not qvarT.contains(self.qvar):
            raise ValueError("The extension target qvar '" + str(qvarT) + "' does not contain the original qvar '" + str(self.qvar) + "'.")
        
        # extend every Kraus operator

        new_Kraus = [IQOpt(E, self.qvar).extend(qvarT).qval for E in self._qval.Kraus]

        new_QSO = QSOpt(new_Kraus)
        if self._qval.qo:
            new_QSO.assert_qo()

        return IQSOpt(new_QSO, qvarT)
    
    ################################################
    # Methods between IQSOpt and IQOpt
    ################################################

    def apply(self, iopt : IQOpt) -> IQOpt:
        '''
        Calculate the application result of indexed superoperator `self` on the operator `iopt`, and return the result.

        - Parameters:
            - `self` : `IQSOpt`, the indexed superoperator.
            - `iopt` : `IQOpt`, the indexed operator.
        - Returns: `IQOpt`, the indexed result.
        '''
        type_check(iopt, IQOpt)

        # the common qvar
        qvar_all = self.qvar + iopt.qvar

        # cylinder extension
        self_ext = self.extend(qvar_all)
        other_ext = iopt.extend(qvar_all)

        return IQOpt(self_ext.qval.apply(other_ext.qval), qvar_all)

    def apply_rho(self, rho : IQOpt) -> IQOpt:
        '''
        Calculate the application result of indexed superoperator `self` on the partial density operator `rho`, and return the result.

        Note that the extension for partial density operators are different: we have to assume that every extra system is in |0> state.

        - Parameters:
            - `self` : `IQSOpt`, the indexed superoperator.
            - `rho` : `IQOpt`, the partial density operator.
        - Returns: `IQOpt`, the indexed result.
        '''
        type_check(rho, IQOpt)

        # the common qvar
        qvar_all = self.qvar + rho.qvar

        # cylinder extension
        self_ext = self.extend(qvar_all)
        other_ext = rho.extend_rho(qvar_all)

        return IQOpt(self_ext.qval.apply(other_ext.qval), qvar_all)
    
    def __add__(self, other : IQSOpt) -> IQSOpt:
        '''
        For indexed quantum superoperators `self` and `other`, return the addition result.
        Automatic cylinder extension is applied.
        - Parameters: `self`, `other` : `IQSOpt`.
        - Returns: `IQSOpt`.
        '''

        type_check(other, IQSOpt)

        # the common qvar
        qvar_all = self.qvar + other.qvar

        # cylinder extension
        self_ext = self.extend(qvar_all)
        other_ext = other.extend(qvar_all)

        # return the result
        return IQSOpt(self_ext.qval + other_ext.qval, qvar_all)


    def dagger(self) -> IQSOpt:
        '''
        Return the conjugate transpose of `self`.
        - Parameters: none.
        - Returns: `IQSOpt`.
        '''

        return IQSOpt(self.qval.dagger(), self.qvar)