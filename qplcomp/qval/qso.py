
from __future__ import annotations
from typing import Sequence, List

from ..sugar import type_check

import numpy as np
from .. import linalgPP

from .qopt import QOpt

from .val import QVal

def Kraus_str(ls : List[QOpt]) -> str:
    res = "{ " + str(ls[0])
    for i in range(1, len(ls)):
        res += ", " + str(ls[i])
    res += " }"
    return res


class QSOpt(QVal):
    '''
    The class to represent quantum super operators.
    '''

    def __init__(self, data, is_qo : None | bool = None):
        '''
        Construct a QSOpt instance with the given data.

        Parameters:
            - `data`:
                - `List[QOpt]`, the Kraus operators `E_i`. Note that the E_i should be of the same qubit number.
            - `is_qo`: `None | bool`, whether this superoperator is quantum operation. In otherwords, whether the Kraus operators `E_i` satisfy `0 <= sum E_i E_i^dagger <= I`.
        '''
        self._qnum : int

        # data is Kraus representation
        if isinstance(data, list):
            if len(data) == 0:
                raise ValueError("The Kraus representation should have at least one operator.")
            
            for E in data:
                type_check(E, QOpt)

            self._qnum = data[0].qnum
            for E in data:
                if E.qnum != self._qnum:
                    raise ValueError("The Kraus operators should be of the same number of qubits.")
                
            self._Krausls = data.copy()
            
        else:
            raise Exception()
        
        self._qo : None | bool = is_qo
        
    @property
    def Kraus(self) -> List[QOpt]:
        '''
        Return the list of corresponding Kraus operators.
        '''
        return self._Krausls
    
    def __str__(self) -> str:
        return Kraus_str(self._Krausls)

    
    @property
    def qnum(self) -> int:
        return self._qnum
    
    @property
    def is_qo(self) -> bool:
        if self._qo is None:
            self._qo = linalgPP.is_qo([E.m_repr for E in self._Krausls], self.prec)
        return self._qo
    

    ################################################
    # Methods between QSOpt and QOpt
    ################################################

    def apply(self, opt : QOpt) -> QOpt:
        '''
        Calculate the application result of superoperator `self` on the operator `opt`, and return the result.

        - Parameters:
            - `self` : `QSOpt`, the superoperator.
            - `opt` : `QOpt`, the operator.
        - Returns: `QOpt`, the result.
        '''
        type_check(opt, QOpt)

        if self.qnum != opt.qnum:
            raise ValueError("The QSOpt instance cannot apply on the QOpt instance. The QSOpt instance is of " + str(self.qnum) + " qubits, but the QOpt instance is of "+ str(opt.qnum) + "qubits.")

        res = QOpt.zero_opt(self.qnum)

        for E in self._Krausls:
            res = res + E @ opt @ E.dagger()

        # quantum operator on effect -> effect
        if self._qo == True and opt.effect_tag == True:
            res.assert_effect()

        # quantum operator on partial density operator -> partial density operator
        if self._qo == True and opt.pdo_tag == True:
            res.assert_pdo()

        return res


    ################################################
    # Methods of QSOpt
    ################################################
        
    def __add__(self, other : QSOpt) -> QSOpt:
        '''
        Calculate and return the addition result of `self` and `other`.
        - Parameters: `self`, `other` : `QSOpt`.
        - Returns: `QSOpt`.
        '''
        type_check(other, QOpt)

        if self.qnum != other.qnum:
            raise ValueError("The two QSOpt should have the same number of qubit numbers.")
        
        return QSOpt(self.Kraus + other.Kraus)


    def dagger(self) -> QSOpt:
        '''
        Calculate and return the conjugate transpose of this QSOpt instance.
        
        Parameters: none.
        Returns: QSOpt, the result.
        '''

        new_Kraus = [item.dagger() for item in self.Kraus]
        return QSOpt(new_Kraus)