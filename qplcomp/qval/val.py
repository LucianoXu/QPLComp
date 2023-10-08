from __future__ import annotations

from ..sugar import type_check

from .qvar import QVar

class QVal:
    '''
    Quantum Values.
    '''

    prec : float = 1e-10
    
    @property
    def qnum(self) -> int:
        '''
        The number of qubits that matches this quantum value.
        '''
        raise NotImplementedError()
    
    
    def __eq__(self, __value: object) -> bool:
        '''
        Decide whether the two QVal instances are equal up to the precision defined by QVal.prec.
        '''
        raise NotImplementedError()
    
class IQVal:
    '''
    Indexed Quantum Values.
    '''
    def __init__(self, qval : QVal, qvar : QVar):
        type_check(qval, QVal)
        self._qval = qval

        type_check(qvar, QVar)
        self._qvar = qvar

        if qval.qnum != qvar.qnum:
            raise ValueError("The qubit number of value '" + str(qval) + "' does not match that of the variable '" + str(qvar) + "'.")
    
    @property
    def qval(self) -> QVal:
        return self._qval
    
    @property
    def qvar(self) -> QVar:
        return self._qvar
    
    @property
    def qnum(self) -> int:
        return self.qvar.qnum
    
    def extend(self, qvarT: QVar) -> IQVal:
        '''
        Extend the indexed quantum value to include extra subsystems, according to the given quantum variables [qvarT], and return the result.
        '''
        raise NotImplementedError()


    def __str__(self) -> str:
        return str(self.qval) + str(self.qvar)