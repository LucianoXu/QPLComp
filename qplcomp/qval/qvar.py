from __future__ import annotations
from typing import List, Tuple, Type, List

from ..sugar import type_check

class QVar:
    '''
    The class for quantum variables (indices).
    '''
    def __init__(self, qvls : List[str]):

        # check for repetition
        temp = []
        for v in qvls:
            if v in temp:
                raise ValueError("The variable '" + v + "' appears in the qvar '" + QVar._qvls_str(qvls) + "' more than once.")
            temp.append(v)
            
        self._qvls = temp

        
    def __str__(self) -> str:
        return QVar._qvls_str(self._qvls)
    
    @property
    def qnum(self) -> int:
        return len(self._qvls)
    
    @property
    def tuple(self) -> Tuple[str, ...]:
        return tuple(self._qvls)
    
    @staticmethod
    def _qvls_str(qvls : List[str]) -> str:
        '''
        Return the formatting of [qvls] as qvar.
        '''
        if len(qvls) == 0:
            return "[]"
        
        r = "[" + qvls[0]
        for i in range(1, len(qvls)):
            r += " " + qvls[i]
        
        return r + "]"


    
    def __getitem__(self, i : int) -> str:
        return self._qvls[i]
    
    def __contains__(self, v : str) -> bool:
        return v in self._qvls
    
    def index(self, v : str) -> int:
        return self._qvls.index(v)
    
    def __add__(self, other : QVar) -> QVar:
        '''
        return the quantum variable that contains [self] and [other]
        '''
        type_check(other, QVar)
        
        r = self._qvls.copy()
        for qv in other._qvls:
            if qv not in r:
                r.append(qv)
        
        return QVar(r)
    
    def append_ahead(self, other : QVar) -> QVar:
        '''
        return the quantum variable that contains [self] and [other]
        other is guaranteed to appear in the tail
        '''
        return (self - other) + other
    
    def __sub__(self, other : QVar) -> QVar:
        '''
        return the quantum variable that removes variables of `other` in `self`
        '''
        type_check(other, QVar)
        
        r = []
        for qv in self._qvls:
            if qv not in other._qvls:
                r.append(qv)
        
        return QVar(r)
    
    def contains(self, other : QVar) -> bool:
        '''
        Test whether the quantum variable `self` contains `other`.
        '''
        type_check(other, QVar)

        for qv in other._qvls:
            if qv not in self._qvls:
                return False
        
        return True
    
    def on_same_var(self, other : QVar) -> bool:

        return self.contains(other) and other.contains(self)
    
    def disjoint(self, other : QVar) -> bool:
        '''
        Test whether the quantum variable `self` and `other` are disjoint.
        '''
        type_check(other, QVar)

        for qv in self._qvls:
            if qv in other._qvls:
                return False
            
        return True
    
    def to(self, other : QVar) -> List[int]:
        '''
        return the positions of variables of `other` in `self`
        '''
        if not self.contains(other):
            raise ValueError("QVar `self` should contain QVar `other`.")
        
        r = []
        for i in range(other.qnum):
            pos = self._qvls.index(other[i])
            r.append(pos)

        return r
