
from __future__ import annotations
from typing import Sequence

from ..sugar import type_check

import numpy as np
from .. import linalgPP

from .val import QVal

class QOpt(QVal):
    '''
    The class to represent quantum operators. They are matrices without quantum variable indices.

    Note: inplace operations are not allowed. Therefore the QOpt here are literal values.
    '''
    def __init__(self, data : np.ndarray,
                 is_unitary : None | bool = None,
                 is_effect : None | bool = None,
                 is_pdo : None | bool = None,
                 is_projector : None | bool = None):
        '''

        Construct a QOpt instance with the given data. 
        
        Parameters
            - data: np.ndarray, two options:
                - a tensor representation of the QOpt
                - a matrix representation of the QOpt
            - is_unitary, is_effect, is_projector : bool. The known properties of this operator.


        [index sequence of tensor representation]

        qvar == [q1, q2, q3, ... , qn]

            n  n+1 n+2 n+3     2n-2 2n-1
            |   |   |   |  ...  |   |
            ---------------------------
           |q1  q2  q3     ...      qn |
            ---------------------------
            |   |   |   |  ...  |   |
            0   1   2   3      n-2 n-1

        '''

        # the tensor representation of this quantum operator
        self._tensor_repr : np.ndarray 

        # the matrix representation of this quantum operator
        self._matrix_repr : np.ndarray

        # the qubit number
        self._qnum : int

        # if the parameter data is matrix representation
        if len(data.shape) == 2:

            # check whether it is square
            d0 = data.shape[0]
            d1 = data.shape[1]

            if d0 != d1:
                raise ValueError("Dimension error.")

            # check whether dim = 2**n for some n
            self._qnum = round(np.log2(d1))
            if (2**self._qnum != d0):
                raise ValueError("Dimension error.")
            
            self._matrix_repr = data
            self._tensor_repr = np.reshape(data, (2,)*self._qnum*2)

        # if the parameter data is tensor representation
        else:
            if len(data.shape) % 2 == 1:
                raise ValueError("Dimension error.")
            
            for d in data.shape:
                if d != 2:
                    raise ValueError("Dimension error.")
                
            self._qnum = len(data.shape) // 2
            self._matrix_repr = data.reshape((2**self._qnum,) * 2)
            self._tensor_repr = data


        # these tags record the verified properties of this QOpt instance
        # if the tag is left None, then it needs to be check first.
        self._unitary : None | bool = is_unitary
        self._effect : None | bool = is_effect
        self._pdo : None | bool = is_pdo
        self._projector : None | bool = is_projector


    @property
    def t_repr(self) -> np.ndarray:
        '''
        Return the tensor representation of this quantum operator.
        '''
        return self._tensor_repr

    @property
    def m_repr(self) -> np.ndarray:
        '''
        Return the matrix representation of this quantum operator.
        '''
        return self._matrix_repr
    
    def __str__(self) -> str:
        return str(self.m_repr)
    
    def __eq__(self, other) -> bool:
        if not isinstance(other, QOpt):
            return False
        
        if self.qnum != other.qnum:
            return False
        
        return linalgPP.close_equal(self.m_repr, other.m_repr, QVal.prec)

    @property
    def qnum(self) -> int:
        return self._qnum
    
    @property
    def unitary_tag(self) -> None | bool:
        return self._unitary
    @property
    def is_unitary(self) -> bool:
        if self._unitary is None:
            self._unitary = linalgPP.is_unitary(self.m_repr, self.prec)
        return self._unitary
    def assert_unitary(self) -> None:
        self._unitary = True
    

    @property
    def effect_tag(self) -> None | bool:
        return self._effect
    @property
    def is_effect(self) -> bool:
        if self._effect is None:
            self._effect = linalgPP.is_effect(self.m_repr, self.prec)
        return self._effect
    def assert_effect(self) -> None:
        self._effect = True

    @property
    def pdo_tag(self) -> None | bool:
        return self._pdo
    @property
    def is_pdo(self) -> bool:
        if self._pdo is None:
            self._pdo = linalgPP.is_pdo(self.m_repr, self.prec)
        return self._pdo
    def assert_pdo(self) -> None:
        self._pdo = True

    @property
    def projector_tag(self) -> None | bool:
        return self._projector
    @property
    def is_projector(self) -> bool:
        if self._projector is None:
            self._projector = linalgPP.is_projector(self.m_repr, self.prec)
        return self._projector
    def assert_projector(self) -> None:
        self._projector = True

    
    @staticmethod
    def eye_opt(qubitn : int) -> QOpt:
        '''
        Create the identity QOpt of the given qubit number.

        Parameters: qubitn : int, the qubit number.
        Returns: QOpt, the identity QOpt.
        '''
        m_repr = np.eye(2**qubitn)
        res = QOpt(m_repr)

        res._unitary = True
        res._effect = True
        res._pdo = None
        res._projector = True

        return res

    @staticmethod
    def ket0_opt(qubitn : int) -> QOpt:
        '''
        Create the |00...0> QOpt of the given qubit number.

        Parameters: qubitn : int, the qubit number.
        Returns: QOpt, the ket0 QOpt.
        '''
        m_repr = np.zeros((2**qubitn, 2**qubitn))
        m_repr[0][0] = 1.
        res = QOpt(m_repr)

        res._unitary = False
        res._effect = True
        res._pdo = True
        res._projector = True

        return res

    
    @staticmethod
    def zero_opt(qubitn : int) -> QOpt:
        '''
        Create the zero QOpt of the given qubit number.

        Parameters: qubitn : int, the qubit number.
        Returns: QOpt, the zero QOpt.
        '''
        m_repr = np.zeros((2**qubitn, 2**qubitn))
        res = QOpt(m_repr)

        res._unitary = False
        res._effect = True
        res._pdo = True
        res._projector = True

        return res
    

    ################################################
    # Methods of QOpt
    ################################################

    
    def __add__(self, other : QOpt) -> QOpt:
        '''
        Calculate and return the addition result of self and other.
        Operators must be of the same qubit number.
        - Parameters: `self`, `other` : `QOpt`.
        - Returns: `QOpt`.
        '''

        type_check(other, QOpt)
        if self.qnum != other.qnum:
            raise ValueError("The two QOpt should have the same number of qubit numbers.")
        
        return QOpt(self.t_repr + other.t_repr)
        
    def neg(self) -> QOpt:
        '''
        Calculate and return the negation of this QOpt instance.
        
        Parameters: none.
        Returns: QOpt, the result.
        '''
        return QOpt(-self.t_repr)
    
    def __neg__(self) -> QOpt:
        return self.neg()
    
    def __sub__(self, other : QOpt) -> QOpt:
        '''
        Calculate and return the subtraction result of self and other.
        Operators must be of the same qubit number.
        - Parameters: `self`, `other` : `QOpt`.
        - Returns: `QOpt`.
        '''
        return self + (- other)


    def dagger(self) -> QOpt:
        '''
        Calculate and return the conjugate transpose of this QOpt instance.
        
        Parameters: none.
        Returns: QOpt, the result.
        '''
        trans = list(range(self.qnum, self.qnum*2)) + list(range(0, self.qnum))

        res = QOpt(self.t_repr.conj().transpose(trans))

        if self._unitary == True:
            res._unitary = True
        if self._effect == True:
            res._effect = True
        if self._pdo == True:
            res._pdo = True
        if self._projector == True:
            res._projector = True

        return res
    
    def mul(self, other : QOpt) -> QOpt:
        '''
        Calculate and return the multiplication of self @ other.

        Parameters: self, other : QOpt, with the same number of qubits.
        Returns: QOpt, the result.
        Errors: ValueError when self and other differ in their qubit numbers.
        '''
        
        type_check(other, QOpt)

        if self.qnum != other.qnum:
            raise ValueError("The two QOpt should have the same number of qubit numbers.")
        
        res = QOpt(self.m_repr @ other.m_repr)
        
        if self._unitary == True and other._unitary == True:
            res._unitary = True

        return res
    
    def __matmul__(self, other : QOpt) -> QOpt:
        return self.mul(other)
    
    def scale(self, c : float) -> QOpt:
        '''
        Calculate and return the scaling of `c * self'.

        Parameters: 
            - `self` : `QOpt`.
            - `c` : `float`, the scalar.
        Returns: `QOpt`, the result.
        '''

        res = QOpt(self.t_repr * c)

        if 0. <= c <= 1.:
            if self._effect == True:
                res._effect = True
            if self._pdo == True:
                res._pdo = True

        return res
    
    def __mul__(self, other : float) -> QOpt:
        return self.scale(other)
    def __rmul__(self, other : float) -> QOpt:
        return self.scale(other)
        
    
    def tensor(self, other : QOpt) -> QOpt:
        '''
        Calculate and return the tensor product of operators self and other.
        '''

        type_check(other, QOpt)

        new_t_repr = np.tensordot(self.t_repr, other.t_repr, ([], []))

        # adjust the index sequence
        r = list(range(0, self.qnum))\
            + list(range(self.qnum*2, self.qnum*2 + other.qnum))\
            + list(range(self.qnum, self.qnum*2))\
            + list(range(self.qnum*2 + other.qnum, (self.qnum + other.qnum)*2))
        
        new_t_repr = new_t_repr.transpose(r)

        res = QOpt(new_t_repr)

        if self._unitary == True and other._unitary == True:
            res._unitary = True

        if self._effect == True and other._effect == True:
            res._effect = True

        if self._pdo == True and other._pdo == True:
            res._pdo = True

        if self._projector == True and other._projector == True:
            res._projector = True

        return res
    
    def permute(self, perm : Sequence[int]) -> QOpt:
        '''
        Permute the order of qubits.
        '''

        # check the validity of the permutation
        if len(perm) != self.qnum:
            raise ValueError("The permutation provided is not valid.")
        appearance = [False] * len(perm)
        for item in perm:
            if item < 0 or item >= len(perm):
                raise ValueError("The permutation provided is not valid.")
            appearance[item] = True
        for pos in appearance:
            if not pos:
                raise ValueError("The permutation provided is not valid.")
        

        t_repr_perm = list(perm) + [i + self.qnum for i in perm]
        new_t_repr = self.t_repr.transpose(t_repr_perm)

        return QOpt(new_t_repr, 
                    is_unitary=self._unitary,
                    is_effect=self._effect,
                    is_pdo=self._pdo,
                    is_projector=self._projector)
    

    
    def Loewner_le(self, other : QOpt) -> bool:
        '''
        Decide whether the two operator self and other follow the Loewner order self <= other. The comparison between eigenvalues are conducted with respected to the given precision.
    
        Parameters: self, other : QOpt, with the same number of qubits.
        Returns: bool, whether self <= other.
        Errors: ValueError when self and other differ in their qubit numbers.
        '''
        type_check(other, QOpt)

        if self.qnum != other.qnum:
            raise ValueError("The two QOpt should have the same number of qubit numbers.")

        return linalgPP.Loewner_le(self.m_repr, other.m_repr, self.prec)
    
    def __le__(self, other : QOpt) -> bool:
        return self.Loewner_le(other)

    def disjunct(self, other : QOpt) -> QOpt:
        '''
        Calculate and return the disjunction of subspaces represented by projectors self and other.

        Parameters: self, other : QOpt, projectors with the same number of qubits.
        Returns: QOpt, a projector, representing the subspace of disjunction.
        Errors: 
            - ValueError when self and other differ in their qubit numbers.
            - ValueError when self or other is not a projector.
        '''
        type_check(other, QOpt)

        if self.qnum != other.qnum:
            raise ValueError("The two QOpt should have the same number of qubit numbers.")
        
        if not self.is_projector or not other.is_projector:
            raise ValueError("The two QOpt are not both projectors.")
        
        # only preserve the 1-eigenvalue vectors
        stacked = np.hstack(
            (linalgPP.row_space(self.m_repr, QVal.prec), 
             linalgPP.row_space(other.m_repr, QVal.prec)))
        
        new_m_repr : np.ndarray
        # check whether it is zero projector
        if stacked.shape[1] == 0:
            new_m_repr = (np.zeros_like(self.m_repr))
        else:
            # orthonormalization
            ortho = linalgPP.column_space(stacked, QVal.prec)
            new_m_repr = ortho @ ortho.transpose().conj()

        return QOpt(new_m_repr, is_unitary=None, is_effect=True, is_projector=True)
    
    def __or__(self, other : QOpt) -> QOpt:
        return self.disjunct(other)
    
    def conjunct(self, other : QOpt) -> QOpt:
        '''
        Calculate and return the conjunction of subspaces represented by projectors self and other.

        Parameters: self, other : QOpt, projectors with the same number of qubits.
        Returns: QOpt, a projector, representing the subspace of conjunction.
        Errors: 
            - ValueError when self and other differ in their qubit numbers.
            - ValueError when self or other is not a projector.

        ================================================================
        About the algorithm: 

        Step 1. Calculate the space of P and Q, get the matrices of orthonormal basis spaceP an spaceQ.
        
        Step 2. The vectors x in the conjunction satisfies both
        
                exists a, spaceP @ a = x,
                exists b, spaceQ @ b = x.

            Therefore we need to find the spaces of a and b satisfying 

                spaceP @ a = spaceQ @ b.

            Therefore we need to find the right-null space of the stacked matrix [spaceP | spaceQ].

        Step 3. Take out the corresponding space of a from the null space, and transform it to the conjunction space by applying spaceP.    
        ================================================================
        '''
        type_check(other, QOpt)

        if self.qnum != other.qnum:
            raise ValueError("The two QOpt should have the same number of qubit numbers.")
        
        if not self.is_projector or not other.is_projector:
            raise ValueError("The two QOpt are not both projectors.")
        
        spaceP = linalgPP.column_space(self.m_repr, QVal.prec)
        spaceQ = linalgPP.column_space(other.m_repr, QVal.prec)

        dimP = spaceP.shape[1]

        # only preserve the 1-eigenvalue vectors
        stacked = np.hstack((spaceP, spaceQ))

        # calculate the right zero space of the stacked matrix [spaceP | spaceQ]
        rnspace = linalgPP.right_null_space(stacked, QVal.prec)


        new_m_repr : np.ndarray
        # check whether it is zero projector
        if rnspace.shape[1] == 0:
            new_m_repr = np.zeros_like(self.m_repr)
        else:
            # get a set of vectors for the conjunction space
            conjunct_space = spaceP @ rnspace[:dimP]

            # orthonormalization
            ortho = linalgPP.column_space(conjunct_space, QVal.prec)
            new_m_repr = ortho @ ortho.transpose().conj()

        return QOpt(new_m_repr, is_unitary=None, is_effect=True, is_projector=True)

    def __and__(self, other : QOpt) -> QOpt:
        return self.conjunct(other)
    
    def complement(self) -> QOpt:
        '''
        Calculate and return the orthogonal complement of the subspace represented by `self`.

        Parameters: `self` : `QOpt`, a projector.
        Returns: `QOpt`, a projector, representing the complement subspace.
        Errors: 
            - 'ValueError' when 'self' is not a projector.
        '''
        
        if not self.is_projector:
            raise ValueError("The QOpt instance is not a projector.")
        
        return QOpt.eye_opt(self.qnum) - self
    
    def __invert__(self) -> QOpt:
        return self.complement()
    
    def space_sub(self, other : QOpt) -> QOpt:
        '''
        Calculate and return the subtraction of subspaces represented by projectors self and other.

        Parameters: self, other : QOpt, projectors with the same number of qubits.
        Returns: QOpt, a projector, representing the subspace of subtraction.
        Errors: 
            - ValueError when self and other differ in their qubit numbers.
            - ValueError when self or other is not a projector.

        ================================================================
        Note: the subtraction of self and other is defined by:

        { v \\in self: \\forall u \\in other, v \\bot u },

        which is proved to be equivalent to `self & (~ other)`.

        '''
        return self & (~ other)
    
    def support(self) -> QOpt:
        '''
        Return the support of `self`.
        Parameters: `self` : `QOpt`, should be Hermitian (not checked here).
        Returns: `QOpt`, a projector.
        '''
        return QOpt(linalgPP.support(self.m_repr, QVal.prec),
                   is_unitary=None,
                   is_effect=True,
                   is_pdo=None,
                   is_projector=True)




    
    def trace(self, qls : Sequence[int]) -> QOpt:
        '''
        Trace out the qubits indicated in `qls`.
        '''

        sorted_qls = sorted(qls, reverse=True)

        temp = self.t_repr

        for i in sorted_qls:
            temp = temp.trace(axis1=i, axis2=i + len(temp.shape)//2)

        res = QOpt(temp)

        if self._pdo == True:
            res._pdo = True

        return res

    def Sasaki_imply(self, other : QOpt) -> QOpt:
        '''
        Calculate and return the Sasaki implication of subspaces represented by projectors `self` and `other`.

        Parameters: `self`, `other` : QOpt, projectors with the same number of qubits.
        Returns: QOpt, a projector, representing the subspace of Sasaki implication.
        
        Note: Sasaki implication P -> R := P^\\bot \vee (P \\wedge R)
        '''
        return (~ self) | (self & other)
    
    def Sasaki_conjunc(self, other : QOpt) -> QOpt:
        '''
        Calculate and return the Sasaki conjunction of subspaces represented by projectors `self` and `other`.

        Parameters: `self`, `other` : QOpt, projectors with the same number of qubits.
        Returns: QOpt, a projector, representing the subspace of Sasaki conjunction.
        
        Note: Sasaki conjunction P -> R := P \\wedge (P^\\bot \\vee R)
        '''
        return self & ((~ self) | other)
