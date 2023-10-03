from __future__ import annotations
from typing import Type

from ..valenv import ValEnv
from .. import qval

from .qvar import QVar

from .parser import parser

import numpy as np

class QExpr:
    '''
    The class for quantum expressions, which has three components:
    - An identifier (string)
    - A quantum operator (np.ndarray)
    - A quantum variable (QVar)
    '''

    # the global ValEnv for quantum expressions
    valenv : ValEnv = ValEnv()

    @staticmethod
    def set_valenv(valenv : ValEnv) -> None:
        QExpr.valenv = valenv

    
    def __init__(self, *args, **kwargs):
        '''
        Create a quantum expression with multiple ways:
        - a string of "qval[qvar]" to be parsed, here qval is the id.
        - two arguments: the first can be an id or a qval, and the second can be a QVar or a string to be parsed.
        The boolean argument with key "check" controlls wether data check is performed. The default value is True.
        '''

        # the case of "id[qvar]" parsing
        if len(args) == 1:
            self._id, qvar_ls = parser.parse(args[0])
            self._qvar = QVar(qvar_ls)
            self._qval = self.valenv[self._id]

        elif len(args) == 2:
            arg0, arg1 = args

            # the case of construction from id
            if isinstance(arg0, str):
                self._id = arg0
                # take out the operator
                self._qval = self.valenv[arg0]
                
            # the case of construction from qval
            elif isinstance(arg0, np.ndarray):
                # save the value and automatic naming
                self._id = self.valenv.append(arg0)
                self._qval = arg0
            else:
                raise RuntimeError("Invalid arguments.")
                

            # the case of "[qvar]" parsing
            if isinstance(arg1, str):
                self._qvar = QVar(arg1)
            # the case of qvar : QVar
            elif isinstance(arg1, QVar):
                self._qvar = arg1
            else:
                raise RuntimeError("Invalid arguments.")

        # the case that a full information is provided
        elif len(args) == 3:
            self._id, self._qval, self._qvar = args
            if not isinstance(self._id, str) or not isinstance(self._qval, np.ndarray) or not isinstance(self._qvar, QVar):
                raise RuntimeError("Invalid arguments.")

        else:
            raise RuntimeError("Invalid arugments.")


        # decide whether a data check is needed
        if "check" in kwargs:
            do_check = kwargs["check"]
        else:
            do_check = True

        if do_check:
            self.validity_check()

        self.init_process()


    @property
    def id(self) -> str:
        return self._id
    
    @property
    def qval(self) -> np.ndarray:
        return self._qval
    
    @property
    def qvar(self) -> QVar:
        return self._qvar
    
    @property
    def qnum(self) -> int:
        return self.qvar.qnum
    
    def validity_check(self) -> None:
        '''
        check the validity of this expression
        '''
        pass
    
    def init_process(self) -> None:
        '''
        the process of the data during initialization
        '''
        pass

    def extend(self, qvarT: QVar) -> QExpr:
        '''
        Extend the expression according to the given quantum variables [qvarT], and return the result.
        '''
        raise NotImplementedError()


    def __str__(self) -> str:
        return self._id + str(self.qvar)
    


class QOpt(QExpr):
    '''
    Quantum operator - a special kind of quantum expression.
    It corresponds to matrices like density operators, unitary operators and Hermitian operators.
    '''

    def validity_check(self) -> None:
        '''
        Here we check whether the qval has the suitable dimension for a quantum operator.
        '''
        super().validity_check()

        calc_qnum : int

        # if input is a matrix
        if len(self._qval.shape) == 2:

            # check whether it is square
            d0 = self._qval.shape[0]
            d1 = self._qval.shape[1]
            if d0 != d1:
                raise ValueError("The operator '" + self._id + "' cannot act as a quantum operator. Dimension error.")

            # check whether dim = 2**n for some n
            calc_qnum = round(np.log2(d1))
            if (2**calc_qnum != d0):
                raise ValueError("The operator '" + self._id + "' cannot act as a quantum operator. Dimension error.")

        # if input is already a tensor
        else:
            if len(self._qval.shape) % 2 == 1:
                raise ValueError("The operator '" + self._id + "' cannot act as a quantum operator. Dimension error.")
            
            for d in self._qval.shape:
                if d != 2:
                    raise ValueError("The operator '" + self._id + "' cannot act as a quantum operator. Dimension error.")
                
            calc_qnum = len(self._qval.shape) // 2

        # check whether the qubit number of the tensor and the qvar matches
        if calc_qnum != self._qvar.qnum:
            raise ValueError("The type for qval '" + self._id + "' is not consistent with the quantum variable '" + str(self._qvar) + "' .")

            
    def init_process(self) -> None:
        super().init_process()

        # transform the matrix to the tensor
        if len(self._qval.shape) == 2:
            calc_qnum = round(np.log2(self._qval.shape[0]))
            self._qval = np.reshape(self._qval, (2,)*calc_qnum*2)

    def extend(self, qvarT: QVar) -> QOpt:
        if not qvarT.contains(self.qvar):
            raise ValueError("The extension target qvar '" + str(qvarT) + "' does not contain the original qvar '" + str(self.qvar) + "'.")
        
        m_I = qval.eye_operator(qvarT.qnum - self.qnum)

        temp_qval = np.tensordot(self.qval, m_I, ([],[]))

        # rearrange the indices
        count_ext = 0
        r_left = []
        r_right = []
        for i in range(qvarT.qnum):
            if qvarT[i] in self.qvar:
                pos = self.qvar.index(qvarT[i])
                r_left.append(pos)
                r_right.append(self.qnum + pos)
            else:
                r_left.append(2*self.qnum + count_ext)
                r_right.append(qvarT.qnum + self.qvar.qnum + count_ext)
                count_ext += 1

        return QOpt(temp_qval.transpose(r_left + r_right), qvarT)


    def __add__(self, other : QOpt) -> QOpt:
        '''
        Matrix Addition.
        Note that additions between operators on different quantum variables are understood as
        additions on the cylinder extensions.
        '''
        if not isinstance(other, QOpt):
            raise ValueError("A quantum operator can only add another quantum operator.")
        
        # the common qvar
        qvar_all = self._qvar + other._qvar

        # cylinder extension
        self_ext = self.extend(qvar_all)
        other_ext = other.extend(qvar_all)

        # return the result
        return QOpt(self_ext.qval + other_ext.qval, qvar_all, check = False)

    def __matmul__(self, other : QOpt) -> QOpt:
        '''
        Matrix Multiplication.
        Note that multiplications between operators on different quantum variables are understood as
        multiplications on the cylinder extensions.
        '''
        if not isinstance(other, QOpt):
            raise ValueError("A quantum operator can only add another quantum operator.")

        # the common qvar
        qvar_all = self._qvar + other._qvar

        # cylinder extension
        self_ext = self.extend(qvar_all)
        other_ext = other.extend(qvar_all)

        return QOpt(qval.opt_mul(self_ext.qval, other_ext.qval), qvar_all, check = False)
    
    def dagger(self) -> QOpt:
        '''
        Return the conjugate transpose of this expression.
        '''
        return QOpt(qval.opt_dagger(self.qval), self.qvar)
    

    # def init(self, qvar_init: QVar) -> QOpt:
    #     '''
    #     Initialize the quantum expression at variables 'qvar_init'.
    #     '''
    #     P0 = np.array([[1., 0.],
    #                     [0., 0.]])
    #     P1 = np.array([[0., 0.],
    #                     [1., 0.]])
    #     # initialize all the variables in order
    #     temp = self
    #     for var in qvar_init:
    #         exprP0 = QOpt(P0, QVar([var]))
    #         exprP1 = QOpt(P1, QVar([var]))
    #         a = opt_apply(temp, qvarM, P0, (var,))
    #         b = opt_apply(temp, qvarM, P1, (var,))
    #         tempH = a + b
        
    #     return temp