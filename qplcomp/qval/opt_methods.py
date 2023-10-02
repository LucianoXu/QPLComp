# ------------------------------------------------------------
# methods.py
#
# Note: the quantum operators here in concern are tensors with 
# (2*qnum) indices, with the row indices in front of the column indices.
# ------------------------------------------------------------
from __future__ import annotations
from typing import Any, List, Sequence

import numpy as np 

def np_prec_equal(a : np.ndarray, b : np.ndarray, precision : float) -> bool:
    '''
    check whether two tensors a and b are equal, according to maximum norm.
    '''
    if a.shape != b.shape :
        return False

    diff : float = np.max(np_complex_norm(a - b))  # type: ignore
    return diff < precision


def np_complex_norm(m : np.ndarray) -> np.ndarray:
    '''
    calculate the element wise norm
    '''
    return np.sqrt(m.real * m.real + m.imag * m.imag)

def get_opt_qnum(m : np.ndarray) -> int:
    '''
    get the qubit number of a operator tensor
    '''
    if not isinstance(m, np.ndarray):
        raise Exception()
    
    for dim in m.shape:
        if dim != 2:
            raise ValueError()

    if len(m.shape) % 2 == 1:
        raise ValueError()
    else:
        return len(m.shape)//2

def check_unity(m : np.ndarray, precision : float) -> bool:
    '''
    check whether tensor m is unitary
    m: tensor of shape (2,2,...,2), with the row indices in front of the column indices
    '''

    if len(m.shape) % 2 == 1:
        return False

    for dim in m.shape:
        if dim != 2:
            return False
    
    # calculate the dim for matrix
    dim_m : int = 2**(len(m.shape)//2)
    matrix = m.reshape((dim_m, dim_m))

    # check the equality of U^dagger @ U and I

    if not np_prec_equal(matrix @ np.transpose(np.conj(matrix)), np.eye(dim_m), precision):
        return False
    return True


def check_hermitian_predicate(m : np.ndarray, precision : float) -> bool:
    '''
    check whether tensor m is hermitian and 0 <= m <= I
    m: tensor of shape (2,2,...,2), with the row indices in front of the column indices
    '''

    if len(m.shape) % 2 == 1:
        return False

    for dim in m.shape:
        if dim != 2:
            return False
    
    # calculate the dim for matrix
    dim_m = 2**(len(m.shape)//2)
    matrix = m.reshape((dim_m, dim_m))

    # check the equivalence of U^dagger @ U and I
    if not np_prec_equal(matrix, np.transpose(np.conj(matrix)), precision):
        return False

    # check 0 <= matrix <= I
    e_vals = np.linalg.eigvals(matrix)
    if np.any(e_vals < 0 - precision) or np.any(e_vals > 1 + precision):
        return False
        
    return True


def eye_operator(qubitn : int) -> np.ndarray:
    '''
    return the identity matrix of 'qubitn' qubits, in the form of a (2,2,2,...) tensor, row indices in the front.
    '''
    return np.eye(2**qubitn).reshape((2,)*qubitn*2)

def dagger(M : np.ndarray) -> np.ndarray:
    '''
    for a tensor M with shape (2,2,2,...), return M^dagger
    Note: M should have been already checked
    '''
    nM = len(M.shape)//2
    trans = list(range(nM, nM*2)) + list(range(0, nM))
    return np.conjugate(M).transpose(trans)


# ################################### operation with qvars
def opt_mul(A : np.ndarray, B : np.ndarray) -> np.ndarray:
    '''
    Calculate and return the multiplication A @ B, where A and B are tensors for quantum operators with the same qubit number.
    '''
    if get_opt_qnum(A) != get_opt_qnum(A):
        raise ValueError("The two tensors should have the same number of qubit numbers.")
    
    _A = tensor_to_matrix(A)
    _B = tensor_to_matrix(B)
    return matrix_to_tensor(_A @ _B)


def opt_apply(M : np.ndarray, qvarM: Sequence[str], O : np.ndarray, qvarO : Sequence[str]) -> np.ndarray:
    '''
    conduct the transformation O.M.O^dagger and return the result operator
    qvarM: qvar sequence of qubits in M
    qvarO: qvar sequence of qubits in O

    Note: the operators M and O should have been checked already

    [index sequence of tensor M (and O)]

            qvar == [q1, q2, q3, ... , qn]

              n  n+1 n+2 n+3     2n-2 2n-1
              |   |   |   |  ...  |   |
             ---------------------------
            | q1  q2  q3     ...      qn|
             ---------------------------
              |   |   |   |  ...  |   |
              0   1   2   3      n-2 n-1

    '''
    nH = len(qvarM)
    nM = len(qvarO)
    # decide the indices for contraction. note that O^dagger is accessed by its conjugate and the same index list iM_ls
    iM_ls = list(range(nM, 2*nM))
    iH_left_ls = [qvarM.index(v) for v in qvarO]
    iH_right_ls = [i + nH for i in iH_left_ls]

    # decide the rearrangements, since the standard rearrangement is not what we want
    count_rem_MH = 0
    count_rem_HMd = nH
    rearrange_MH = []
    rearrange_HMd = []
    for i in range(nH):
        if i in iH_left_ls:
            rearrange_MH.append(2*nH-nM + qvarO.index(qvarM[i]))
        else:
            rearrange_MH.append(count_rem_MH)
            count_rem_MH += 1
        if i + nH in iH_right_ls:
            rearrange_HMd.append(2*nH-nM + qvarO.index(qvarM[i - nH]))
        else:
            rearrange_HMd.append(count_rem_HMd)
            count_rem_HMd += 1

    rearrange_MH = rearrange_MH + list(range(nH - nM, 2*nH - nM))
    rearrange_HMd = list(range(nH)) + rearrange_HMd

    # conduct the contraction and rearrange the indices
    temp1 = np.tensordot(M, O, (iH_left_ls, iM_ls)).transpose(rearrange_MH)
    temp2 = np.tensordot(temp1, np.conjugate(O), (iH_right_ls, iM_ls)).transpose(rearrange_HMd)
    return temp2    

def opt_init(M : np.ndarray, qvarM: Sequence[str], qvar_init: Sequence
[str]) -> np.ndarray:
    '''
    initialize the operator M at variables 'qvar_init'
    '''
    P0 = np.array([[1., 0.],
                    [0., 0.]])
    P1 = np.array([[0., 0.],
                    [1., 0.]])
    # initialize all the variables in order
    temp = M
    for var in qvar_init:
        a = opt_apply(temp, qvarM, P0, (var,))
        b = opt_apply(temp, qvarM, P1, (var,))
        tempH = a + b
    
    return temp

def tensor_to_matrix(t : np.ndarray) -> np.ndarray:
    '''
    transform the quantum operator from a tensor to a matrix
    '''
    nM = len(t.shape)//2
    ndim = 2**nM
    return t.reshape((ndim, ndim))


def matrix_to_tensor(t : np.ndarray) -> np.ndarray:
    '''
    transform the quantum operator from a matrix to a tensor
    '''
    qubitn = round(np.log2(t.shape[0]))
    return t.reshape((2,)*2*qubitn)

