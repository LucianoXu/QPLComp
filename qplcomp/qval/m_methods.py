# ------------------------------------------------------------
# matrix_methods.py
# ------------------------------------------------------------
from __future__ import annotations
from typing import Any, List, Sequence

import numpy as np 

def np_elementwise_norm(m : np.ndarray) -> np.ndarray:
    '''
    calculate the element wise norm
    '''
    return np.sqrt(m.real * m.real + m.imag * m.imag)

def np_prec_zero(a : np.ndarray, precision : float) -> bool:
    '''
    Check whether the tensor a is zero with respect to the given precision.
    '''
    return np.max(np_elementwise_norm(a)) < precision

def np_prec_equal(a : np.ndarray, b : np.ndarray, precision : float) -> bool:
    '''
    check whether two tensors a and b are equal, according to maximum norm.
    '''
    if a.shape != b.shape :
        return False

    diff : float = np.max(np_elementwise_norm(a - b))  # type: ignore
    return diff < precision


def is_spd(A : np.ndarray, precision : float):
    '''
    Check whether operator A is semi-positive definite.

    Note: it will not check whether A is Hermitian.
    '''
    e_vals = np.linalg.eigvals(A)

    if np.any(e_vals < 0 - precision):
        return False
    else:
        return True

def loewner_le(A : np.ndarray, B : np.ndarray, precision : float):
    '''
    Decide the loewner order of two Hermitian matrices A and B.

    Note: it will not check whether A or B is Hermitian.
    '''

    return is_spd(B-A, precision)

def normalized(vec : np.ndarray) -> np.ndarray:
    '''
    Calculate and return the normalized vector.
    '''
    norm = np.linalg.norm(vec)
    return vec / norm

def complex_dot(vec0 : np.ndarray, vec1 : np.ndarray) -> complex:
    '''
    Calculate the complex vector dot vec0 * vec1.

    Note: vec1 takes the conjugate.
    '''
    return np.sum(vec0 * vec1.conj()) # type: ignore

def Schmidt_decomposition(A : np.ndarray, precision : float) -> np.ndarray:
    '''
    Calculate and return the Schmidt decomposition of a set of vectors given by columns in A. 

    Note: the linear dependent vectors are ruled out (with given precision).
    '''
    # get the space dimension
    dim = A.shape[0]
    ortho = np.array([]).reshape((dim, 0))

    # Schmidt decomposition algorithm
    for i in range(A.shape[1]):
        # check whether it is already the whole space
        if ortho.shape[1] == dim:
            break

        veci = A[:,i]

        # subtract the projection within the existing space
        for j in range(ortho.shape[1]):
            proj_val = complex_dot(veci, ortho[:,j])
            veci = veci - proj_val * ortho[:,j]

        # check whether the result is zero
        if not np_prec_zero(veci, precision):
            veci_normalized = normalized(veci)
            ortho = np.hstack((ortho, veci_normalized.reshape((dim, 1))))
    
    return ortho


def right_non_null_space_h(m : np.ndarray, precision: float) -> np.ndarray:
    '''
    Calculate the right non-zero space of matrix m.
    Note: m should be Hermitian.
    '''
    dim = m.shape[0]
    eigval, eigvec = np.linalg.eigh(m)
    res = np.array([]).reshape((dim,0))
    for i in range(dim):
        if eigval[i] > precision:
            res = np.hstack((res, eigvec[:,i].reshape((dim, 1))))

    return res


def right_null_space(m : np.ndarray, precision : float) -> np.ndarray:
    '''
    Calculate the right-null space of m. Return a matrix consisting of the orthonormal basis as columns.
    '''
    U, S, V = np.linalg.svd(m)

    # find the rank
    rank = len(S)
    for i in range(len(S)):
        if S[i] < precision:
            rank = i
            break

    return V[rank:].transpose().conj()



