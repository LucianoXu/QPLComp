
import numpy as np

from .general import close_zero, close_equal

from .vmethods import v_normalized, v_complex_dot

def column_simplest(A : np.ndarray, precision : float) -> np.ndarray:
    '''
    Reduce the matrix `A` to the column-simplest form, with pivots being `1`, using only column operations.
    Extra zero columns are thrown away.
    Matrix `A` need not to be square.
    '''
    res = np.array([]).reshape((len(A), 0))

    for i in range(A.shape[0]):

        # find the pivot
        pivot_norm = 0.
        pivot_j = -1
        for j in range(A.shape[1]):
            if np.abs(A[i][j]) > pivot_norm + precision:
                pivot_norm = np.abs(A[i][j])
                pivot_j = j

        if pivot_j != -1:

            # set pivot to 1
            pivot_col = A[:, [pivot_j]] / A[i, pivot_j]
            A = np.hstack((A[:, :pivot_j], A[:, pivot_j+1:]))
            res = np.hstack((res, pivot_col))

            # subtraction on other columns
            for j in range(A.shape[1]):
                A[:,[j]] -= A[i][j] * pivot_col

    # reduse res to simplest form

    for j in range(1, res.shape[1]):
        pivot_i = 0
        while(res[pivot_i, j] < precision):
            pivot_i += 1
        
        for _j in range(j):
            res[:, [_j]] -= res[pivot_i, _j] * res[:, [j]]

    return res
                


def column_space(A : np.ndarray, precision : float) -> np.ndarray:
    '''
    Calculate a set of orthonormal basis of the column space of A.
    This is also the right non-zero space of A, because the right zero space is orthogonal to the column space.

    It is implemented by Schmidt decomposition.

    Note: the linear dependent vectors are ruled out (with given precision).


    Parameters:
        - A : np.ndarray, the matrix.
        - precision : float.

    Returns: np.ndarray, a matrix with columns being the orthonormal basis.
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

        # subtract the projector within the existing space
        for j in range(ortho.shape[1]):
            proj_val = v_complex_dot(veci, ortho[:,j])
            veci = veci - proj_val * ortho[:,j]

        # check whether the result is zero
        if not close_zero(veci, precision):
            veci_normalized = v_normalized(veci)
            ortho = np.hstack((ortho, veci_normalized.reshape((dim, 1))))
    
    return ortho


def row_space(A : np.ndarray, precision: float) -> np.ndarray:
    '''
    Calculate a set of orthonormal basis of the row space of A.
    Based on the row space-column space theorem, the row space is calculate throw row_space method.

    Note: the linear dependent vectors are ruled out (with given precision).

    Parameters:
        - A : np.ndarray, the matrix.
        - precision : float.

    Returns: np.ndarray, a matrix with columns being the orthonormal basis.
    '''
    return column_space(A.transpose().conj(), precision)


def right_null_space(A : np.ndarray, precision : float) -> np.ndarray:
    '''
    Calculate the right-null space of A. 
    It is implemented through a SVD decomposition on A.

    Parameters:
        - A : np.ndarray, the matrix.
        - precision : float.

    Returns: np.ndarray, a matrix with columns being the orthonormal basis.
    '''
    U, S, V = np.linalg.svd(A)

    # find the rank
    rank = len(S)
    for i in range(len(S)):
        if S[i] < precision:
            rank = i
            break

    return V[rank:].transpose().conj()

def support(A : np.ndarray, precision: float) -> np.ndarray:
    '''
    Calculate the support of A.
    Parameters: 
        - `self` : `np.ndarray`, matrix, should be Hermitian.
        - `precision` : `float`.
    Returns: `np.ndarray`, a projector matrix.
    '''

    eigval, eigvec = np.linalg.eigh(A)

    res = np.zeros_like(A)
    for i in range(len(eigval)):
        if np.abs(eigval[i]) > precision:
            res += eigvec[:, [i]] @ eigvec[:, [i]].conj().transpose()

    return res    


#######################################################################
#
# Property Verification Methods.
#
#######################################################################

def is_unitary(A : np.ndarray, precision : float) -> bool:
    '''
    Check whether matrix A is unitary.

    Parameters:
        - A : np.ndarray, a square matrix.
        - precision : float.
    Returns: bool, whether A is unitary.
    '''

    # check the equality of U^dagger @ U and I
    if not close_equal(A @ A.transpose().conj(), np.eye(A.shape[0]), precision):
        return False
    
    return True


def is_Hermitian(A : np.ndarray, precision : float) -> bool:
    '''
    Check whether matrix A is Hermitian.

    Parameters:
        - A : np.ndarray, a square matrix.
        - precision : float.
    Returns: bool, whether A is Hermitian.
    '''

    # check the equality of U^dagger @ U and I
    if not close_equal(A, A.transpose().conj(), precision):
        return False
    
    return True

def is_pdo(A : np.ndarray, precision : float) -> bool:
    '''
    Check whether matrix `A` can be considered as a partial density operator. That is, `A` is semipositive definite and `tr(A) <= 1`.
    '''

    # check whether A is spd
    if not is_spd(A, precision):
        return False
    
    # check whether tr(A) <= 1
    if np.trace(A) > 1 + precision:
        return False
    
    return True


def is_spd(A : np.ndarray, precision : float):
    '''
    Check whether operator A is semi-positive definite.

    Parameters:
        - A : np.ndarray, a square matrix.
        - precision : float.
    Returns: bool, whether A is semi-positive definite.
    '''
    if not is_Hermitian(A, precision):
        return False

    e_vals = np.linalg.eigvals(A)

    if np.any(e_vals < 0 - precision):
        return False
    else:
        return True

def Loewner_le(A : np.ndarray, B : np.ndarray, precision : float):
    '''
    Decide the loewner order of two Hermitian matrices A and B.

    Note: it will not check whether A or B is Hermitian.

    Parameters:
        - A, B : np.ndarray, two square matrices.
        - precision : float.
    Returns: bool, whether A <= B in Loewner order.

    '''

    e_vals = np.linalg.eigvals(B - A)

    if np.any(e_vals < 0 - precision):
        return False
    else:
        return True

def is_effect(A : np.ndarray, precision : float) -> bool:
    '''
    Check whether matrix A represents a quantum effect. That is, A is Hermitian and 0 <= A <= I.

    Parameters:
        - A : np.ndarray, a square matrix.
        - precision : float.
    Returns: bool, whether A represents a quantum effect.
    '''

    # check the A is Hermitian
    if not is_Hermitian(A, precision):
        return False

    # check 0 <= matrix <= I
    e_vals = np.linalg.eigvals(A)
    if np.any(e_vals < 0 - precision) or np.any(e_vals > 1 + precision):
        return False
        
    return True


def is_projector(A : np.ndarray, precision : float) -> bool:
    '''
    Check whether matrix A is a projector. That is, A is Hermitian and A^2 = A.

    Parameters:
        - A : np.ndarray, a square matrix.
        - precision : float.
    Returns: bool, whether A is a projector.
    '''

    # check the A is Hermitian
    if not is_Hermitian(A, precision):
        return False

    # check whether A^2 = A
    if not close_equal(A @ A, A, precision):
        return False
        
    return True