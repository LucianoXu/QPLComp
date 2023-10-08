
import numpy as np

def v_normalized(vec : np.ndarray) -> np.ndarray:
    '''
    Calculate and return the normalized vector.
    '''
    norm = np.linalg.norm(vec)
    return vec / norm

def v_complex_dot(vec0 : np.ndarray, vec1 : np.ndarray) -> complex:
    '''
    Calculate the complex vector dot vec0 * vec1.

    Note: vec1 takes the conjugate.
    '''
    return np.sum(vec0 * vec1.conj()) # type: ignore