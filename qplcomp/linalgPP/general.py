import numpy as np

def elementwise_norm(m : np.ndarray) -> np.ndarray:
    '''
    Calculate the element wise norm.
    '''
    return np.sqrt(m.real * m.real + m.imag * m.imag)

def close_zero(a : np.ndarray, precision : float) -> bool:
    '''
    Check whether the tensor a is zero with respect to the given precision.
    '''
    return np.max(elementwise_norm(a)) < precision

def close_equal(a : np.ndarray, b : np.ndarray, precision : float) -> bool:
    '''
    check whether two tensors a and b are equal, according to maximum norm.
    '''
    if a.shape != b.shape :
        return False

    diff : float = np.max(elementwise_norm(a - b))  # type: ignore
    return diff < precision
