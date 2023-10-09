'''
The methods for superoperators.
'''

from typing import List

from .mmethods import Loewner_le, is_spd

import numpy as np

def is_qo(kraus : List[np.ndarray], precision : float) -> bool:
    sum_res = np.sum([m @ m.conj().transpose for m in kraus], axis = 0)

    if Loewner_le(sum_res, np.zeros_like(sum_res), precision)\
    or Loewner_le(np.eye(len(sum_res)), sum_res, precision):
        return False
    
    return True

