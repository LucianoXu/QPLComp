#-------------------------------------------------
# definition of operator environments
#-------------------------------------------------

from typing import Dict
import numpy as np

from .. import qopt

# the default precision for equivalence check
PRECISION_DEFAULT = 1e-10

class OptEnv:
    '''
    The operator environment which relates keys (string) to values (tensors)
    Note that the environment will check the equivalence of operators based on
    its precision setting.
    '''
    def __init__(self, precision : float = PRECISION_DEFAULT) -> None:
        self.precision : float = precision
        self._optlib : Dict[str, np.ndarray] = {}

        # the number for auto naming
        self._numbering = 0

    def get_name(self) -> str:
        '''
        Return a key which is not used in the environment.
        '''
        res = "OP" + str(self._numbering)
        self._numbering += 1
        while res in self._optlib:
            res = "OP" + str(self._numbering)
            self._numbering += 1
        return res


    def append(self, value : np.ndarray) -> str:
        '''
        check whether the value already exists in this environment.
        If yes, return the corresponding key.
        If not, create a new item with an auto key and return the key used.
        '''
        for key in self._optlib:
            if qopt.np_prec_equal(value, self._optlib[key], self.precision):
                return key
            
        name = self.get_name()
        self._optlib[name] = value
        return name
    
    def __setitem__(self, key : str, value : np.ndarray) -> None:
        self._optlib[key] = value

    def __getitem__(self, key : str) -> np.ndarray:
        return self._optlib[key]
    
from .predefined import predefined_optlib

def get_predefined_optenv() -> OptEnv:
    '''
    Return a predefined operator environment, where many operators are already provided in [.predefined.py]
    '''
    optenv = OptEnv()
    for key in predefined_optlib:
        optenv[key] = predefined_optlib[key]
    return optenv