#-------------------------------------------------
# definition of quantum value environments
#-------------------------------------------------

from typing import Dict
import numpy as np

from .. import qval

# the default precision for equivalence check
PRECISION_DEFAULT = 1e-10

class ValEnv:
    '''
    The value environment which relates keys (string) to values (tensors)
    Note that the environment will check the equivalence of operators based on
    its precision setting.
    '''
    def __init__(self, precision : float = PRECISION_DEFAULT) -> None:
        self.precision : float = precision
        self._vallib : Dict[str, np.ndarray] = {}

        # the number for auto naming
        self._numbering = 0

    def get_name(self) -> str:
        '''
        Return a key which is not used in the environment.
        '''
        res = "OP" + str(self._numbering)
        self._numbering += 1
        while res in self._vallib:
            res = "OP" + str(self._numbering)
            self._numbering += 1
        return res


    def append(self, value : np.ndarray) -> str:
        '''
        check whether the value already exists in this environment.
        If yes, return the corresponding key.
        If not, create a new item with an auto key and return the key used.
        '''
        if not isinstance(value, np.ndarray):
            raise ValueError("Invalid value. Only np.ndarray is allowed.")
        
        for key in self._vallib:
            if qval.np_prec_equal(value, self._vallib[key], self.precision):
                return key
            
        name = self.get_name()
        self._vallib[name] = value
        return name
    
    def __setitem__(self, key : str, value : np.ndarray) -> None:
        if not isinstance(value, np.ndarray):
            raise ValueError("Invalid value. Only np.ndarray is allowed.")
        self._vallib[key] = value

    def __getitem__(self, key : str) -> np.ndarray:
        return self._vallib[key]
    
from .predefined import predefined_optlib

def get_predefined_valenv() -> ValEnv:
    '''
    Return a predefined operator environment, where many operators are already provided in [.predefined.py]
    '''
    valenv = ValEnv()
    for key in predefined_optlib:
        valenv[key] = predefined_optlib[key]
    return valenv