'''

Defines the defensive coding strategy and the corresponding error type.

'''
from __future__ import annotations
from typing import Type, Tuple

class CIC_SYS_Error(Exception):
    pass


def CIC_SYS_type_check(obj : object, target_type : Type | Tuple[Type, ...]) -> None:
    '''
    This method checks whether CIC systems works as expected.
    '''

    if isinstance(target_type, tuple):
        for t in target_type:
            if isinstance(obj, t):
                return
        
        raise CIC_SYS_Error("The parameter expression '" + str(obj) + "' should be within type '" + str(target_type) + "', but is of type '"+ str(type(obj)) + "'.")

    elif not isinstance(obj, target_type):
        raise CIC_SYS_Error("The parameter expression '" + str(obj) + "' should be of type '" + str(target_type) + "', but is of type '"+ str(type(obj)) + "'.")

class CICError(Exception):
    '''
    This error corresponds to the invalid operation from the user in the CIC system.
    '''
    pass

