'''

This file provides some syntax sugar for the project.

'''
from __future__ import annotations
from typing import Type, Tuple

def type_check(obj : object, target_type : Type | Tuple[Type, ...]) -> None:
    '''
    The method to check the type of this object. It will raise a TypeError if the type of expr is not target_type.
    '''
    if isinstance(target_type, tuple):
        for t in target_type:
            if isinstance(obj, t):
                return
        
        raise TypeError("The parameter expression '" + str(obj) + "' should be within type '" + str(target_type) + "', but is of type '"+ str(type(obj)) + "'.")

    elif not isinstance(obj, target_type):
        raise TypeError("The parameter expression '" + str(obj) + "' should be of type '" + str(target_type) + "', but is of type '"+ str(type(obj)) + "'.")
