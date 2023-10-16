
from __future__ import annotations

from typing import Type, Tuple, Any, TypeVar

import inspect
import os


class Meta_Sys_Error(Exception):
    pass


def Meta_Sys_type_check(obj : object, target_type : Type | Tuple[Type, ...]) -> None:
    '''
    This method checks whether CIC systems works as expected.
    '''

    if isinstance(target_type, tuple):
        for t in target_type:
            if isinstance(obj, t):
                return
        
        raise Meta_Sys_Error("The parameter expression '" + str(obj) + "' should be within type '" + str(target_type) + "', but is of type '"+ str(type(obj)) + "'.")

    elif not isinstance(obj, target_type):
        raise Meta_Sys_Error("The parameter expression '" + str(obj) + "' should be of type '" + str(target_type) + "', but is of type '"+ str(type(obj)) + "'.")


class __META_SYS_INFO__:
    counter = 0
    registered : list[str] = []



class MetaTerm:
    '''
    meta-term
    ```
    _
    ```

    The meta term for objects in the calculus itself.
    All objects are by default abstract and cannot be instantiated.
    Use `@concrete_term` decorator to transform a class to concrete one.
    '''
    meta_term_name : str
    meta_term_def : str
    term_order : int

    def __new__(cls, *args, **kwargs):
        raise Meta_Sys_Error(f"Cannot instantiate abstract proof object {cls}.")

    def is_concrete(self) -> bool:
        return False
    
T = TypeVar('T', bound = MetaTerm)
def meta_term(cls : Type[T]) -> Type[T]:
    '''
    Parse meta term information from the docstring of `MetaTerm` subclasses.
    The docstring should be of form:
    ```
    meta-term-name
    "```"
    meta-term-def
    "```"
    intro-string ...
    ```
    '''
    
    # register
    cls.term_order = __META_SYS_INFO__.counter
    __META_SYS_INFO__.counter += 1
    __META_SYS_INFO__.registered.append(cls.__name__)

    doc : str| None = cls.__doc__
    try:
        if doc is None:
            raise ValueError()
        pos1 = doc.index("```")
        cls.meta_term_name = doc[:pos1].replace("\n","").replace("\t","").replace(" ","")

        doc = doc[pos1 + len("```"):]
        pos2 = doc.index("```")
        cls.meta_term_def = doc[:pos2]
    except ValueError:
        raise Exception(f"Cannot process the meta-term information of class {cls}.")


    return cls

def concrete_term(cls : Type[T]) -> Type[T]:
    '''
    Decorator for concrete meta terms: reload the definition for `__new__` in the class definition by:
    ```Python
    def __new__(cls, *args, **kwargs):
        return object.__new__(cls)
    ```
    '''

    # process meta_term informations
    cls = meta_term(cls)

    def concrete_new(cls, *args, **kwargs):
        return object.__new__(cls)

    cls.__new__ = concrete_new
    cls.is_concrete = lambda self: True
    
    return cls

# decorate the root term
MetaTerm = meta_term(MetaTerm)

@meta_term
class MetaProof(MetaTerm):
    '''
    meta-proof
    ```
    _
    ```
    The proof objects for the calculus itself.
    '''

    def premises(self) -> str:
        raise NotImplementedError()
    
    def conclusion(self) -> str:
        raise NotImplementedError()
    
    def __str__(self) -> str:
        space_len = len(self.meta_term_name) + 3

        # indent, premise
        res = " " * space_len + self.premises()
        if res[-1] == "\n":
            res = res[:-1]
        res = res.replace("\n", "\n" + " " * space_len)
        res += "\n"

        # line
        res += f"({self.meta_term_name}) " + "-"*40 + "\n" 

        # indent conclusion
        res += " " * space_len + self.conclusion() 
        return res
    


####################################################################
# methods on meta system


def meta_term_describe(mt : MetaTerm) -> str:
    '''
    Output a description for the meta term.
    '''
    return f"({mt.meta_term_name}):" + "\n" + mt.meta_term_def



def get_meta_system_def(GLOBAL : dict[str, Any]) -> str:
    '''
    Inspect the current package and extract all definitions of subclass of `MetaTerm`, which finally form the system.

    `GLOBAL` : shoule pass in `global()` result
    '''

    # get the sorted terms
    meta_terms = list(filter(
        lambda obj : inspect.isclass(obj) and issubclass(obj, MetaTerm),GLOBAL.values()
    ))
    meta_terms.sort(key=lambda x: x.term_order)

    res = ""
    for item in meta_terms:
        res += meta_term_describe(item) + "\n\n"

    return res

def meta_system_check(GLOBAL : dict[str, Any], file : str = "") -> None:
    '''
    Checks whether the current meta system is well formed and generate the form.

    `GLOBAL` : shoule pass in `global()` result
    `file` : should pass in `__file__` result
    '''

    # check whether meta terms are properly registered by decorators `meta_term` or `concrete_term`
    for obj in GLOBAL.values():
        if inspect.isclass(obj):
            if issubclass(obj, MetaTerm) and obj.__name__ not in __META_SYS_INFO__.registered:
                raise Exception(f"Class {obj} is subclass of MetaTerm but not registered.")

    # produce the rule doc
    with open(os.path.join(os.path.dirname(file),"meta_rule.txt"), "w", encoding="utf-8") as p:
        p.write(get_meta_system_def(GLOBAL=GLOBAL))
