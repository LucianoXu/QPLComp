'''
QPLComp.qexpr
=====

This package provides the data structure and methods for quantum expressions.

A quantum expression is a quantum operator with the corresponding quantum variable. Many methods on the operator level, such as contraction and addition, also exists for quantum expressions. The methods of this package takes care of the details.

'''

from .qvar import QVar
from .qexpr import QExpr, QOpt