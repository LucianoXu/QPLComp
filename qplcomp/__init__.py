'''
QPLComp
=====

This package aims at providing the necessary components for the implementation of numerical/symbolic calculation of quantum computing and quantum information. It contains:

- `QPLComp.qval`: the subpackage for quantum values `QVal` and indexed quantum values `IQVal`. Quantum values are those special vectors, operators and super operators used in quantum computing. `QVal` provides a abstract description and supports flexible representations. `IQVal` is quantum values indexed with quantum variables. Most operations involved in quantum computing can be conducted in a direct way.

- `QPLComp.qexpr`: the subpackage for expressions of quantum computing. We implemented a variable system to represent the values of quantum computing with expressions.
'''

from . import qval
from . import qexpr

from .env import Expr, Env

from .qexpr import Parser
from .qexpr import get_default_env


from .qval import QVar
from .qval import QOpt, IQOpt
from .qval import QSOpt, IQSOpt