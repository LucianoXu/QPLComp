'''
QPLComp.qval
=====

This package deals with the operations on quantum values, where numpy ndarray are considered as the values.
'''

from .m_methods import np_prec_equal
from .m_methods import Schmidt_decomposition

from .opt_methods import eye_operator

from .opt_methods import opt_mul
from .opt_methods import opt_dagger
from .opt_methods import opt_loewner_le
from .opt_methods import proj_disjunct
from .opt_methods import proj_conjunct