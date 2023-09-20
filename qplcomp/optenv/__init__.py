'''
QPLComp.optenv
=====

This package provides a special dictionary [OptEnv] which relates the name of quantum operators (as str) to quantum operators (as np.ndarray). Note that the ''quantum operator'' mentioned here are not indexed with quantum variables. In other words, they are ''literal values''.

The environment will (try to) maintain the uniqueness of each operator, and operator equivalence is checked with respect to the precision setting of the environment. 

It has an automatic naming strategy for new values. Therefore, it can work to preserve the intermediate calculation results during the simulation of quantum computing and quantum program verification, which helps provide a succint expression.
'''
from .optenv import OptEnv
from .optenv import get_predefined_optenv