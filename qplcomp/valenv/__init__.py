'''
QPLComp.valenv
=====

This package provides a special dictionary [ValEnv] which relates the name of quantum values (as str) to quantum values (as np.ndarray). Note that the ''quantum values'' mentioned here are not indexed with quantum variables. In other words, they are ''literal values''.

The environment will (try to) maintain the uniqueness of each value, and value equivalence is checked with respect to the precision setting of the environment. 

It has an automatic naming strategy for new values. Therefore, it can work to preserve the intermediate calculation results during the simulation of quantum computing and quantum program verification, which helps provide a succint expression.
'''
from .valenv import ValEnv
from .valenv import get_predefined_valenv