'''
QPLComp.qval
=====

This package deals with the values in quantum computing and quantum information.

It first defines `QVar`, the class for quantum variables, which are used for indexing quantum values.

Note that we do not consider the change of systems for now. In otherwords, all the quantum operators are square matrices.

Two types of values are included here: `QVal`(quantum values) and `IQVal`(indexed quantum values). `QVal` instances are not indexed by quantum variables, and the operations between them are often limited to quantum values with the same qubit number. `IQVal` are `QVal` indexed by `QVar` instances, which are more flexible, and the operation between `IQVal` instances are understood as those on their cylinder extensions.

Finally, it provides a library `qvallib` with common quantum operators preserved as `QVal` instances.
'''

from .qvar import QVar
from .val import QVal, IQVal

from .qopt import QOpt
from .qso import QSOpt

from .iqopt import IQOpt

from .predefined import qvallib