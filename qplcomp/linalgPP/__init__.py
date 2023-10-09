'''
qplcomp.linalgPP
=====

This package is the plus version of `np.linalg`. It contains more algorithms of linear algebra not included in `np.linalg`.

'''
from .mmethods import row_space
from .mmethods import column_space
from .mmethods import right_null_space

from .mmethods import is_unitary
from .mmethods import is_effect
from .mmethods import is_pdo
from .mmethods import is_spd
from .mmethods import is_projector

from .mmethods import Loewner_le

from .somethods import is_qo