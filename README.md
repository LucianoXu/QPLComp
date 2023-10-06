# QPLComp

This package aims at providing the necessary components for the implementation of quantum programming languages.


## Subpackage: valenv
The subpackage `valenv` (value environment) provides a special dictionary `ValEnv` which relates the name of quantum values (as str) to quantum values (as np.ndarray). Note that the ''quantum values'' mentioned here are not indexed with quantum variables. In other words, they are ''literal values''.

The environment will (try to) maintain the uniqueness of each value, and value equivalence is checked with respect to the precision setting of the environment. 

It has an automatic naming strategy for new values. Therefore, it can work to preserve the intermediate calculation results during the simulation of quantum computing and quantum program verification, which helps provide a succint expression.

### definition and methods
#### `valenv.ValEnv`
The value environment which relates keys (string) to values (tensors).
##### `ValEnv(precision = 1e-10)`
Create an empty value environment.
- Parameters: `precision` : `float`, the setting of precision.
- Returns: `None`.
- Error: never.
  
##### `append(value)`
Check whether the value already exists in this environment.
If yes, return the corresponding key.
If not, create a new item with an auto key and return the key used.
- Parameters: `value` : `np.ndarray`, the value to append in the environment.
- Returns: `str`, the name of the value in the environment.
- Error: `ValueError` when `value` is not `np.ndarray`.

##### `env[key]=value` (magic method)
Set the corresponding value of the key in this environment
- Parameters:
  - `env` : a `ValEnv` instance.
  - `key` : `str`.
  - `value` : `np.ndarray`.
- Returns: `None`.
- Error: `ValueError` when `value` is not `np.ndarray`.

##### `env[key]` (magic method)
Get the corresponding value of the key in this environment.
- Parameters:
  - `env` : a `ValEnv` instance.
  - `key` : `str`.
- Returns: `np.ndarray`, the corresponding value
- Error: `KeyError` when `key` is not in `env`.

#### `get_predefined_valenv()`
Get the predefined value environment containing the common quantum values.
- Parameters: none.
- Returns: `ValEnv`
- Error: never.

## Subpackage: qval
This package deals with the operations on quantum values, where numpy ndarray are considered as the values.

### definitions and methods


#### `np_prec_equal(a, b, precision)`
Check whether two tensors `a` and `b` are equal according to the maximum norm difference.
- Parameters:
  - `a`, `b` : `np.ndarray`, the two tensors to be compared.
  - `precision` : `float`, the threshold precision for equivalence.
- Returns: `bool`, whether `a` and `b` is equal.

#### `Schmidt_decomposition(A, precision)`
Calculate and return the Schmidt decomposition of a set of vectors given by columns in `A`. 

Note: the linear dependent vectors are ruled out (with given precision).
- Parameters: 
  - `A` : `np.ndarray`, a matrix.
  - `precision` : `float`.\
- Returns: `np.ndarray`, a matrix containing the orthonormal basis as columns.


#### `opt_dagger(A)`
Calculate and return the conjugate transpose of operator tensor A.
- Parameters: `A` : `np.ndarray`, an operator tensor.
- Returns: `np.ndarray`, the conjugate transpose.


#### `opt_mul(A, B)`
Calculate and return the multiplication `A @ B`, where `A` and `B` are tensors for quantum operators with the same qubit number.
- Parameters: `A`, `B` : `np.ndarray`, the two operator tensors.
- Returns: `np.ndarray`, the multiplication result.

#### `opt_loewner_le(A, B, precision)`
Decide whether the two operator tensors `A` and `B` follow the loewner order `A <= B`. The comparison between eigenvalues are conducted with respected to the given precision.
- Parameters: 
  - `A`, `B` : `np.ndarray`.
  - `precision` : `float`.
- Returns: `bool`, whether `A` is smaller than `B`.

#### `proj_disjunct(P, Q, precision)`
Calculate and return the disjunction of subspaces represented by projectors `P` and `Q`.

`P` and `Q` are operator tensors.
- Parameters: 
  - `P`, `Q` : `np.ndarray`.
  - `precision` : `float`, used to decide the linear dependency among vectors.
- Returns: `np.ndarray`.

#### `proj_conjunct(P, Q, precision)`
Calculate and return the conjunction of subspaces represented by projectors `P` and `Q`.

`P` and `Q` are operator tensors.
- Parameters: 
  - `P`, `Q` : `np.ndarray`.
  - `precision` : `float`, used to decide the linear dependency among vectors.
- Returns: `np.ndarray`.



**Note: this method will not check whether `A` and `B` are Hermitian or not.**
- Parameters:
  - `A`, `B` : `np.ndarray`.
  - `precision` : `float`.
- Returns: `bool`, whether `A` is smaller than `B`.

## Subpackage: qexpr
This package provides the data structure and methods for quantum expressions.

A quantum expression is a quantum operator with the corresponding quantum variable. Many methods on the operator level, such as contraction and addition, also exists for quantum expressions. The methods of this package takes care of the details.

### definitions and methods
#### `QVar`
The class for quantum variables (indices)
##### The methods same as `List[str]`:
  - `qvar[i]` (`__getitem__`)
  - `var in qvar` (`__contains__`)
  - `index(v)`
##### `QVar(qvls)`
Create a quantum variable instance.
- Parameters: `qvls` : 
    - `List[str]`, a list of the name of quantum variables;
    - or `str`, a string to be parsed as a `qvls`.
- Returns: `None`.
- Errors: `ValueError` when there are repeated names in the list `qvls`.

##### `qvar1 + qvar2` (magic method)
Append the quantum variables in `qvar2` after `qvar1` to get the united quantum variable.
- Parameters: `qvar1`, `qvar2` : `QVar`.
- Returns: `QVar`.

##### `contains(other)`
Test whether this quantum variable contains `other`.
- Parameters: `other` : `QVar`.
- Returns: `bool`, whether `self` contains `other`.

#### `QExpr`
The class for quantum expressions, which has three components:
- An identifier (`str`)
- A quantum operator (`np.ndarray`)
- A quantum variable (`QVar`)
  
##### `QExpr.valenv` : `valenv.ValEnv`
The global value environment for quantum expressions.

##### `QExpr(*args, **kwargs)`
Create a quantum expression with multiple ways.
- Parameters:
  - `args`:
    - a string of `qval[qvar]` to be parsed, here `qval` is the id.
    - two arguments: the first can be an id (of type `str`) or a quantum value (of type `np.ndarray`), and the second can be a `QVar` instance or a string to be parsed.
  - `kwargs`:
    - `check=True` : `bool`, controlls wether data check is performed.
- Returns: `None`.

##### `extend(qvarT)`
Extend the expression according to the given quantum variables `qvarT`, and return the result.
- Parameters: `qvarT` : `QVar`, the target quantum variable. **`qvarT` should contain `self.qvar`.**
- Returns: `QExpr` (or the corresponding child class), the extension result.

##### `id` (property)
Return the id of this quantum expression (within the global value environment).
- Parameters: none.
- Returns: `str`.

##### `qval` (property)
Return the value of this quantum expression.
- Parmeters: none.
- Returns: `np.ndarray`.

##### `qvar` (property)
Return the quantum variable of this quantum expression.
- Parameters: none.
- Returns: `QVar`.


##### `qnum` (property)
Return the qubit number of this quantum expression.
- Parameters: none.
- Returns: `int`.


#### `QOpt(QExpr)`
Quantum operator - a special kind of quantum expression. It corresponds to matrices like density operators, unitary operators and Hermitian operators.

##### `qopt1 + qopt2` (magic method)
For quantum operators `qopt1` and `qopt2`, return the addition result.
Additions between operators on different quantum variables are understood as additions on the cylinder extensions.
- Parameters: `qopt1`, `qopt2` : `QOpt`.
- Returns: `QOpt`.

##### `qopt1 @ qopt2` (magic method)
For quantum operators `qopt1` and `qopt2`, return the matrix multiplication result.
Multiplications between operators on different quantum variables are understood as multiplications on the cylinder extensions.
- Parameters: `qopt1`, `qopt2` : `QOpt`.
- Returns: `QOpt`.

##### `dagger()`
Return the conjugate transpose of this expression.
- Parameters: none.
- Returns: `QOpt`.

##### `qopt1 <= qopt2` (magic method)
Decide the Loewner order `qopt1 <= qopt2`.
- Parameters: `qopt1`, `qopt2` : `QOpt`.
- Returns: `bool`, whether `qopt1` is smaller than `qopt2`.



#### `QProj`
Quantum projector - a special kind of quantum expression.
A projector `P` satisfies `P^2 = P`.


##### `disjunct(other)` (or `self | other`)
Calculate and return the disjunction for subspaces of `self` and `other`.

The magic method notation for disjunction is `self | other`.
- Parameters: `other` : `QProj`.
- Returns: `QProj`, the disjunction.
- Errors: `ValueError` when `other` is not `QProj`.

##### `conjunct(other)` (or `self & other`)
Calculate and return the conjunction for subspaces of `self` and `other`.

The magic method notation for conjunction is `self & other`.
- Parameters: `other` : `QProj`.
- Returns: `QProj`, the conjunction.
- Errors: `ValueError` when `other` is not `QProj`.
