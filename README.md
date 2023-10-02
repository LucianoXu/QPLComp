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


#### `opt_extend(M, qvarM, qvar_all)`
Get the cylinder extension of the given operator `M`, according to all variables `qvar_all` and return the result.
It can also be used to permute the indices of `M`.
- Parameters:
  - `M` : `np.ndarray`, the operator to be extended. Note that it should be a tensor with 2 dimensional indices.
  - `qvarM` : `Sequence[str]`, the indices of `M`.
  - `qvar_all` : `Sequence[str]`, the indices of the extension target.
- Returns: `np.ndarray`, the extension target.

## Subpackage: qexpr
This package provides the data structure and methods for quantum expressions.

A quantum expression is a quantum operator with the corresponding quantum variable. Many methods on the operator level, such as contraction and addition, also exists for quantum expressions. The methods of this package takes care of the details.

### definitions and methods
#### `QVar`
The class for quantum variables (indices)
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
Additions between operators on different quantum variables are understood as additions on the cylinder extension.
- Parameters: `qopt1`, `qopt2` : `QOpt`.
- Returns: `QOpt`.





