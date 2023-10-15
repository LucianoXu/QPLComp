# QPLComp

This package aims at providing the necessary components for the implementation of numerical/symbolic calculation of quantum computing and quantum information. It contains:

- `QPLComp.qval`: the subpackage for quantum values `QVal` and indexed quantum values `IQVal`. Quantum values are those special vectors, operators and super operators used in quantum computing. `QVal` provides a abstract description and supports flexible representations. `IQVal` is quantum values indexed with quantum variables. Most operations involved in quantum computing can be conducted in a direct way.

- `QPLComp.qexpr`: the subpackage for expressions of quantum computing. With a variable system, we can represent the concepts of quantum computing with expressions, and enable symbolic calculation to some extent.


# CICPy

Principle of implementation:
- The global environment will always remain well-formed.
- Typed expressions are represented by `Expr` classes.
- The proof of typing is preserved as the `_T` member for that expression.
- The definitional equality of CIC is represented by the `__eq__` relation for `Expr` classes.

It is better to consider Dirac notations as the new sorts of CIC, because they follow different calculation rules, and in this way we can embed the operations of Dirac notations into the CIC system directly.