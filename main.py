from qplcomp import *
import numpy as np

if __name__ == "__main__":
    a = Parser.parse("(X X)†[p]")
    b = Parser.parse("Pm[q]")

    print(a)
    print(a.eval())
    # print(Pm <= Pm.disjunct(P0))

