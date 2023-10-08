from qplcomp import *
import numpy as np

if __name__ == "__main__":
    a = Parser.parse("P0[p]")
    b = Parser.parse("Pm[q]")

    print(a.eval() & b.eval())
    # print(Pm <= Pm.disjunct(P0))

