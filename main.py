from qplcomp import *
import numpy as np

if __name__ == "__main__":
    env = get_predefined_valenv()
    QExpr.set_valenv(env)

    a = QOpt("CX[p q]")
    b = QOpt("CX[q p]")

    # dirac-notation decision procedure?

    P0 = QProj("P0[q]")
    Pm = QProj("Pm[p]")

    x = Pm & P0

    print(x)
    print(x.qval)

    # print(Pm <= Pm.disjunct(P0))

