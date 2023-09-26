from qplcomp import *
import numpy as np

if __name__ == "__main__":
    env = get_predefined_valenv()
    QExpr.set_valenv(env)

    a = QOpt("I[q]")
    c = QOpt("CX[q d]")

    b = a + c
    print(b)
    print(b.qval)