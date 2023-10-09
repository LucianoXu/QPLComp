from qplcomp import *
import numpy as np

def Demo(code : str) -> None:
    A = Parser.parse(code)
    print("Input String: "+ code)
    print("Parsing Result: " + str(A))
    print("Value: ")
    print(A.eval())
    print()

if __name__ == "__main__":
    pass
    Demo("(X + X) (X)")
    print(type(Parser.Global["E'Set0"]))
    # Demo("P0")
    # Demo("P0[p] + (- P1[p])")

    # print(Pm <= Pm.disjunct(P0))

