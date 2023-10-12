from qplcomp import *
import numpy as np

from qplcomp import linalgPP

def Demo(code : str) -> None:
    A = Parser.parse(code)
    print("Input String: "+ code)
    print("Parsing Result: " + str(A))
    print("Value: ")
    print(A.eval())
    print()

if __name__ == "__main__":
    pass
    Demo("X")
    Demo("CX")
    Demo("P0 \\vee Pm")
    Demo("P0 ∧ Pm")
    # Pm = Parser.parse("Pm[q] \\SasakiImply P0[p]")
    # print(Pm)
    # print(Pm.eval())
