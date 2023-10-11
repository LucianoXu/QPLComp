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
    
    Pm = Parser.parse("Pm[q]\\otimes Pp[p]").eval()
    Pm : IQOpt
    print(Pm.initwlp(QVar(["q"])))
