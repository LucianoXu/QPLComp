
from qplcomp import *
import numpy as np

def Demo(code : str):
    A = Parser.parse(code)
    print("Input String: "+ code)
    print("Parsing Result: " + str(A))
    print("Value: ")
    print(A.eval())
    print()

def test_01():
    Demo("X")
    Demo("CX")


def test_02():
    try:
        Demo("X[p q]")
    except:
        pass
    else:
        raise Exception()

def test_03():
    try:
        Demo("CX[p p]")
    except:
        pass
    else:
        raise Exception()

def test_04():
    Demo("(P0 + P1)[p]")
    Demo("(X * Y)[p]")
    Demo("(X \\otimes X)[p q]")
    Demo("(X ⊗ X)[p q]")
    Demo("(X * X)†[p]")
    Demo("(X * X)^\\dagger[p]")
    Demo("P0 \\vee Pm")
    Demo("P0 ∧ Pm")

def test_05():
    Demo("P0[p] + P1[p]")
    Demo("P0[p] + (-P1)[q]")
    Demo("I[p] - Pm[p]")
    Demo("CX[p q] CX[p q]")
    Demo("H[q] CX[p q] H[q]")
    Demo("Y[q]^\\dagger Y[q]")
    Demo("P0[p] \\otimes P1[q]")
    Demo("P0[p] \\wedge Pm[q]")
    Demo("P0[p] \\vee Pm[q]")

def test_06():
    try:
        Demo("CX[p q] \\otimes X[p]")
    except:
        pass
    else:
        raise Exception()