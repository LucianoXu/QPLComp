from qplcomp import *
import numpy as np

from env import *
if __name__ == "__main__":
    pass
    ec = ECPointer.Empty(3)
    ec = ec.W_Global_Assum("x", Var("Type"))
    ec = ec.W_Global_Assum("y", Var("x"))
    ec = ec.W_Global_Assum("z", Var("y"))
    ec.envp.print_dec()
    # Demo("X")
    # Demo("CX")
    # Demo("P0 \\vee Pm")
    # Demo("P0 ∧ Pm")
    # Pm = Parser.parse("Pm[q] \\SasakiImply P0[p]")
    # print(Pm)
    # print(Pm.eval())