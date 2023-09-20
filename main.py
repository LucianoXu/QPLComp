import qplcomp
import numpy as np

if __name__ == "__main__":
    env = qplcomp.optenv.get_predefined_optenv()
    a = np.array([[0.0]])
    env.append(a)
    print(env.append(a))