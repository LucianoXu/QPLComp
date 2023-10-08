# ------------------------------------------------------------
# parser.py
#
# parser
# ------------------------------------------------------------
from __future__ import annotations
import ply.yacc as yacc

from .lexer import tokens, lexer

from ..sugar import type_check

from ..env import Env, Expr

from ..qval import qvallib, QOpt
from .eqopt import EQOpt

def get_default_env() -> Env:
    '''
    Return the environment with predefined quantum values.
    '''
    env = Env()
    for key in qvallib:
        val = qvallib[key]
        if isinstance(val, QOpt):
            env[key] = EQOpt(val, env)
        else:
            raise Exception("Unexpected Exception.")

    return env


class Parser:
    Global : Env = get_default_env()

    @staticmethod
    def set_global_env(env : Env) -> None:
        '''
        Set the Global environment
        '''
        type_check(env, Env)
        Parser.Global = env

    @staticmethod
    def parse(code : str) -> Expr:
        res = parser.parse(code)
        if not isinstance(res, Expr):
            raise Exception("Unexpected Exception.")
        
        return res



############################################################
# parsing rules
############################################################

precedence = (
    ('left', '+', '-'),
    ('left', '*', 'OTIMES'),
    ('left', 'DAGGER'),
)

def p_output(p):
    '''
    output  : eiqopt
            | eqopt
    '''
    p[0] = p[1]

from ..env import Variable
def p_variable(p):
    '''
    variable    : ID
    '''
    p[0] = Variable(p[1], Parser.Global)


from .eiqopt import EIQOpt
def p_eiqopt(p):
    '''
    eiqopt  : eqopt eqvar
    '''
    p[0] = EIQOpt(p[1], p[2], Parser.Global)


from .eqopt import EQOpt, EQOptAdd, EQOptNeg, EQOptSub, EQOptMul, EQOptDagger, EQOptTensor
def p_eqopt(p):
    '''
    eqopt   : variable
            | '(' eqopt ')'
            | '(' '-' eqopt ')'
            | eqopt '+' eqopt
            | eqopt '-' eqopt
            | eqopt '*' eqopt
            | eqopt eqopt %prec '*'
            | eqopt DAGGER
            | eqopt OTIMES eqopt
    '''
    if len(p) == 2:
        p[0] = p[1]
    elif len(p) == 4 and p[1] == '(':
        p[0] = p[2]
    elif len(p) == 5:
        p[0] = EQOptNeg(p[3], Parser.Global)
    elif p[2] == '+':
        p[0] = EQOptAdd(p[1], p[3], Parser.Global)
    elif p[2] == '-':
        p[0] = EQOptSub(p[1], p[3], Parser.Global)
    elif p[2] == '*':
        p[0] = EQOptMul(p[1], p[3], Parser.Global)
    elif len(p) == 3 and p.slice[2].type == 'eqopt':
        p[0] = EQOptMul(p[1], p[2], Parser.Global)
    elif p.slice[2].type == 'DAGGER':
        p[0] = EQOptDagger(p[1], Parser.Global)
    elif p.slice[2].type == 'OTIMES':
        p[0] = EQOptTensor(p[1], p[3], Parser.Global)
    else:
        raise Exception()


from .eqvar import EQVar
def p_eqvar(p):
    '''
    eqvar   : qvar
    '''
    p[0] = EQVar(p[1], Parser.Global)

from ..qval import QVar
def p_qvar(p):
    '''
    qvar : qvar_pre ']'
    '''
    p[0] = QVar(p[1])


def p_qvar_pre(p):
    '''
    qvar_pre : '['
                | qvar_pre ID
    '''
    if p[1] == '[':
        p[0] = []
    else:
        p[0] = p[1] + [p[2]]

def p_error(p):
    if p is None:
        raise RuntimeError("unexpected end of file")
    raise RuntimeError("Syntax error in input: '" + str(p.value) + "'.")



# Build the parser
parser = yacc.yacc()