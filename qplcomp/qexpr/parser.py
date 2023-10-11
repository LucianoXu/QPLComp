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

from ..qval import qvallib, QOpt, QSOpt
from .eqopt import EQOpt
from .eqso import EQSOpt

def get_default_env() -> Env:
    '''
    Return the environment with predefined quantum values.
    '''
    env = Env()
    for key in qvallib:
        val = qvallib[key]
        if isinstance(val, QOpt):
            env[key] = EQOpt(val, env)
        elif isinstance(val, QSOpt):
            env[key] = EQSOpt(val, env)
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
    ('right', 'SASAKI_IMPLY'),
    ('left', 'SASAKI_CONJUNCT'),
    ('left', 'DISJUNCT'),
    ('left', 'CONJUNCT'),
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


from .eiqopt import *
def p_eiqopt(p):
    '''
    eiqopt  : eqopt eqvar
            | '(' eiqopt ')'
            | '(' '-' eiqopt ')'
            | eiqopt '+' eiqopt
            | eiqopt '-' eiqopt
            | eiqopt '*' eiqopt
            | eiqopt eiqopt %prec '*'
            | eiqopt DAGGER
            | eiqopt OTIMES eiqopt
            | eiqopt DISJUNCT eiqopt
            | eiqopt CONJUNCT eiqopt
            | eiqopt SASAKI_IMPLY eiqopt
            | eiqopt SASAKI_CONJUNCT eiqopt
    '''
    if len(p) == 3 and p.slice[1].type == 'eqopt' and p.slice[2].type == 'eqvar':
        p[0] = EIQOpt(p[1], p[2], Parser.Global)
    elif len(p) == 4 and p[1] == '(' and p[3] == ')':
        p[0] = p[2]
    elif len(p) == 5 and p[2] == '-':
        p[0] = EIQOptNeg(p[3], Parser.Global)
    elif len(p) == 4 and p[2] == '+':
        p[0] = EIQOptAdd(p[1], p[3], Parser.Global)
    elif len(p) == 4 and p[2] == '-':
        p[0] = EIQOptSub(p[1], p[3], Parser.Global)
    elif len(p) == 4 and p[2] == '*':
        p[0] = EIQOptMul(p[1], p[3], Parser.Global)
    elif len(p) == 3 and p.slice[2].type == 'eiqopt':
        p[0] = EIQOptMul(p[1], p[2], Parser.Global)
    elif p.slice[2].type == 'DAGGER':
        p[0] = EIQOptDagger(p[1], Parser.Global)
    elif p.slice[2].type == 'OTIMES':
        p[0] = EIQOptTensor(p[1], p[3], Parser.Global)
    elif p.slice[2].type == 'DISJUNCT':
        p[0] = EIQOptDisjunct(p[1], p[3], Parser.Global)
    elif p.slice[2].type == 'CONJUNCT':
        p[0] = EIQOptConjunct(p[1], p[3], Parser.Global)
    elif p.slice[2].type == 'SASAKI_IMPLY':
        p[0] = EIQOptSasakiImply(p[1], p[3], Parser.Global)
    elif p.slice[2].type == 'SASAKI_CONJUNCT':
        p[0] = EIQOptSasakiConjunct(p[1], p[3], Parser.Global)
    else:
        raise Exception()


from .eqopt import *
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
            | eqopt DISJUNCT eqopt
            | eqopt CONJUNCT eqopt
            | eqopt SASAKI_IMPLY eqopt
            | eqopt SASAKI_CONJUNCT eqopt
    '''
    if len(p) == 2:
        p[0] = p[1]
    elif len(p) == 4 and p[1] == '(' and p[3] == ')':
        p[0] = p[2]
    elif len(p) == 5 and p[2] == '-':
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
    elif p.slice[2].type == 'DISJUNCT':
        p[0] = EQOptDisjunct(p[1], p[3], Parser.Global)
    elif p.slice[2].type == 'CONJUNCT':
        p[0] = EQOptConjunct(p[1], p[3], Parser.Global)
    elif p.slice[2].type == 'SASAKI_IMPLY':
        p[0] = EQOptSasakiImply(p[1], p[3], Parser.Global)
    elif p.slice[2].type == 'SASAKI_CONJUNCT':
        p[0] = EQOptSasakiConjunct(p[1], p[3], Parser.Global)
    # elif len(p) == 5 and p.slice[1].type == 'eqso':
    #     p[0] = EQSOptApply(p[1], p[3], Parser.Global)
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