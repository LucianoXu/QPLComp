# ------------------------------------------------------------
# parser.py
#
# parser
# ------------------------------------------------------------
from __future__ import annotations
from typing import Tuple

from ..sugar import type_check

from ..env import Env

def type_match(p, types: Tuple[str, ...]) -> bool:
    '''
    The method to check whether the sentence match the corresponding types.
    '''
    if len(p) != len(types) + 1:
        return False
    
    for i in range(len(types)):
        if p.slice[i + 1].type != types[i]:
            return False
    return True

class ParsingEnv:
    env : Env = Env()


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
    p[0] = Variable(p[1], ParsingEnv.env)


from .eiqopt import *
def p_eiqopt(p):
    '''
    eiqopt  : IQOPT variable
            | eqopt eqvar
            | '(' eiqopt ')'
            | '(' '-' eiqopt ')'
            | eiqopt '+' eiqopt
            | eiqopt '-' eiqopt
            | num '*' eiqopt
            | num eiqopt %prec '*'
            | eiqopt '*' eiqopt
            | eiqopt eiqopt %prec '*'
            | eiqopt DAGGER
            | eiqopt OTIMES eiqopt
            | eiqopt DISJUNCT eiqopt
            | eiqopt CONJUNCT eiqopt
            | eiqopt COMPLEMENT
            | eiqopt SASAKI_IMPLY eiqopt
            | eiqopt SASAKI_CONJUNCT eiqopt
    '''
    if type_match(p, ('IQOPT', 'variable')):
        p[0] = p[2]
    elif type_match(p, ('eqopt', 'eqvar')):
        p[0] = EIQOpt(p[1], p[2], ParsingEnv.env)
    elif type_match(p, ('(', 'eiqopt', ')')):
        p[0] = p[2]
    elif type_match(p, ('(', '-', 'eiqopt', ')')):
        p[0] = EIQOptNeg(p[3], ParsingEnv.env)
    elif type_match(p, ('eiqopt', '+', 'eiqopt')):
        p[0] = EIQOptAdd(p[1], p[3], ParsingEnv.env)
    elif type_match(p, ('eiqopt', '-', 'eiqopt')):
        p[0] = EIQOptSub(p[1], p[3], ParsingEnv.env)
    elif type_match(p, ('num', '*', 'eiqopt')):
        p[0] = EIQOptScale(p[1], p[3], ParsingEnv.env)
    elif type_match(p, ('num', 'eiqopt')):
        p[0] = EIQOptScale(p[1], p[2], ParsingEnv.env)
    elif type_match(p, ('eiqopt', '*', 'eiqopt')):
        p[0] = EIQOptMul(p[1], p[3], ParsingEnv.env)
    elif type_match(p, ('eiqopt', 'eiqopt')):
        p[0] = EIQOptMul(p[1], p[2], ParsingEnv.env)
    elif type_match(p, ('eiqopt', 'DAGGER')):
        p[0] = EIQOptDagger(p[1], ParsingEnv.env)
    elif type_match(p, ('eiqopt', 'OTIMES', 'eiqopt')):
        p[0] = EIQOptTensor(p[1], p[3], ParsingEnv.env)
    elif type_match(p, ('eiqopt', 'DISJUNCT', 'eiqopt')):
        p[0] = EIQOptDisjunct(p[1], p[3], ParsingEnv.env)
    elif type_match(p, ('eiqopt', 'CONJUNCT', 'eiqopt')):
        p[0] = EIQOptConjunct(p[1], p[3], ParsingEnv.env)
    elif type_match(p, ('eiqopt', 'COMPLEMENT')):
        p[0] = EIQOptComplement(p[1], ParsingEnv.env)
    elif type_match(p, ('eiqopt', 'SASAKI_IMPLY', 'eiqopt')):
        p[0] = EIQOptSasakiImply(p[1], p[3], ParsingEnv.env)
    elif type_match(p, ('eiqopt', 'SASAKI_CONJUNCT', 'eiqopt')):
        p[0] = EIQOptSasakiConjunct(p[1], p[3], ParsingEnv.env)
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
            | num '*' eqopt
            | num eqopt  %prec '*'
            | eqopt '*' eqopt
            | eqopt eqopt %prec '*'
            | eqopt DAGGER
            | eqopt OTIMES eqopt
            | eqopt DISJUNCT eqopt
            | eqopt CONJUNCT eqopt
            | eqopt COMPLEMENT
            | eqopt SASAKI_IMPLY eqopt
            | eqopt SASAKI_CONJUNCT eqopt
    '''
    if type_match(p, ('variable',)):
        p[0] = p[1]
    elif type_match(p, ('(', 'eqopt', ')')):
        p[0] = p[2]
    elif type_match(p, ('(', '-', 'eqopt', ')')):
        p[0] = EQOptNeg(p[3], ParsingEnv.env)
    elif type_match(p, ('eqopt', '+', 'eqopt')):
        p[0] = EQOptAdd(p[1], p[3], ParsingEnv.env)
    elif type_match(p, ('eqopt', '-', 'eqopt')):
        p[0] = EQOptSub(p[1], p[3], ParsingEnv.env)
    elif type_match(p, ('num', '*', 'eqopt')):
        p[0] = EQOptScale(p[1], p[3], ParsingEnv.env)
    elif type_match(p, ('num', 'eqopt')):
        p[0] = EQOptScale(p[1], p[2], ParsingEnv.env)
    elif type_match(p, ('eqopt', '*', 'eqopt')):
        p[0] = EQOptMul(p[1], p[3], ParsingEnv.env)
    elif type_match(p, ('eqopt', 'eqopt')):
        p[0] = EQOptMul(p[1], p[2], ParsingEnv.env)
    elif type_match(p, ('eqopt', 'DAGGER')):
        p[0] = EQOptDagger(p[1], ParsingEnv.env)
    elif type_match(p, ('eqopt', 'OTIMES', 'eqopt')):
        p[0] = EQOptTensor(p[1], p[3], ParsingEnv.env)
    elif type_match(p, ('eqopt', 'DISJUNCT', 'eqopt')):
        p[0] = EQOptDisjunct(p[1], p[3], ParsingEnv.env)
    elif type_match(p, ('eqopt', 'CONJUNCT', 'eqopt')):
        p[0] = EQOptConjunct(p[1], p[3], ParsingEnv.env)
    elif type_match(p, ('eqopt', 'COMPLEMENT')):
        p[0] = EQOptComplement(p[1], ParsingEnv.env)
    elif type_match(p, ('eqopt', 'SASAKI_IMPLY', 'eqopt')):
        p[0] = EQOptSasakiImply(p[1], p[3], ParsingEnv.env)
    elif type_match(p, ('eqopt', 'SASAKI_CONJUNCT', 'eqopt')):
        p[0] = EQOptSasakiConjunct(p[1], p[3], ParsingEnv.env)
    # elif len(p) == 5 and p.slice[1].type == 'eqso':
    #     p[0] = EQSOptApply(p[1], p[3], ParsingEnv.env)
    else:
        raise Exception()

from .eqvar import EQVar
def p_eqvar(p):
    '''
    eqvar   : qvar
    '''
    p[0] = EQVar(p[1], ParsingEnv.env)

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

def p_num(p):
    '''
    num : FLOATNUM
        | COMPLEXNUM
    '''
    if p.slice[1].type == 'FLOATNUM':
        p[0] = float(p[1])
    elif p.slice[1].type == 'COMPLEXNUM':
        p[0] = complex(p[1])
    else:
        raise Exception()

def p_error(p):
    if p is None:
        raise RuntimeError("unexpected end of file")
    raise RuntimeError("Syntax error in input: '" + str(p.value) + "'.")



