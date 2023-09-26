# ------------------------------------------------------------
# parser.py
#
# parser
# ------------------------------------------------------------

import ply.yacc as yacc

from .lexer import tokens, lexer

def p_qexpr(p):
    '''
    qexpr : ID qvar
    '''
    p[0] = (p[1], p[2])


def p_qvar(p):
    '''
    qvar : qvar_pre ']'
    '''
    p[0] = p[1]


def p_qvar_pre(p):
    '''
    qvar_pre : '[' ID
                | qvar_pre ID
    '''
    if p[1] == '[':
        p[0] = [p[2]]
    else:
        p[0] = p[1] + [p[2]]

def p_error(p):
    if p is None:
        raise RuntimeError("unexpected end of file")
    raise RuntimeError("Syntax error in input: '" + str(p.value) + "'.")



# Build the parser
parser = yacc.yacc()