
# ------------------------------------------------------------
# lexer.py
#
# tokenizer
# ------------------------------------------------------------

import ply.lex as lex


tokens = [
    'ID',
    'OTIMES',
    'DAGGER',
 ]
 
literals = ['(', ')', '[', ']', '+', '-', '*']

t_OTIMES = r"⊗|\\otimes"
t_DAGGER = r"†|\^\\dagger"

def t_ID(t):
    r'[a-zA-Z_][a-zA-Z_0-9]*'
    return t

# A string containing ignored characters (spaces and tabs)
t_ignore = ' \t'

def t_error(t):
    raise ValueError("Syntax Error. Illegal character '" + t.value[0] + "'.")


# Build the lexer
import re
lexer = lex.lex(reflags = re.UNICODE)