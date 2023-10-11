
# ------------------------------------------------------------
# lexer.py
#
# tokenizer
# ------------------------------------------------------------

import ply.lex as lex

reserved = {
}

tokens = [
    'ID',
    'OTIMES',
    'DAGGER',
    'DISJUNCT',
    'CONJUNCT',
    'SASAKI_IMPLY',
    'SASAKI_CONJUNCT',
 ] + list(reserved.values())
 
literals = ['(', ')', '[', ']', '+', '-', '*']

t_OTIMES = r"⊗|\\otimes"
t_DAGGER = r"†|\^\\dagger"
t_DISJUNCT = r"∨|\\vee"
t_CONJUNCT = r"∧|\\wedge"
t_SASAKI_IMPLY = r"⇝|\\SasakiImply"
t_SASAKI_CONJUNCT = r"⋒|\\SasakiConjunct"

def t_ID(t):
    r'[a-zA-Z\'][a-zA-Z\'0-9]*'
    t.type = reserved.get(t.value, 'ID')
    return t

# A string containing ignored characters (spaces and tabs)
t_ignore = ' \t'

def t_error(t):
    raise ValueError("Syntax Error. Illegal character '" + t.value[0] + "'.")


# Build the lexer
import re
lexer = lex.lex(reflags = re.UNICODE)