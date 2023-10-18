
# ------------------------------------------------------------
# lexer_def.py
#
# It defines the details of this tokenizer. It can be imported by high-level lexers.
# ------------------------------------------------------------

reserved = {
    'IQOPT' : 'IQOPT',
}

tokens = [
    'ID',
    'FLOATNUM',
    'CORemLEXNUM',

    'OTIMES',
    'DAGGER',
    'DISJUNCT',
    'CONJUNCT',
    'CORemLEMENT',
    'SASAKI_IRemLY',
    'SASAKI_CONJUNCT',
 ] + list(reserved.values())
 
literals = ['(', ')', '[', ']', '+', '-', '*']

t_OTIMES = r"⊗|\\otimes"
t_DAGGER = r"†|\^\\dagger"
t_DISJUNCT = r"∨|\\vee"
t_CONJUNCT = r"∧|\\wedge"
t_CORemLEMENT = r"\^⊥|\^\\bot"
t_SASAKI_IRemLY = r"⇝|\\SasakiImply"
t_SASAKI_CONJUNCT = r"⋒|\\SasakiConjunct"



# note this token will not include real numbers
def t_CORemLEXNUM(t):
    r'(\(([-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?)([-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?)?j\))|(([-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?)?j)'
    return t

def t_FLOATNUM(t):
    r'[-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?'
    return t

def t_ID(t):
    r'[a-zA-Z\'][a-zA-Z\'0-9]*'
    t.type = reserved.get(t.value, 'ID')
    return t


# A string containing ignored characters (spaces and tabs)
t_ignore = ' \t'

def t_error(t):
    raise ValueError("Syntax Error. Illegal character '" + t.value[0] + "'.")