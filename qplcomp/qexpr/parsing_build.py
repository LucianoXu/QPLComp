

#############################################################
# the lexer

import ply.lex as lex

from .lexer_def import *

# Build the lexer
import re
lexer = lex.lex(reflags = re.UNICODE)



#############################################################
# the parser

import ply.yacc as yacc

from .parser_def import *

# Build the parser
parser = yacc.yacc()





#############################################################
# the encapsulation 

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
        ParsingEnv.env = env

    @staticmethod
    def parse(code : str) -> Expr:
        res = parser.parse(code)
        if not isinstance(res, Expr):
            raise Exception("Unexpected Exception.")
        
        return res


# assign the environment for parser
from . import parser_def
parser_def.ParsingEnv.env = Parser.Global