import sys
import ply.lex as lex

if sys.version_info[0] >= 3:
    raw_input = input

class FPRlex(object):
	def __init__(self):
		# Build the lexer
		self.lexer = lex.lex(module=self)
	
	reserved = {
		'or' : 'OR',
		'and' : 'AND',
		'not' : 'NOT',
		'abs' : 'ABS',
		'tofp' : 'TOFP',
		'toreal' : 'TOREAL',
		'Real' : 'REAL',
		'Float' : 'FLOAT',
		'+inf' : 'NUMBER',
		'inf' : 'NUMBER',
		'-inf' : 'NUMBER',
		'nan' : 'NUMBER',
		'min' : 'MIN',
		'max' : 'MAX'}
	
	tokens = list(dict.fromkeys([
		'NUMBER',
		'WORD',
		'PLUS',
		'PLUS_FP',
		'MINUS',
		'MINUS_FP',
		'MUL',
		'MUL_FP',
		'DIVIDE',
		'DIVIDE_FP',
		'EQUAL',
		'ASSIGN',
		'NEQUAL',
		'G',
		'S',
		'GE',
		'SE',
		'COMMA',
		'LPAREN',
		'RPAREN',
		'NEWLINES',
		'SLPAREN',
		'SRPAREN',
		'COLON',
		'SEMICOLON'] + list(reserved.values())))
		
	# Regular expression rules for simple tokens
	#t_NUMBER = r"([-+]?\d+\.\d+)|([-+]?\d+)|(\+inf)|(\-inf)"
	t_PLUS_FP = r'\+FP'
	t_MUL_FP = r'\*FP'
	t_MINUS_FP = r'-FP'
	t_DIVIDE_FP = r'/FP'
	t_PLUS    = r'\+'
	t_MINUS   = r'-'
	t_MUL   = r'\*'
	t_DIVIDE  = r'/'
	t_NEQUAL = r"\!="
	t_GE = r">="
	t_SE = r"<="
	t_G  = r'>'
	t_S  = r'<'
	t_EQUAL  = r'=='
	t_ASSIGN = r'='
	t_LPAREN  = r'\('
	t_RPAREN  = r'\)'
	t_COMMA = r','
	t_SLPAREN  = r'\['
	t_SRPAREN  = r'\]'
	t_COLON = r':'
	t_SEMICOLON = r';'
	
	def t_NUMBER(self,t):
		r'([-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?)|(\-inf)|(\+inf)|(nan)'
		t.value=str(t.value)
		return t
		
	def t_WORD(self,t):
		r'[a-zA-Z$_][a-zA-Z0-9$_]*'
		t.type = self.reserved.get(t.value,'WORD') 
		t.value = str(t.value)
		return t
	
	# Define a rule so we can track line numbers
	def t_NEWLINES(self,t):
		r'\n+'
		t.lexer.lineno += len(t.value)
		t.value = str(t.value)
		return t
	
	def t_COMMENT(self,t):
		r'\%.*'
		pass
		# No return value. Token discarded
		 
	# Error handling rule
	def t_error(self,t):
		print "Found Illegal character "+t.value[0]
		exit(0)
		 
	# A string containing ignored characters (spaces and tabs)
	t_ignore  = ' \t\r'
	
