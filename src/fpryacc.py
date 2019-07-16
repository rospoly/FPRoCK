import sys
import ply.yacc as yacc
from fprlex import *
import fprlex

uniqueLexer=FPRlex()
			
class FPRyacc:
	
	tokens = FPRlex.tokens
	reserved = FPRlex.reserved

	def __init__(self,program,solver,buildModelForVarsOnlyForBNB,buildModelForAllExceptVariables,debug):
		self.lexer = uniqueLexer
		self.solver=solver
		self.parser = yacc.yacc(module=self)
		self.debug = debug
		self.buildModelForVarsOnlyForBNB = buildModelForVarsOnlyForBNB
		self.buildModelForAllExceptVariables = buildModelForAllExceptVariables
		self.program=program
		self.parser.parse(self.program)
		
	def myPrint(self,s,p):
		res=""
		if self.debug:
			print str(s)+": "+str(p[0])
		return
	
	def p_FileInput(self, p):
		''' FileInput : VarDeclaration Constraints
					  | VarDeclaration
					  | Constraints
		'''
		if len(p)>5:
			p[0]=str(p[1])+str(p[2])+str(p[3])+str(p[4])+str(p[5])
		elif len(p)>3:
			p[0]=str(p[1])+str(p[2])+str(p[3])
		elif len(p)>1:
			p[0]=str(p[1])
		self.myPrint("FileInput",p)
		
	def p_VarDeclaration(self, p):
		''' VarDeclaration :  RealDecl NEWLINES FPDecl NEWLINES
							| FPDecl NEWLINES RealDecl NEWLINES
							| RealDecl NEWLINES FPDecl
							| FPDecl NEWLINES RealDecl
							| RealDecl NEWLINES
							| FPDecl NEWLINES
							| RealDecl 
							| FPDecl
		'''
		if   len(p)>4:
			p[0]=str(p[1])+str(p[2])+str(p[3])+str(p[4])
		elif len(p)>3:
			p[0]=str(p[1])+str(p[2])+str(p[3])
		elif len(p)>2:
			p[0]=str(p[1])+str(p[2])
		elif len(p)>1:
			p[0]=str(p[1])
		
		#if self.buildModelForAllExceptVariables:
		#	self.solver.encodeVariables()	
		
		self.myPrint("VarDeclaration",p)
		
	def p_RealDecl(self, p):
		''' RealDecl : REAL COLON RealDeclList
		'''
		p[0]=str(p[1])+str(p[2])+str(p[3])
		self.myPrint("RealDecl",p)
	
	def p_FPDecl(self, p):
		''' FPDecl : FLOAT COLON FPDeclList
		'''
		p[0]=str(p[1])+str(p[2])+str(p[3])
		self.myPrint("FPDecl",p)
		
	def p_RealDeclList(self, p):
		''' RealDeclList : RealDeclListNotEmpty 
		'''
		p[0]=str(p[1])
		self.myPrint("RealDeclList",p)
	
	def p_FPDeclList(self, p):
		''' FPDeclList : FPDeclListNotEmpty 
		'''
		p[0]=str(p[1])
		self.myPrint("FPDeclList",p)
		
	def p_FPDeclListNotEmpty(self, p):
		''' FPDeclListNotEmpty : FPVarDecl 
							   | FPVarDecl COMMA FPDeclListNotEmpty
		'''
		if len(p)>2:
			p[0]=str(p[1])+str(p[2])+str(p[3])
		elif len(p)==2:
			p[0]=str(p[1])
		self.myPrint("FPDeclListNotEmpty",p)
	
	def p_RealDeclListNotEmpty(self, p):
		''' RealDeclListNotEmpty : RealVarDecl 
								 | RealVarDecl COMMA RealDeclListNotEmpty
		'''
		if len(p)>2:
			p[0]=str(p[1])+str(p[2])+str(p[3])
		elif len(p)==2:
			p[0]=str(p[1])
		self.myPrint("RealDeclListNotEmpty",p)
		
	def p_RealVarDecl(self, p):
		''' RealVarDecl : WORD ASSIGN SLPAREN NUMBER SEMICOLON NUMBER SRPAREN
		'''
		p[0]=str(p[1])+str(p[2])+str(p[3])+str(p[4])+str(p[5])+str(p[6])+str(p[7])
		
		if not self.buildModelForAllExceptVariables:
			self.solver.addVariableReal(str(p[1]),str(p[4]),str(p[6]))
		
		self.myPrint("RealVarDecl",p)
	
	def p_FPVarDecl(self, p):
		''' FPVarDecl : WORD SLPAREN LPAREN NUMBER COMMA NUMBER RPAREN SRPAREN ASSIGN SLPAREN NUMBER SEMICOLON NUMBER SRPAREN
		''' 
		p[0]=str(p[1])+str(p[2])+str(p[3])+str(p[4])+str(p[5])+str(p[6])+str(p[7])+str(p[8])+str(p[9])+str(p[10])+str(p[11])+str(p[12])+str(p[13])+str(p[14])
		
		if not self.buildModelForAllExceptVariables:
			self.solver.addVariableFP(str(p[1]),str(p[11]),str(p[13]),str(p[4]),str(p[6]))
		
		self.myPrint("FPVarDecl",p)
	
	def p_Constraints(self, p):
		'''Constraints : ConstraintsList'''
		#if not self.buildModelForVarsOnlyForBNB:
		#	p[0]=self.solver.encodeConstraints(str(p[1]))
		p[0]=str(p[1])
		self.myPrint("Constraints",p)
	
	def p_ConstraintsListBool(self, p):
		'''ConstraintsList : ListBoolExpr
						   | ListBoolExpr NEWLINES ConstraintsList'''
		if not self.buildModelForVarsOnlyForBNB:			
			if len(p)>2:
				p[0]=str(p[1])+" "+str(p[3])
			else:
				p[0]=str(p[1])
		self.myPrint("ConstraintsListBool",p)
	
	def p_ConstraintsListAssign(self, p):
		'''ConstraintsList : AliasAssignment
						   | AliasAssignment NEWLINES ConstraintsList'''
		if not self.buildModelForVarsOnlyForBNB:
			if len(p)>2:
				p[0]=str(p[3])
			else:
				p[0]=""
		self.myPrint("ConstraintsListAssign",p)
	
	def p_AliasAssignment(self, p):
		'''AliasAssignment : WORD ASSIGN ArithExpr
		'''
		if not self.buildModelForVarsOnlyForBNB:
			self.solver.buildAliasAssignment(str(p[1]),str(p[3]))
			p[0]=""
		self.myPrint("AliasAssignment",p)
	
	def p_ListBoolExpr(self, p):
		'''ListBoolExpr : NotEmptyListBoolExpr
		'''
		if not self.buildModelForVarsOnlyForBNB:			
			if str(p[1])!="None":
				p[0]=self.solver.encodeConstraints(str(p[1]))
			else:
				p[0]=""
		self.myPrint("ListBoolExpr",p)
	
	def p_empty(self, p):
		'Empty :'
		pass
		
	def p_NotEmptyListBoolExpr(self, p):
		'''NotEmptyListBoolExpr : BoolExpr
								| BoolExpr COMMA NotEmptyListBoolExpr 
		'''
		if len(p)>2:
			p[0]=str(p[1])+" "+str(p[3])
		else:
			p[0]=str(p[1])
		self.myPrint("NotEmptyListBoolExpr",p)
	
	def p_BoolExprListNot(self, p):
		'''BoolExpr : NOT LPAREN BoolExpr RPAREN '''
		if not self.buildModelForVarsOnlyForBNB:
			p[0]=self.solver.buildNotLogicExpression(p[3])	
		self.myPrint("BoolExprListNot",p)
	
	def p_BoolExprListAndOr(self, p):
		'''BoolExpr : AND LPAREN NotEmptyListBoolExpr RPAREN
					| OR LPAREN NotEmptyListBoolExpr RPAREN
		'''
		if not self.buildModelForVarsOnlyForBNB:
			p[0]=self.solver.buildAndOrLogicExpression(str(p[1]),str(p[3]))
		self.myPrint("BoolExprListAndOr",p)
	
	def p_BoolExprMinimal(self, p):
		'''BoolExpr : ArithExpr EQUAL ArithExpr
					| ArithExpr NEQUAL ArithExpr
					| ArithExpr G ArithExpr
					| ArithExpr S ArithExpr
					| ArithExpr GE ArithExpr
					| ArithExpr SE ArithExpr
		'''
		if not self.buildModelForVarsOnlyForBNB:
			p[0]=self.solver.encodeBooleanExpression(str(p[1]),str(p[2]),str(p[3]))
		self.myPrint("BoolExpr",p)
		
	def p_ArithExpr(self, p):
		'''ArithExpr : AnnidateArithExpr
					 | BinaryArithExpr
		'''
		p[0]=str(p[1])
		self.myPrint("ArithExpr",p)
	
	def p_RealBinaryArithExpr(self, p):
		'''BinaryArithExpr : AnnidateArithExpr PLUS  AnnidateArithExpr
						   | AnnidateArithExpr MINUS AnnidateArithExpr
						   | AnnidateArithExpr MUL AnnidateArithExpr
						   | AnnidateArithExpr DIVIDE AnnidateArithExpr
						   | MINUS AnnidateArithExpr
		'''
		
		if not self.buildModelForVarsOnlyForBNB:
			if len(p)>3:
				varname=self.solver.encodeRealArithmeticExpression(str(p[1]),str(p[2]),str(p[3]))
			else:
				varname=self.solver.encodeRealArithmeticExpression("0.0",str(p[1]),str(p[2]))
			p[0]=varname
		
		self.myPrint("RealBinaryArithExpr",p)
	
	def p_FPBinaryArithExpr(self, p):
		'''BinaryArithExpr : AnnidateArithExpr PLUS_FP  AnnidateArithExpr
						   | AnnidateArithExpr MINUS_FP AnnidateArithExpr
						   | AnnidateArithExpr MUL_FP AnnidateArithExpr
						   | AnnidateArithExpr DIVIDE_FP AnnidateArithExpr
		'''
		if not self.buildModelForVarsOnlyForBNB:
			if len(p)>3:
				varname=self.solver.encodeFPArithmeticExpression(str(p[1]),str(p[2]),str(p[3]))
			else:
				varname=self.solver.encodeFPArithmeticExpression("0.0",str(p[1]),str(p[2]))
			p[0]=varname
		self.myPrint("FPBinaryArithExpr",p)
		
	def p_RealAnnidateArithExprParen(self, p):
		'''AnnidateArithExpr : LPAREN AnnidateArithExpr PLUS  AnnidateArithExpr RPAREN
							 | LPAREN AnnidateArithExpr MINUS AnnidateArithExpr RPAREN
							 | LPAREN AnnidateArithExpr MUL AnnidateArithExpr RPAREN
							 | LPAREN AnnidateArithExpr DIVIDE AnnidateArithExpr RPAREN
							 | LPAREN MINUS AnnidateArithExpr RPAREN
		'''
		if not self.buildModelForVarsOnlyForBNB:
			if len(p)>5:
				varname=self.solver.encodeRealArithmeticExpression(str(p[2]),str(p[3]),str(p[4]))
			else:
				varname=self.solver.encodeRealArithmeticExpression("0.0",str(p[2]),str(p[3]))
			p[0]=varname
		self.myPrint("RealAnnidateArithExprParen",p)
		
	def p_RealAnnidateArithExprRound(self, p):
		'''AnnidateArithExpr : TOFP LPAREN AnnidateArithExpr PLUS AnnidateArithExpr COMMA NUMBER COMMA NUMBER RPAREN
							 | TOFP LPAREN AnnidateArithExpr MINUS AnnidateArithExpr COMMA NUMBER COMMA NUMBER RPAREN
							 | TOFP LPAREN AnnidateArithExpr MUL AnnidateArithExpr COMMA NUMBER COMMA NUMBER RPAREN
							 | TOFP LPAREN AnnidateArithExpr DIVIDE AnnidateArithExpr COMMA NUMBER COMMA NUMBER RPAREN
							 | TOFP LPAREN MINUS AnnidateArithExpr COMMA NUMBER COMMA NUMBER RPAREN
		'''
		if not self.buildModelForVarsOnlyForBNB:
			if len(p)>9:
				varname=self.solver.encodeRealArithmeticExpression(str(p[3]),str(p[4]),str(p[5]))
				varname=self.solver.tofp(varname,str(p[7]),str(p[9]))
			else:
				varname=self.solver.encodeRealArithmeticExpression("0.0",str(p[3]),str(p[4]))
				varname=self.solver.tofp(varname,str(p[6]),str(p[8]))
			p[0]=varname
		
		self.myPrint("RealAnnidateArithExprRound",p)
		
	def p_RealAnnidateArithExprAbs(self, p):
		'''AnnidateArithExpr : ABS LPAREN AnnidateArithExpr PLUS  AnnidateArithExpr RPAREN
							 | ABS LPAREN AnnidateArithExpr MINUS AnnidateArithExpr RPAREN
							 | ABS LPAREN AnnidateArithExpr MUL AnnidateArithExpr RPAREN
							 | ABS LPAREN AnnidateArithExpr DIVIDE AnnidateArithExpr RPAREN
							 | ABS LPAREN MINUS AnnidateArithExpr RPAREN
		'''
		if not self.buildModelForVarsOnlyForBNB:	
			if len(p)>5:
				varname=self.solver.encodeRealArithmeticExpression(str(p[3]),str(p[4]),str(p[5]))
				varname=self.solver.absolute(varname)
			else:
				varname=self.solver.encodeRealArithmeticExpression("0.0",str(p[3]),str(p[4]))
				varname=self.solver.absolute(varname)		
			p[0]=varname
		
		self.myPrint("RealAnnidateArithExprAbs",p)
		
	def p_FPAnnidateArithExprParen(self, p):
		'''AnnidateArithExpr : LPAREN AnnidateArithExpr PLUS_FP AnnidateArithExpr RPAREN
							 | LPAREN AnnidateArithExpr MINUS_FP AnnidateArithExpr RPAREN
							 | LPAREN AnnidateArithExpr MUL_FP AnnidateArithExpr RPAREN
							 | LPAREN AnnidateArithExpr DIVIDE_FP AnnidateArithExpr RPAREN
							 | LPAREN MINUS_FP AnnidateArithExpr RPAREN
		'''
		if not self.buildModelForVarsOnlyForBNB:
			if len(p)>5:
				varname=self.solver.encodeFPArithmeticExpression(str(p[2]),str(p[3]),str(p[4]))
			else:
				varname=self.solver.encodeFPArithmeticExpression("0.0",str(p[2]),str(p[3]))
			p[0]=varname
		
		self.myPrint("FPAnnidateArithExprParen",p)
	
	def p_FPAnnidateArithExprAbs(self, p):
		'''AnnidateArithExpr : ABS LPAREN AnnidateArithExpr PLUS_FP AnnidateArithExpr RPAREN
							 | ABS LPAREN AnnidateArithExpr MINUS_FP AnnidateArithExpr RPAREN
							 | ABS LPAREN AnnidateArithExpr MUL_FP AnnidateArithExpr RPAREN
							 | ABS LPAREN AnnidateArithExpr DIVIDE_FP AnnidateArithExpr RPAREN
							 | ABS LPAREN MINUS_FP AnnidateArithExpr RPAREN
		'''
		
		if not self.buildModelForVarsOnlyForBNB:
			if len(p)>5:
				varname=self.solver.encodeFPArithmeticExpression(str(p[3]),str(p[4]),str(p[5]))
				varname=self.solver.absolute(varname)
			else:
				varname=self.solver.encodeFPArithmeticExpression("0.0",str(p[3]),str(p[4]))
				varname=self.solver.absolute(varname)		
			p[0]=varname
			
		self.myPrint("FPAnnidateArithExprAbs",p)
	
	def p_MinAnnidateArithExpr(self, p):
		'''AnnidateArithExpr : MIN LPAREN AnnidateArithExpr COMMA AnnidateArithExpr RPAREN
		'''
		
		if not self.buildModelForVarsOnlyForBNB:
			varname=self.solver.encodeMinProblem(str(p[3]),str(p[5]))
			p[0]=varname
		self.myPrint("MinAnnidateArithExpr",p)
		
	def p_MaxAnnidateArithExpr(self, p):
		'''AnnidateArithExpr : MAX LPAREN AnnidateArithExpr COMMA AnnidateArithExpr RPAREN
		'''
		
		if not self.buildModelForVarsOnlyForBNB:
			varname=self.solver.encodeMaxProblem(str(p[3]),str(p[5]))
			p[0]=varname
		self.myPrint("MaxAnnidateArithExpr",p)
	
	def p_UnaryExpr(self, p):
		'''AnnidateArithExpr : UnaryExpr
							 | LPAREN UnaryExpr RPAREN
		'''
		
		if len(p)>2:
			p[0]=str(p[2])	
		else:
			p[0]=str(p[1])
		self.myPrint("UnaryArithExpr",p)
	
	def p_UnaryExprABS(self, p):
		'''AnnidateArithExpr : ABS LPAREN AnnidateArithExpr RPAREN
		'''
		
		if not self.buildModelForVarsOnlyForBNB:
			p[0]=self.solver.absolute(str(p[3]))
		
		self.myPrint("UnaryExprABS",p)
		
	def p_UnaryExprTOFP(self, p):
		'''AnnidateArithExpr : TOFP LPAREN AnnidateArithExpr COMMA NUMBER COMMA NUMBER RPAREN
		'''
		
		if not self.buildModelForVarsOnlyForBNB:
			p[0]=self.solver.tofp(str(p[3]),str(p[5]),str(p[7]))

		self.myPrint("UnaryExprTOFP",p)
	
	def p_UnaryExprTOREAL(self, p):
		'''AnnidateArithExpr : TOREAL LPAREN AnnidateArithExpr RPAREN
		'''
		
		if not self.buildModelForVarsOnlyForBNB:
			p[0]=self.solver.toreal(str(p[3]))
		
		self.myPrint("UnaryExprTOREAL",p)
	
	def p_Number(self, p):
		'''UnaryExpr : NUMBER'''
		#Nothing to do here I think
		p[0]=str(p[1])
		self.myPrint("Number",p)
	
	def p_Variable(self, p):
		'''UnaryExpr : WORD '''
		if not self.buildModelForVarsOnlyForBNB:
			self.solver.checkVariable(str(p[1]))
			p[0]=str(p[1])
		self.myPrint("Variable",p)

	def p_error(self, p):
		if p:
			raise Exception("Syntax error at '%s', type %s, on line %d\n, program '%s'" % (p.value, p.type, p.lineno, self.program))
			exit(-1)
		else:
			raise Exception("Syntax error at EOF, program '%s'", self.program)
			exit(-1)
