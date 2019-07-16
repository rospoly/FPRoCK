from gmpy2 import *
import gmpy2
from printing import *
from mpmath import *
from mpmath import iv
import collections
import os

def isNumericInteger(expression):
	try:
		if str(float(expression))=="nan" or  "inf" in str(float(expression)):
			return False
		int(expression)
		return True
	except:
		return False
	return False
	
def isNumericSpecialValue(expression):
	try:
		if str(float(expression))=="nan" or  "inf" in str(float(expression)):
			return True
	except:
		return False
	return False

def isNumericReal(expression):
	try:
		if str(float(expression))=="nan" or  "inf" in str(float(expression)):
			return False
		float(expression)
		return True
	except:
		return False
	return False

def isNumericFP(expression):
	try:
		float(expression)
		return True
	except:
		return False
	return False

def checkBoundsConsistent(lb,ub):
	if ((lb=="nan" and ub!="nan") or
		(lb!="nan" and ub=="nan")):
		print "Cannot define an numeric interval with nan. Use [nan,nan]."
		exit(0)
	if float(lb)>float(ub):
		print "Lower bound looks greater than upper bound."
		exit(0)
	return
		
def computeSmallestPositiveNumberSubNormal(mantissa,exponent):
	with gmpy2.local_context(gmpy2.context(), precision=max(5*mantissa,100)) as ctx:
		smallestPositiveDenormal= gmpy2.exp2(-mantissa)*(gmpy2.exp2(-(gmpy2.exp2(exponent-1)-1-1)))
		return smallestPositiveDenormal

def computeSmallestPositiveNumberNormal(mantissa,exponent):
	with gmpy2.local_context(gmpy2.context(), precision=max(5*mantissa,100)) as ctx:
		#smallestPositiveNumber= mpfr(2**(-mantissa)*(2**(-(2**(exponent-1)-1-1)))) denormal
		smallestPositiveNumber= gmpy2.exp2(-(gmpy2.exp2(exponent-1)-1-1))
		#for negative it is just a matter of signs
		return smallestPositiveNumber

def computeBiggestPositiveNumber(mantissa,exponent):
	with gmpy2.local_context(gmpy2.context(), precision=max(5*mantissa,100)) as ctx:
		#biggestPositiveNumber = mpfr((2-(2**-mantissaPrecision))*2**(2**(exponentPrecision-1)-1))
		biggestPositiveNumber = gmpy2.mul(gmpy2.sub(2,gmpy2.exp2(-mantissa)),gmpy2.exp2(gmpy2.exp2(exponent-1)-1))
		#for negative it is just a matter of signs
		return biggestPositiveNumber
		
def getAbsLowerBound(bound):
	vals=bound.split(",")
	absVals=[Decimal(number) for number in vals]
	minVal=min(absVals)
	return max(minVal,Decimal(0.0))
	
def getAbsUpperBound(bound):
	vals=bound.split(",")
	absVals=[Decimal(number) for number in vals]
	absVals=map(abs, absVals)
	return max(absVals)

def adjustLbUbForSpecificFormat(lb,ub,mantissa,minDenormal,minNormal,maxNumber):
	negmaxNumber=-maxNumber
	
	with gmpy2.local_context(gmpy2.context(), precision=mantissa, round=RoundDown) as ctx:
		adjustLB=mpfr(lb)
		if gmpy2.is_nan(adjustLB):
			pass
		if gmpy2.is_infinite(adjustLB):
			pass
		elif adjustLB>mpfr("0.0") and adjustLB<=minDenormal:
			adjustLB=mpfr("0.0")
		elif adjustLB>=minDenormal and adjustLB<=minNormal:
			adjustLB=minDenormal
		elif -minDenormal<=adjustLB and adjustLB<mpfr("0.0"): 
			adjustLB=-minDenormal
		elif -minNormal<=adjustLB and adjustLB<=-minDenormal:
			adjustLB=-minNormal
		elif adjustLB>=maxNumber:
			adjustLB=mpfr("+inf")
		elif adjustLB<=negmaxNumber:
			adjustLB=mpfr("-inf")

	with gmpy2.local_context(gmpy2.context(), precision=mantissa, round=RoundUp) as ctx:
		adjustUB=mpfr(ub)
		if gmpy2.is_nan(adjustUB):
			pass
		if gmpy2.is_infinite(adjustUB):
			pass
		if adjustUB>mpfr("0.0") and adjustUB<=minDenormal:
			adjustUB=minDenormal
		elif adjustUB>=minDenormal and adjustUB<=minNormal:
			adjustUB=minNormal
		elif -minDenormal<=adjustUB and adjustUB<mpfr("0.0"): 
			adjustUB=mpfr("0.0")
		elif -minNormal<=adjustUB and adjustUB<=-minDenormal:
			adjustUB=-minDenormal
		elif adjustUB>=maxNumber:
			adjustUB=mpfr("+inf")
		elif adjustUB<=negmaxNumber:
			adjustUB=mpfr("-inf")

	return adjustLB,adjustUB	

def exponentRangeLbUb(mantissa,quantizedlb,quantizedub,minNormal,maxNormal):
	#print "lbub",quantizedlb,quantizedub
	
	with gmpy2.local_context(gmpy2.context(), precision=max(5*mantissa,100)) as ctx:
	
		if gmpy2.is_nan(quantizedlb):
			expLb = mpfr(minNormal)
		elif mpfr("0.0")>=quantizedlb and mpfr("0.0")<=quantizedub:
			expLb = mpfr(minNormal)
		elif -minNormal<=quantizedlb and minNormal>=quantizedlb:
			expLb = mpfr(minNormal)
		elif quantizedlb<=-maxNormal or quantizedlb>=maxNormal:
			expLb = maxNormal
		else:
			expLb = min(abs(quantizedlb),abs(quantizedub))
		
		if gmpy2.is_nan(quantizedub):
			expUb = mpfr(minNormal)
		elif -minNormal<=quantizedub and minNormal>=quantizedub and -minNormal<=quantizedlb and minNormal>=quantizedlb:
			expUb = mpfr(minNormal)
		elif quantizedub<=-maxNormal or quantizedub>=maxNormal:
			expUb = maxNormal
		else:
			expUb = max(abs(quantizedlb),abs(quantizedub))
		
		#print "exp",expLb,expUb
		return expLb,expUb
	
class FPVariable:
	def __init__(self,name,lb,ub,mantissa,exponent,realCounterpart,inheritFlagValue=""):
		
		self.name=name
		self.realCounterpart=realCounterpart
		self.realLb=self.realCounterpart.lb
		self.realUb=self.realCounterpart.ub
		self.mantissa=int(mantissa)
		self.exponent=int(exponent)
		self.inheritFlagValue= inheritFlagValue
		
		self.spdNum=computeSmallestPositiveNumberSubNormal(self.mantissa,self.exponent)
		self.spnNum=computeSmallestPositiveNumberNormal(self.mantissa,self.exponent)
		self.gpnNum=computeBiggestPositiveNumber (self.mantissa,self.exponent)
		
		self.qLb,self.qUb=adjustLbUbForSpecificFormat(lb,ub,self.mantissa,self.spdNum,self.spnNum,self.gpnNum)
		self.expLb,self.expUb=exponentRangeLbUb(self.mantissa,self.qLb,self.qUb,self.spnNum,self.gpnNum)
		
		self.quantizedlb=printFullNumberMPFR(self.qLb)
		self.quantizedub=printFullNumberMPFR(self.qUb)

		self.exponentLb=printFullNumberMPFR(self.expLb)
		self.exponentUb=printFullNumberMPFR(self.expUb)

		self.spdString=printFullNumberMPFR(self.spdNum)
		self.spnString=printFullNumberMPFR(self.spnNum)
		self.gpnString=printFullNumberMPFR(self.gpnNum)
				
		self.priority=self.getPriority()
		self.middlePoint=self.giveMiddlePoint()

		#print "Name: "+self.name
		#print "Min Denormal: "+self.spdString
		#print "Min Normal: "+self.spnString
		#print "Max: "+self.gpnString
		#print "QuantizedLb:"+ self.quantizedlb
		#print "QuantizedUb:"+ self.quantizedub
		#print "Lb:"+ self.realLb
		#print "Ub:"+ self.realUb
		#print "ExpLb:"+ self.exponentLb
		#print "ExpUb:"+ self.exponentUb
	
	def __repr__(self):
		return self.name+"=["+self.realLb+", "+self.realUb+"]"
	
	def __str__(self):
		return self.name+"=["+self.realLb+", "+self.realUb+"]"
	
	def encodeInit(self):
		coverVarEncoding=self.realCounterpart.encode()
		coverVarName=self.realCounterpart.name
		
		fpvar= coverVarEncoding
		
		fpvar= fpvar+ "(declare-const flag-"+ self.name +" Real)\n"
		fpvar= fpvar+ "(declare-const abs-"+ coverVarName +" Real)\n"
		fpvar= fpvar+ "(declare-const two-to-exp-p-minus-e-" +coverVarName + " Real)\n"

		fpvar= fpvar+ "(assert (= abs-" + coverVarName + " (absvalue " + coverVarName + ")))\n"
		fpvar= fpvar+ "(declare-const " + self.name + " Real)\n\n"
		
		if self.inheritFlagValue=="":
			fpvar= fpvar+ "(assert (= flag-" + self.name + " (initFlag " +self.name+ " "+ coverVarName + " "+self.gpnString+")))\n\n"
		else:
			fpvar= fpvar+ "(assert (= flag-" + self.name + " (initFlagInherit " +self.name+ " "+ coverVarName + " "+self.gpnString+" "+self.inheritFlagValue+")))\n\n"
		
		fpvar= fpvar+ "(assert (= (* " + self.name + " two-to-exp-p-minus-e-" + coverVarName +") (quantize " +coverVarName+" two-to-exp-p-minus-e-" + coverVarName +")))\n\n"
		return fpvar
	
	def encodeExponentRangeLinear(self):
		val=""
		var="abs-"+self.realCounterpart.name
		varexp="two-to-exp-p-minus-e-"+self.realCounterpart.name
		with gmpy2.local_context(gmpy2.context(), precision=max(5*self.mantissa,100)) as ctx:	
			iteratorExp=gmpy2.floor(gmpy2.log2(self.expLb))
			iterator=gmpy2.exp2(iteratorExp)

			nextIterator=gmpy2.exp2(iteratorExp+1)
			twoPminusE=gmpy2.exp2(self.mantissa-iteratorExp)

			val=val+"(assert (=> (and (>= "+var+" 0.0) (< "+var+" "+self.exponentLb+")) (= "+varexp+" "+printFullNumberMPFR(twoPminusE)+"))) \n"

			if nextIterator<=self.expUb:
				val=val+"(assert (=> (and (>= "+var+" "+self.exponentLb+") (< "+var+" "+printFullNumberMPFR(nextIterator)+")) (= "+varexp+" "+printFullNumberMPFR(twoPminusE)+"))) \n"
			else:
				val=val+"(assert (=> (and (>= "+var+" "+self.exponentLb+") (<= "+var+" "+self.exponentUb+")) (= "+varexp+" "+printFullNumberMPFR(twoPminusE)+"))) \n"
			
			iteratorExp=iteratorExp+1
			iterator=gmpy2.exp2(iteratorExp)
			nextIterator=gmpy2.exp2(iteratorExp+1)
			twoPminusE=gmpy2.exp2(self.mantissa-iteratorExp)
			
			#if not iterator<=self.expUb:
			#	val=val+"(assert (=> (and (>= "+var+" "+printFullNumberMPFR(iterator)+") (<= "+var+" "+self.quantizedub+")) (= "+varexp+" "+printFullNumberMPFR(twoPminusE)+"))) \n"
			#	val=val+"\t"+printFullNumberMPFR(twoPminusE)+" "
			
			while iterator<=self.expUb:
				if nextIterator<=self.expUb:
					val=val+"(assert (=> (and (>= "+var+" "+printFullNumberMPFR(iterator)+") (< "+var+" "+printFullNumberMPFR(nextIterator)+")) (= "+varexp+" "+printFullNumberMPFR(twoPminusE)+"))) \n"
					#par=par+")"	
				else:
					val=val+"(assert (=> (and (>= "+var+" "+printFullNumberMPFR(iterator)+") (<= "+var+" "+self.quantizedub+")) (= "+varexp+" "+printFullNumberMPFR(twoPminusE)+"))) \n"
					#par=par+")"
					#val=val+"\t"+printFullNumberMPFR(twoPminusE)+" "
				iteratorExp=iteratorExp+1
				iterator=gmpy2.exp2(iteratorExp)
				nextIterator=gmpy2.exp2(iteratorExp+1)
				twoPminusE=gmpy2.exp2(self.mantissa-iteratorExp)
				
			#val=val+par+"\n\n"
		return val

	def encode(self):
		return self.encodeInit()+self.encodeExponentRangeLinear()+"\n\n"
	
	def giveMiddlePoint(self):
		if self.realLb=="nan" and self.realUb=="nan":
			return "nan"
		elif ("inf" in self.realLb) or ("inf" in self.realUb):
			return "nan"
		elif self.realLb==self.realUb:
			return self.realLb
		else:	
			with gmpy2.local_context(gmpy2.context(), precision=500, round=RoundToNearest) as ctx:
				if gmpy2.sign(mpfr(self.realLb))<0 and gmpy2.sign(mpfr(self.realUb))>0:
					return "0.0"
					
				if gmpy2.is_zero(mpfr(self.realLb)):
					tmpLB=computeSmallestPositiveNumberSubNormal(52,11)
				else:
					tmpLB=mpfr(self.realLb)
				
				if gmpy2.is_zero(mpfr(self.realUb)):
					tmpUB=computeSmallestPositiveNumberSubNormal(52,11)
				else:
					tmpUB=mpfr(self.realUb)
					
			with gmpy2.local_context(gmpy2.context(), precision=500, round=RoundDown) as ctx:	
				adjustLB=min(abs(tmpLB),abs(tmpUB))
					
			with gmpy2.local_context(gmpy2.context(), precision=500, round=RoundUp) as ctx:
				adjustUB=max(abs(tmpLB),abs(tmpUB))
			
			with gmpy2.local_context(gmpy2.context(), precision=500, round=RoundToNearest) as ctx:
				iteratorExp=gmpy2.floor(gmpy2.log2(adjustLB))
				minExp=iteratorExp
				iterator=gmpy2.exp2(iteratorExp)
				while iterator<adjustUB:
					iteratorExp=iteratorExp+1
					iterator=gmpy2.exp2(iteratorExp)
				middlePowerExp=int((minExp+iteratorExp)/2.0)
				
				if gmpy2.sign(mpfr(self.realLb))>=0 and gmpy2.sign(mpfr(self.realUb))>=0:
					value=gmpy2.exp2(middlePowerExp)
				else:
					value=-gmpy2.exp2(middlePowerExp)
				
				if value<=mpfr(self.realLb) or value>=mpfr(self.realUb):
					return "nan"
				else:
					return printFullNumberMPFR(value)
	
	def getPriority(self):
		if self.realLb=="nan" and self.realUb=="nan":
			return 0
		elif ("inf" in self.realLb) or ("inf" in self.realUb):
			return 0
		elif self.realLb==self.realUb:
			return 0	
		else:
			with gmpy2.local_context(gmpy2.context(), precision=500, round=RoundToNearest) as ctx:
				if gmpy2.is_zero(mpfr(self.realLb)):
					tmpLB=computeSmallestPositiveNumberSubNormal(53,11)
				else:
					tmpLB=mpfr(self.realLb)
					
				if gmpy2.is_zero(mpfr(self.realUb)):
					tmpUB=computeSmallestPositiveNumberSubNormal(53,11)
				else:
					tmpUB=mpfr(self.realUb)
								
			with gmpy2.local_context(gmpy2.context(), precision=500, round=RoundDown) as ctx:
				if gmpy2.sign(mpfr(self.realLb))<0 and gmpy2.sign(mpfr(self.realUb))>0:
					adjustLB=computeSmallestPositiveNumberSubNormal(52,11)
				else:
					adjustLB=min(abs(tmpLB),abs(tmpUB))
					
			with gmpy2.local_context(gmpy2.context(), precision=500, round=RoundUp) as ctx:
				adjustUB=max(abs(tmpLB),abs(tmpUB))
			
			with gmpy2.local_context(gmpy2.context(), precision=500, round=RoundToNearest) as ctx:
				counter=0
				iteratorExp=gmpy2.floor(gmpy2.log2(adjustLB))
				iterator=gmpy2.exp2(iteratorExp)
				while iterator<adjustUB:
					counter=counter+1
					iteratorExp=iteratorExp+1
					iterator=gmpy2.exp2(iteratorExp)
				return counter

class RealVariable:
	def __init__(self,name,lb,ub):
		self.name=name
		self.lb=printFullNumberString(lb)
		self.ub=printFullNumberString(ub)
		self.encodingStorage=""
		checkBoundsConsistent(lb,ub)
		self.priority=self.getPriority()
		self.middlePoint=self.giveMiddlePoint()
	
	def __repr__(self):
		return self.name+"=["+self.lb+", "+self.ub+"]"
		
	def __str__(self):
		return self.name+"=["+self.lb+", "+self.ub+"]"
		
	def encode(self):
		realVar="(declare-const "+self.name+" Real)\n"
		if self.ub!="+inf" and self.ub!="nan":
			if self.ub.startswith("-"):
				realVar=realVar+"(assert (<= "+self.name+" "+self.encodeNegativeBoundValue(self.ub)+"))\n"
			else:	
				realVar=realVar+"(assert (<= "+self.name+" "+self.ub+"))\n"
		if self.lb!="-inf" and self.ub!="nan":
			if self.lb.startswith("-"):
				realVar=realVar+"(assert (>= "+self.name+" "+self.encodeNegativeBoundValue(self.lb)+"))\n"
			else:
				realVar=realVar+"(assert (>= "+self.name+" "+self.lb+"))\n"
		return realVar+self.encodingStorage+"\n\n"
		
	def encodeNegativeBoundValue(self,value):
		tmpValue=value.replace("-","")
		return "(- 0 "+ tmpValue + ")"

	def giveMiddlePoint(self):
		if self.lb=="nan" and self.ub=="nan":
			return "nan"
		elif ("inf" in self.lb) or ("inf" in self.ub):
			return "nan"
		elif self.lb==self.ub:
			return self.lb
		else:	
			with gmpy2.local_context(gmpy2.context(), precision=500, round=RoundToNearest) as ctx:
				if gmpy2.sign(mpfr(self.lb))<0 and gmpy2.sign(mpfr(self.ub))>0:
					return "0.0"
				if gmpy2.is_zero(mpfr(self.lb)):
					tmpLB=computeSmallestPositiveNumberSubNormal(52,11)
				else:
					tmpLB=mpfr(self.lb)					
				if gmpy2.is_zero(mpfr(self.ub)):
					tmpUB=computeSmallestPositiveNumberSubNormal(52,11)
				else:
					tmpUB=mpfr(self.ub)
			
			with gmpy2.local_context(gmpy2.context(), precision=500, round=RoundDown) as ctx:
				adjustLB=min(abs(tmpLB),abs(tmpUB))
					
			with gmpy2.local_context(gmpy2.context(), precision=500, round=RoundUp) as ctx:
				adjustUB=max(abs(tmpLB),abs(tmpUB))
			
			with gmpy2.local_context(gmpy2.context(), precision=500, round=RoundToNearest) as ctx:
				iteratorExp=gmpy2.floor(gmpy2.log2(adjustLB))
				minExp=iteratorExp
				iterator=gmpy2.exp2(iteratorExp)
				while iterator<adjustUB:
					iteratorExp=iteratorExp+1
					iterator=gmpy2.exp2(iteratorExp)
					
				middlePowerExp=int((minExp+iteratorExp)/2.0)
				
				if gmpy2.sign(mpfr(self.lb))>=0 and gmpy2.sign(mpfr(self.ub))>=0:
					value=gmpy2.exp2(middlePowerExp)
				else:
					value=-gmpy2.exp2(middlePowerExp)
				if value<=mpfr(self.lb) or value>=mpfr(self.ub):
					return "nan"
				else:
					return printFullNumberMPFR(value)
	
	def getPriority(self):
		if self.lb=="nan" and self.ub=="nan":
			return 0
		elif ("inf" in self.lb) or ("inf" in self.ub):
			return 0
		elif self.lb==self.ub:
			return 0	
		else:
			with gmpy2.local_context(gmpy2.context(), precision=500, round=RoundToNearest) as ctx:
				if gmpy2.is_zero(mpfr(self.lb)):
					tmpLB=computeSmallestPositiveNumberSubNormal(52,11)
				else:
					tmpLB=mpfr(self.lb)
				if gmpy2.is_zero(mpfr(self.ub)):
					tmpUB=computeSmallestPositiveNumberSubNormal(52,11)
				else:
					tmpUB=mpfr(self.ub)
			
			with gmpy2.local_context(gmpy2.context(), precision=500, round=RoundDown) as ctx:
				if gmpy2.sign(mpfr(self.lb))<0 and gmpy2.sign(mpfr(self.ub))>0:
					adjustLB=computeSmallestPositiveNumberSubNormal(52,11)
				else:
					adjustLB=min(abs(tmpLB),abs(tmpUB))
					
			with gmpy2.local_context(gmpy2.context(), precision=500, round=RoundUp) as ctx:
				adjustUB=max(abs(tmpLB),abs(tmpUB))
			
			with gmpy2.local_context(gmpy2.context(), precision=500, round=RoundToNearest) as ctx:
				counter=0
				iteratorExp=gmpy2.floor(gmpy2.log2(adjustLB))
				iterator=gmpy2.exp2(iteratorExp)
				while iterator<adjustUB:
					counter=counter+1
					iteratorExp=iteratorExp+1
					iterator=gmpy2.exp2(iteratorExp)
				return counter
				
class modelSolverLS:
	def __init__(self,roundingMode="rnd-to-nearest-even"):
		self.FPVariables=collections.OrderedDict()
		self.realPrivateCounterpartFP=collections.OrderedDict()
		self.RealVariables=collections.OrderedDict()
		self.Alias=collections.OrderedDict()
		
		self.nameforPrivateCounterpart="cover-"
		self.nameforFPArithmeticOperation="fpop-"
		self.nameforRealArithmeticOperation="realop-"
		self.nameforBooleanEncoding="comparison-"
		
		self.nameforMaxOperator="max-"
		self.nameforMinOperator="min-"
				
		self.nameforToReal="ConvToReal-"
		self.nameforToFP="ConvToFP-"
		self.nameforAbsolute="absop-"

		self.roundingModes=self.initRoundingModes()
		self.roundingMode=roundingMode
		self.roundingFunction=self.roundingModes[self.roundingMode]
		
		self.mapSymbolsRealToFP=self.initMapSymbolsRealToFP()
		self.mapSymbolsRealToReal=self.initMapSymbolsRealToReal()
		self.mapSymbolsArithmeticFlags=self.initMapSymbolsArithmeticFlags()
		self.mapSymbolsFPArithmeticToReal=self.initMapFPArithmeticToReal()
		self.mapSymbolsSpecialValues=self.initMapSymbolsSpecialValues()
		
		self.isLeaf=True
		#self.program=""
		#self.varEncoding=""
		
		self.preliminaryEncoding=self.initEncoding()
		self.status="Virgin"
		self.encodingOrderedList=[]
	
	def getEncoding(self):
		return (self.preliminaryEncoding+self.encodeVariablesAndProgram())
		
	def initMapSymbolsSpecialValues(self):
		myMap={}
		myMap["+inf"]="PlusInfinity"
		myMap["-inf"]="MinusInfinity"
		myMap["nan"]="NotANumber"
		return myMap
	
	def initMapSymbolsRealToFP(self):
		myMap={}
		myMap[">"]="g"
		myMap[">="]="ge"
		myMap["<"]="s"
		myMap["<="]="se"
		myMap["=="]="eq"
		myMap["!="]="neq"
		return myMap
	
	def initMapSymbolsRealToReal(self):
		myMap={}
		myMap[">"]=">"
		myMap[">="]=">="
		myMap["<"]="<"
		myMap["<="]="<="
		myMap["=="]="="
		myMap["!="]="not ( ="
		return myMap
	
	def initMapSymbolsArithmeticFlags(self):
		myMap={}
		myMap["+"]="add"
		myMap["-"]="sub"
		myMap["*"]="mul"
		myMap["/"]="divFloat"
		myMap["+FP"]="add"
		myMap["-FP"]="sub"
		myMap["*FP"]="mul"
		myMap["/FP"]="divFloat"
		return myMap
	
	def initMapFPArithmeticToReal(self):
		myMap={}
		myMap["+FP"]="+"
		myMap["-FP"]="-"
		myMap["*FP"]="*"
		myMap["/FP"]="/"
		myMap["+"]="+"
		myMap["-"]="-"
		myMap["*"]="*"
		myMap["/"]="/"
		return myMap
	
	def initRoundingModes(self):
		roundingModes=dict()
		roundingModes["rnd-to-negative"]="(define-fun rnd-to-negative ((x Real)) Int (to_int x))\n\n"
		roundingModes["ceil"]="(define-fun ceil ((x Real)) Int (ite (= x (to_int x)) (to_int x) (+ 1 (to_int x))))\n\n"
		roundingModes["rnd-to-positive"]=roundingModes["ceil"]+"\n"+"(define-fun rnd-to-positive ((x Real)) Int (ceil x))\n\n"
		roundingModes["rnd-to-zero"]=roundingModes["rnd-to-positive"]+"\n"+roundingModes["rnd-to-negative"]+"\n"+"(define-fun rnd-to-zero ((x Real)) Int (ite (> x 0.0) (rnd-to-negative x) (rnd-to-positive x)))\n\n"
		roundingModes["rnd-to-nearest-away"]="(define-fun rnd-to-nearest-away ((x Real)) Int (to_int (+ x 0.5)))\n\n"
		roundingModes["iseven"]="(define-fun iseven ((x Int)) Bool (ite (= 0 (mod x 2)) true false))\n\n"
		roundingModes["rnd-to-nearest-even"]=roundingModes["iseven"]+roundingModes["ceil"]+"(define-fun rnd-to-nearest-even ((x Real)) Int (let ((y (ceil (- x 0.5))) (z (to_int (+ x 0.5)))) (ite (= y z) y (ite (iseven y) y z))))\n\n"	
		return roundingModes
	
	def staticEncoding(self):
		f= open(os.path.dirname(__file__)+"/specialValues.txt","r")
		text=f.read()
		f.close()
		return text
	
	def buildContraintLine(self,expression):
		if expression!="":
			return "(assert "+expression+")\n\n"
		return ""
		
	def encodeConstraints(self,expression):
		self.encodingOrderedList.append("(assert "+expression+")\n\n")
		#self.program=self.program+expression
		return expression
	
	def buildNotLogicExpression(self,expression):
		return "(not "+expression+")"
		
	def buildAndOrLogicExpression(self,operator,expression):
		return "("+operator+" "+expression+")"
	
	def checkVariable(self, varName):
		if not (varName in self.RealVariables or varName in self.FPVariables or varName in self.Alias):
			print "Variable '"+varName+"' not declared."
			exit(0)
		return
		
	def buildAliasAssignment(self,alias,expression):
		if expression in self.RealVariables:
			if not alias in self.Alias:
				self.Alias[alias]=expression
			else:
				print "Alias '"+alias+"' already exists."
				exit(0)
		elif expression in self.FPVariables:
			if not alias in self.Alias:
				self.Alias[alias]=expression
			else:
				print "Alias '"+alias+"' already exists."
				exit(0)
		else:
			print "Cannot create an alias for expression: '"+expression+"'"
			exit(0)
	
	def safeIntervalForRealArithmetic(self,leftRealvar,symbol,rightRealvar):
		iv.prec=1000
		#mp.prec = 1000 maybe you need to use this for mpmathify
		
		rangeLeftVar=iv.mpf([leftRealvar.lb,leftRealvar.ub])
		rangeRightVar=iv.mpf([rightRealvar.lb,rightRealvar.ub])
		
		if "+" in symbol:
			rangeResultVar=rangeLeftVar+rangeRightVar
		if "-" in symbol:
			rangeResultVar=rangeLeftVar-rangeRightVar
		if "*" in symbol:
			rangeResultVar=rangeLeftVar*rangeRightVar
		if "/" in symbol:
			rangeResultVar=rangeLeftVar/rangeRightVar
		
		lb=mpmathify(rangeResultVar.a)
		ub=mpmathify(rangeResultVar.b)
		
		strLb=printFullNumberMPMATH(lb)
		strUb=printFullNumberMPMATH(ub)
		
		return strLb,strUb
	
	def safeIntervalForMaxMinOperatorReal(self,leftRealvar,symbol,rightRealvar):
		mp.prec=1000
		
		leftlb=mpmathify(leftRealvar.lb)
		leftub=mpmathify(leftRealvar.ub)
		
		rightlb=mpmathify(rightRealvar.lb)
		rightub=mpmathify(rightRealvar.ub)
		
		if symbol=="max":
			resultlb=max(leftlb,rightlb)
			resultub=max(leftub,rightub)
		elif symbol=="min":
			resultlb=min(leftlb,rightlb)
			resultub=min(leftub,rightub)
		else:
			print "Symbol can be max or min. Symbol not recognized."
			exit(0)
		
		strLb=printFullNumberMPMATH(resultlb)
		strUb=printFullNumberMPMATH(resultub)
		
		return strLb,strUb

	def safeIntervalForMaxMinOperatorFP(self,mantissaDest,exponentDest,leftFPvar,symbol,rightFPvar):
		mp.prec=mantissaDest
		
		leftlb=mpmathify(leftFPvar.quantizedlb)
		leftub=mpmathify(leftFPvar.quantizedub)
		
		rightlb=mpmathify(rightFPvar.quantizedlb)
		rightub=mpmathify(rightFPvar.quantizedub)
		
		if symbol=="max":
			resultlb=max(leftlb,rightlb)
			resultub=max(leftub,rightub)
		elif symbol=="min":
			resultlb=min(leftlb,rightlb)
			resultub=min(leftub,rightub)
		else:
			print "Symbol can be max or min. Symbol not recognized."
			exit(0)
		
		strLb=printFullNumberMPMATH(resultlb)
		strUb=printFullNumberMPMATH(resultub)
		
		return strLb,strUb
		
	def safeIntervalForFPArithmetic(self, mantissaDest,exponentDest,leftFPvar,symbol,rightFPvar):
		
		mantissaDestination=mantissaDest
		
		iv.prec=mantissaDestination
		#mp.prec = mantissaDestination maybe you need to use this for mpmathify

		
		rangeLeftVar=iv.mpf([leftFPvar.quantizedlb,leftFPvar.quantizedub])
		rangeRightVar=iv.mpf([rightFPvar.quantizedlb,rightFPvar.quantizedub])
		
		if "+" in symbol:
			rangeResultVar=rangeLeftVar+rangeRightVar
		if "-" in symbol:
			rangeResultVar=rangeLeftVar-rangeRightVar
		if "*" in symbol:
			rangeResultVar=rangeLeftVar*rangeRightVar
		if "/" in symbol:
			rangeResultVar=rangeLeftVar/rangeRightVar
		
		lb=mpmathify(rangeResultVar.a)
		ub=mpmathify(rangeResultVar.b)
		
		strLb=printFullNumberMPMATH(lb)
		strUb=printFullNumberMPMATH(ub)
		
		return strLb,strUb
	
	def encodeRealArithmeticExpression(self,leftOperand,symbol,rightOperand):
		if leftOperand in self.Alias:
			leftOperand=self.Alias[leftOperand]
		if rightOperand in self.Alias:
			rightOperand=self.Alias[rightOperand]
			
		if isNumericReal(leftOperand):
			realVarName=self.nameforRealArithmeticOperation+leftOperand
			if realVarName in self.RealVariables:
				realVar=self.RealVariables[realVarName]
			else:
				realVar=self.addVariableReal(realVarName,printFullNumberString(leftOperand),printFullNumberString(leftOperand))
			leftOperand=realVarName

		if isNumericReal(rightOperand):
			realVarName=self.nameforRealArithmeticOperation+rightOperand
			if realVarName in self.RealVariables:
				realVar=self.RealVariables[realVarName]
			else:
				realVar=self.addVariableReal(realVarName,printFullNumberString(rightOperand),printFullNumberString(rightOperand))
			rightOperand=realVarName
					
		if leftOperand in self.RealVariables and rightOperand in self.RealVariables:
			leftOperandVar=self.RealVariables[leftOperand]
			rightOperandVar=self.RealVariables[rightOperand]
			realVarName=self.nameforRealArithmeticOperation+leftOperandVar.name+symbol+rightOperandVar.name
			if realVarName in self.RealVariables:
				realVar=self.RealVariables[realVarName]
			else:
				lb,ub=self.safeIntervalForRealArithmetic(leftOperandVar,symbol,rightOperandVar)
				realVar=self.addVariableReal(realVarName,lb,ub)
				encodeOperation="(assert (= "+realVarName+" ( "+symbol+" "+ leftOperandVar.name + " "+rightOperandVar.name+")))\n"
				self.encodingOrderedList.append(encodeOperation)
				#self.program=self.program+encodeOperation

			return realVarName
		else:
			print "Real operation between non Real values: "+leftOperand+symbol+rightOperand+". Cast using toreal."
			exit(0)
	
		
	def encodeFPArithmeticExpression(self,leftOperand,symbol,rightOperand):
		def encodeRealArithmeticExpressionCounterpart(resultOperand,leftOperand,operation,rightOperand):
			return "(assert (= "+resultOperand+" ("+operation+" "+leftOperand+" "+rightOperand+")))\n\n"
		
		if leftOperand in self.Alias:
			leftOperand=self.Alias[leftOperand]
		if rightOperand in self.Alias:
			rightOperand=self.Alias[rightOperand]
		
		if leftOperand=="0.0":
			if rightOperand in self.FPVariables:
				
				rightOperandVar=self.FPVariables[rightOperand]
				fpVarName=self.nameforFPArithmeticOperation+"_0"+symbol+rightOperandVar.name
				
				if fpVarName in self.FPVariables:
					fpVar=self.FPVariables[fpVarName]
				else:
					fpVar=self.addVariableFP(fpVarName,"0.0","0.0",rightOperandVar.mantissa,rightOperandVar.exponent)
					#self.program=self.program+realEncoding
					
				leftOperand=fpVarName
			else:
				print "FP operation between non FP values. Cast using tofp."
				exit(0)

		if leftOperand in self.FPVariables and rightOperand in self.FPVariables:
			
			leftOperandVar=self.FPVariables[leftOperand]
			rightOperandVar=self.FPVariables[rightOperand]
						
			mantissaDest=max(leftOperandVar.mantissa,rightOperandVar.mantissa)
			exponentDest=max(leftOperandVar.exponent,rightOperandVar.exponent)

			fpVarName=self.nameforFPArithmeticOperation+leftOperandVar.name+symbol+rightOperandVar.name
			
			if fpVarName in self.FPVariables:
				fpVar=self.FPVariables[fpVarName]
			else:
				lb,ub=self.safeIntervalForFPArithmetic(mantissaDest,exponentDest,leftOperandVar,symbol,rightOperandVar)
				flagOperation="("+self.mapSymbolsArithmeticFlags[symbol]+" flag-"+leftOperand+" "+leftOperand+" flag-"+rightOperand+" "+rightOperand+")"
				fpVar=self.addVariableFP(fpVarName,lb,ub,mantissaDest,exponentDest,flagOperation)
				realEncoding=encodeRealArithmeticExpressionCounterpart(fpVar.realCounterpart.name,leftOperandVar.name,self.mapSymbolsFPArithmeticToReal[symbol], rightOperandVar.name)
				self.encodingOrderedList.append(realEncoding)
				#self.program=self.program+realEncoding
				#self.encoding=self.encoding+realEncoding
			return fpVarName
		else:
			print "FP operation between non FP values. Cast using tofp."
			exit(0)
	
	def encodeBooleanExpression(self,leftOperand,symbol,rightOperand):
		if leftOperand in self.Alias:
			leftOperand=self.Alias[leftOperand]
		if rightOperand in self.Alias:
			rightOperand=self.Alias[rightOperand]
			
		if isNumericReal(leftOperand):
			realVarName=self.self.nameforBooleanEncoding+leftOperand
			if realVarName in self.RealVariables:
				realVar=self.RealVariables[realVarName]
			else:
				realVar=self.addVariableReal(realVarName,printFullNumberString(leftOperand),printFullNumberString(leftOperand))
			leftOperand=realVarName

		if isNumericReal(rightOperand):
			realVarName=self.nameforBooleanEncoding+rightOperand
			if realVarName in self.RealVariables:
				realVar=self.RealVariables[realVarName]
			else:
				realVar=self.addVariableReal(realVarName,printFullNumberString(rightOperand),printFullNumberString(rightOperand))
			rightOperand=realVarName
			
		if leftOperand in self.RealVariables and rightOperand in self.RealVariables:
			encode="("+self.mapSymbolsRealToReal[symbol]+" "+leftOperand+" "+rightOperand+")"
			if "(" in symbol:
				encode=encode+")"
			return encode
		elif leftOperand in self.FPVariables and rightOperand in self.FPVariables:
			if symbol in self.mapSymbolsRealToFP:
				encode="("+self.mapSymbolsRealToFP[symbol]+" flag-"+leftOperand+" "+leftOperand+" flag-"+rightOperand+" "+rightOperand+")"
				return encode
			else:
				print "Symbol '"+symbol+"'not recognized"
				exit(0)
		else:
			print "Cannot compare a Real and a FP. Use tofp for numbers,nan,inf. You need explicit casting in the expression '"+leftOperand+" "+symbol+" "+rightOperand+"' "
			exit(0)
	
	def encodeMaxProblem(self,leftOperand,rightOperand):
		if leftOperand in self.Alias:
			leftOperand=self.Alias[leftOperand]
		if rightOperand in self.Alias:
			rightOperand=self.Alias[rightOperand]
		
		if isNumericReal(leftOperand):
			realVarName=self.nameforRealArithmeticOperation+leftOperand
			if realVarName in self.RealVariables:
				realVar=self.RealVariables[realVarName]
			else:
				realVar=self.addVariableReal(realVarName,printFullNumberString(leftOperand),printFullNumberString(leftOperand))
			leftOperand=realVarName
			
		if isNumericReal(rightOperand):
			realVarName=self.nameforRealArithmeticOperation+rightOperand
			if realVarName in self.RealVariables:
				realVar=self.RealVariables[realVarName]
			else:
				realVar=self.addVariableReal(realVarName,printFullNumberString(rightOperand),printFullNumberString(rightOperand))
			rightOperand=realVarName

		if leftOperand in self.RealVariables and rightOperand in self.RealVariables:
			leftOperandVar=self.RealVariables[leftOperand]
			rightOperandVar=self.RealVariables[rightOperand]
			realVarName=self.nameforMaxOperator+leftOperandVar.name+rightOperandVar.name
			if realVarName in self.RealVariables:
				realVar=self.RealVariables[realVarName]
			else:
				lb,ub=self.safeIntervalForMaxMinOperatorReal(leftOperandVar,"max",rightOperandVar)
				realVar=self.addVariableReal(realVarName,lb,ub)
				encodeOperation="(assert (= "+realVarName+" (maxReal " + leftOperandVar.name + " "+rightOperandVar.name+")))\n"
				self.encodingOrderedList.append(encodeOperation)
				#self.program=self.program+encodeOperation
			return realVarName
			
		elif leftOperand in self.FPVariables and rightOperand in self.FPVariables:
			leftOperandVar=self.FPVariables[leftOperand]
			rightOperandVar=self.FPVariables[rightOperand]

			mantissaDest=max(leftOperandVar.mantissa,rightOperandVar.mantissa)
			exponentDest=max(leftOperandVar.exponent,rightOperandVar.exponent)

			fpVarName=self.nameforMaxOperator+leftOperandVar.name+rightOperandVar.name

			if fpVarName in self.FPVariables:
				fpVar=self.FPVariables[fpVarName]
			else:
				lb,ub=self.safeIntervalForMaxMinOperatorFP(mantissaDest,exponentDest,leftOperandVar,"max",rightOperandVar)
				flagOperation="(maxFlag "+" flag-"+leftOperand+" "+leftOperand+" flag-"+rightOperand+" "+rightOperand+")"
				fpVar=self.addVariableFP(fpVarName,lb,ub,mantissaDest,exponentDest,flagOperation)
				realEncoding="(assert (= "+fpVar.realCounterpart.name+" (maxReal " + leftOperandVar.name + " "+rightOperandVar.name+")))\n"				
				self.encodingOrderedList.append(realEncoding)
				#self.program=self.program+realEncoding
				#self.encoding=self.encoding+realEncoding
			return fpVarName
		else:
			print "Cannot perform max operator with a Real and a FP. Use tofp for numbers,nan,inf. You need explicit casting in the expression 'max ("+leftOperand+","+rightOperand+")' "
			exit(0)
		
	def encodeMinProblem(self,leftOperand,rightOperand):
		if leftOperand in self.Alias:
			leftOperand=self.Alias[leftOperand]
		if rightOperand in self.Alias:
			rightOperand=self.Alias[rightOperand]
			
		if isNumericReal(leftOperand):
			realVarName=self.nameforRealArithmeticOperation+leftOperand
			if realVarName in self.RealVariables:
				realVar=self.RealVariables[realVarName]
			else:
				realVar=self.addVariableReal(realVarName,printFullNumberString(leftOperand),printFullNumberString(leftOperand))
			leftOperand=realVarName
			
		if isNumericReal(rightOperand):
			realVarName=self.nameforRealArithmeticOperation+rightOperand
			if realVarName in self.RealVariables:
				realVar=self.RealVariables[realVarName]
			else:
				realVar=self.addVariableReal(realVarName,printFullNumberString(rightOperand),printFullNumberString(rightOperand))
			rightOperand=realVarName

		if leftOperand in self.RealVariables and rightOperand in self.RealVariables:
			leftOperandVar=self.RealVariables[leftOperand]
			rightOperandVar=self.RealVariables[rightOperand]
			realVarName=self.nameforMinOperator+leftOperandVar.name+rightOperandVar.name
			if realVarName in self.RealVariables:
				realVar=self.RealVariables[realVarName]
			else:
				lb,ub=self.safeIntervalForMaxMinOperatorReal(leftOperandVar,"min",rightOperandVar)
				realVar=self.addVariableReal(realVarName,lb,ub)
				encodeOperation="(assert (= "+realVarName+" (minReal " + leftOperandVar.name + " "+rightOperandVar.name+")))\n"
				self.encodingOrderedList.append(encodeOperation)
				#self.program=self.program+encodeOperation
			return realVarName
			
		elif leftOperand in self.FPVariables and rightOperand in self.FPVariables:
			leftOperandVar=self.FPVariables[leftOperand]
			rightOperandVar=self.FPVariables[rightOperand]

			mantissaDest=max(leftOperandVar.mantissa,rightOperandVar.mantissa)
			exponentDest=max(leftOperandVar.exponent,rightOperandVar.exponent)

			fpVarName=self.nameforMinOperator+leftOperandVar.name+rightOperandVar.name

			if fpVarName in self.FPVariables:
				fpVar=self.FPVariables[fpVarName]
			else:
				lb,ub=self.safeIntervalForMaxMinOperatorFP(mantissaDest,exponentDest,leftOperandVar,"min",rightOperandVar)
				flagOperation="(minFlag "+" flag-"+leftOperand+" "+leftOperand+" flag-"+rightOperand+" "+rightOperand+")"
				fpVar=self.addVariableFP(fpVarName,lb,ub,mantissaDest,exponentDest,flagOperation)
				realEncoding="(assert (= "+fpVar.realCounterpart.name+" (minReal " + leftOperandVar.name + " "+rightOperandVar.name+")))\n"				
				self.encodingOrderedList.append(realEncoding)
				#self.program=self.program+realEncoding
				#self.encoding=self.encoding+realEncoding
			return fpVarName
		else:
			print "Cannot perform min operator with a Real and a FP. Use tofp for numbers,nan,inf. You need explicit casting in the expression 'max ("+leftOperand+","+rightOperand+")' "
			exit(0)
	
	def absolute(self,expression):
		if expression in self.Alias:
			expression=self.Alias[expression]
		
		if expression in self.RealVariables:
			var=self.RealVariables[expression]
			realVarName=self.nameforAbsolute+var.name
			if realVarName in self.RealVariables:
				realVar=self.RealVariables[realVarName]
			else:
				realVar=self.addVariableReal(realVarName, var.lb, var.ub)
				encodeAssignment="(assert (= (absvalue "+var.name+") "+realVar.name+"))\n\n"
				self.encodingOrderedList.append(encodeAssignment)
				#self.program=self.program+encodeAssignment
				#self.encoding=self.encoding+encodeAssignment
			return realVar.name
			
		elif expression in self.FPVariables:
			var=self.FPVariables[expression]
			absoluteVarName=self.nameforAbsolute+var.name
			if absoluteVarName in self.FPVariables:
				fpVar=self.FPVariables[absoluteVarName]
			else:
				inheritFlag="(absflag flag-"+var.name+")"
				fpVar=self.addVariableFP(absoluteVarName,var.quantizedlb,var.quantizedub,var.mantissa,var.exponent,inheritFlag)
				coverName=fpVar.realCounterpart.name
				encodeAssignment="(assert (= "+coverName+" (absvalue "+var.name+")))\n\n"
				self.encodingOrderedList.append(encodeAssignment)
				#self.program=self.program+encodeAssignment
				#self.encoding=self.encoding+encodeAssignment
			return fpVar.name
			
		elif isNumericReal(expression):
			realVarName=self.nameforAbsolute+expression
			if realVarName in self.RealVariables:
				realVar=self.RealVariables[realVarName]
			else:
				realVar=self.addVariableReal(realVarName, printFullNumberString(expression), printFullNumberString(expression))
			encodeAssignment="(assert (= (absvalue "+expression+") "+realVar.name+"))\n\n"
			self.encodingOrderedList.append(encodeAssignment)
			#self.program=self.program+encodeAssignment
			#self.encoding=self.encoding+encodeAssignment
			return realVar.name
		else:
			print "Expression '"+expression+"'not recognized."
			exit(0)
	
	def tofp(self, expression, mantissa, exponent):
		if expression in self.Alias:
			expression=self.Alias[expression]
		
		if expression in self.RealVariables:
			var=self.RealVariables[expression]
			fpVarName=self.nameforToFP+var.name
			if (fpVarName in self.FPVariables and 
				self.FPVariables[fpVarName].mantissa==int(mantissa) and 
				self.FPVariables[fpVarName].exponent==int(exponent)):
					fpVar=self.FPVariables[fpVarName]
			else:
				fpVar=self.addVariableFP(fpVarName,var.lb,var.ub,int(mantissa),int(exponent))
				coverName=fpVar.realCounterpart.name
				encodeAssignment="(assert (= "+coverName+" "+var.name+"))\n\n"
				self.encodingOrderedList.append(encodeAssignment)
				#self.program=self.program+encodeAssignment
				#self.encoding=self.encoding+encodeAssignment
			return fpVarName
		elif expression in self.FPVariables:
			var=self.FPVariables[expression]
			fpVarName=self.nameforToFP+var.name
			if (fpVarName in self.FPVariables and
				self.FPVariables[fpVarName].mantissa==int(mantissa) and 
				self.FPVariables[fpVarName].exponent==int(exponent)):
					fpVar=self.FPVariables[fpVarName]
			else:
				inheritFlag="flag-"+var.name
				fpVar=self.addVariableFP(fpVarName,var.quantizedlb,var.quantizedub,int(mantissa),int(exponent),inheritFlag)
				coverName=fpVar.realCounterpart.name
				encodeAssignment="(assert (= "+coverName+" "+var.name+")))\n\n"
				self.encodingOrderedList.append(encodeAssignment)
				#self.program=self.program+encodeAssignment
				#self.encoding=self.encoding+encodeAssignment
			return fpVarName
		elif isNumericReal(expression):
			fpVarName=self.nameforToFP+str(expression)+"-"+str(mantissa)+"-"+str(exponent)
			fpVar=self.addVariableFP(fpVarName,str(expression),str(expression),int(mantissa),int(exponent))
			if (fpVarName in self.FPVariables and
				self.FPVariables[fpVarName].mantissa==int(mantissa) and 
				self.FPVariables[fpVarName].exponent==int(exponent)):
					fpVar=self.FPVariables[fpVarName]
			else:
				coverName=fpVar.realCounterpart.name
				encodeAssignment="(assert (= "+coverName+" "+printFullNumberString(expression)+"))\n\n"
				self.encodingOrderedList.append(encodeAssignment)
				#self.program=self.program+encodeAssignment
				#self.encoding=self.encoding+encodeAssignment
			return fpVarName
			
		elif isNumericSpecialValue(expression):
			fpVarName=self.nameforToFP+str(expression)+"-"+str(mantissa)+"-"+str(exponent)
			if fpVarName in self.FPVariables:
				fpVar=self.FPVariables[fpVarName]
			else:
				fpVar=self.addVariableFP(fpVarName,str(expression),str(expression),int(mantissa),int(exponent),self.mapSymbolsSpecialValues[expression])
			return fpVarName
		else:
			print "Expression '"+expression+"' does not exist or it has not been declared."
			exit(0)
		
	def toreal(self, expression):
		if expression in self.Alias:
			expression=self.Alias[expression]
		
		if expression in self.FPVariables:
			var=self.FPVariables[expression]
			realVarName=self.nameforToReal+var.name
			if realVarName in self.RealVariables:
				realVar=self.RealVariables[realVarName]
			else:
				realVar=self.addVariableReal(realVarName, var.quantizedlb, var.quantizedub)
				encodeAssignment="(assert (= (To_Real flag-"+var.name+" "+var.name+") "+realVar.name+"))\n\n"
				self.encodingOrderedList.append(encodeAssignment)
				#self.program=self.program+encodeAssignment
				#self.encoding=self.encoding+encodeAssignment
			return realVarName
		else:
			print "Expression '"+expression+"'is already a real or it has not been declared."
			exit(-1)
		
	def addVariableReal(self,name,lb,ub):
		if name in self.RealVariables or name in self.FPVariables or name in self.Alias:
			print "Variable '"+name+"' found twice!"
			exit(-1)
		
		self.RealVariables[name]=RealVariable(name,lb,ub)
		if not name in self.encodingOrderedList:
			self.encodingOrderedList.append(name)
		#self.encoding=self.encoding+self.RealVariables[name].encode()
		return self.RealVariables[name]
	
	def encodeVariablesAndProgram(self):
		program=""
		for val in self.encodingOrderedList:
			if val in self.RealVariables:
				program=program+self.RealVariables[val].encode()
			elif val in self.FPVariables:
				program=program+self.FPVariables[val].encode()
			else:
				program=program+val
		return program
	
	def createFlagFromInit(self,lb,ub):
		if lb=="+inf" and ub=="+inf":
			return self.mapSymbolsSpecialValues[lb]
		if lb=="inf" and ub=="inf":
			return self.mapSymbolsSpecialValues[lb]
		if lb=="-inf" and ub=="-inf":
			return self.mapSymbolsSpecialValues[lb]
		if lb=="nan" and ub=="nan":
			return self.mapSymbolsSpecialValues[lb]
		return ""
	
	def addVariableFP(self,name,lb,ub,mantissa,exponent,inheritFlag=""):
		if name in self.RealVariables or name in self.FPVariables or name in self.Alias:
			print "Variable '"+name+"' found twice!"
			exit(0)
		
		self.realPrivateCounterpartFP[self.nameforPrivateCounterpart+name]=RealVariable(self.nameforPrivateCounterpart+name,lb,ub)
		if inheritFlag=="":
			inheritFlag=self.createFlagFromInit(lb,ub)
		self.FPVariables[name]=FPVariable(name,lb,ub,mantissa,exponent,self.realPrivateCounterpartFP[self.nameforPrivateCounterpart+name],inheritFlag)
		if not name in self.encodingOrderedList:
			self.encodingOrderedList.append(name)
		#self.encoding=self.encoding+self.FPVariables[name].encode()
		return self.FPVariables[name]
	
	def encodeQuantizationProcedure(self):
		encoding="(define-fun quantize ((val Real) (exp-p-minus-e-val Real)) Real \n"
		encoding=encoding+"\t (to_real ("+self.roundingMode+" (* val exp-p-minus-e-val))))\n\n"
		return encoding
		
	def initEncoding(self):
		encoding=self.roundingFunction
		encoding=encoding+self.encodeQuantizationProcedure()
		encoding=encoding+self.staticEncoding()
		return encoding
	
	def printVariables(self):
		res=""
		for var in self.RealVariables:
			 res=res+str(self.RealVariables[var])+", "
		res="Real: "+res+"\nFP: "
		for var in self.FPVariables:
			 res=res+str(self.FPVariables[var])+", "
		res=res+"\nAlias: "
		for var in self.Alias:
			 res=res+str(self.Alias[var])+", "
		print res
