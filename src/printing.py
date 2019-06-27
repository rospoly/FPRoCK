from gmpy2 import *
import gmpy2
from mpmath import *
from decimal import *
import decimal

def containsOnlyZeroOrDot(strNumber):
	for digit in strNumber:
		if digit=="0" or digit==".":
			continue
		else:
			return False
	return True

def printFullNumberMPMATH(mpmathNumber):
	mp.pretty=True
	i=5000
	num=nstr(mpmathNumber,i)
	while nstr(mpmathNumber,i*2)!=num:
		i=i*2
		num=nstr(mpmathNumber,i)
	return num
	
def printFullNumberMPFR(mpfrNumber):
	if gmpy2.is_zero(mpfrNumber):
		return "0.0"
	if gmpy2.is_infinite(mpfrNumber) and mpfrNumber>mpfr("0.0"):
		return "+inf"
	if gmpy2.is_infinite(mpfrNumber) and mpfrNumber<mpfr("0.0"):
		return "-inf"
	if gmpy2.is_nan(mpfrNumber):
		return "nan"
	
	i=5000
	myFormat="{0:."+str(i)+"f}"	
	value=myFormat.format(mpfrNumber)

	while containsOnlyZeroOrDot(value):
		i=i*2
		myFormat="{0:."+str(i)+"f}"
		value=myFormat.format(mpfrNumber)
	
	while value[-1]!="0":
		i=i*2
		myFormat="{0:."+str(i)+"f}"
		value=myFormat.format(mpfrNumber)
		
	while value[-1]=="0":
		value=value[:-1]
	
	if value[-1]==".":
		value=value+"0"
	
	return value

def printFullNumberString(inputString):
	tmp=Decimal(inputString)
	
	if tmp==Decimal("0"):
		return "0.0"
	if tmp==Decimal("Infinity"):
		return "+inf"
	if tmp==Decimal("-Infinity"):
		return "-inf"
	if str(tmp)==str(Decimal("NaN")):
		return "nan"
	
	i=5000
	myFormat="{0:."+str(i)+"f}"	
	value=myFormat.format(tmp)

	while containsOnlyZeroOrDot(value):
		i=i*2
		myFormat="{0:."+str(i)+"f}"
		value=myFormat.format(tmp)
	
	while value[-1]!="0":
		i=i*2
		myFormat="{0:."+str(i)+"f}"
		value=myFormat.format(tmp)
		
	while value[-1]=="0":
		value=value[:-1]
	
	if value[-1]==".":
		value=value+"0"
	
	return value
