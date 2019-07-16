import shlex
import subprocess

class z3wrapper:
	def __init__(self,encoding,timeout):
		self.numberToLabel=self.initMap()
		self.encoding=encoding
		self.timeout=timeout

	def initMap(self):
		myMap={}
		myMap["0.0"]="MinusInfinity"
		myMap["1.0"]="PlusInfinity"
		myMap["2.0"]="MinusZero"
		myMap["3.0"]="PlusZero"
		myMap["4.0"]="Numbers"
		myMap["5.0"]="NotANumber"
		return myMap
		
	def getEncodings(self):
		#(set-option :timeout 2000)
		#\n(set-option :pp.decimal true)\n
		#\n(set-option :pp-decimal-precision 5)\n
		encodings=[]
		mandatoryStartEncoding=""
		startEncoding=[""]
		#checkTactics =(["\n(check-sat)\n(get-model)",
		#				"\n(check-sat-using qfnra-nlsat)\n(get-model)",
		#				"\n(check-sat-using nlsat)\n(get-model)",
		#				"\n(check-sat-using qfnra)\n(get-model)",
		#				"\n(check-sat-using (or-else (and-then qfnra-nlsat fail) (and-then smt fail)))\n(get-model)",
		#				"\n(check-sat-using (then simplify solve-eqs qfnra-nlsat))\n(get-model)",
		#				"\n(check-sat-using (then simplify solve-eqs nlsat))\n(get-model)",
		#				"\n(check-sat-using (then simplify solve-eqs qfnra))\n(get-model)",
		#				"\n(check-sat-using (and-then qfnra-nlsat smt))\n(get-model)",
		#				"\n(check-sat-using (then simplify bit-blast qfnra))\n(get-model)",
		#				"\n(check-sat-using (then simplify solve-eqs smt))\n(get-model)",
		#				"\n(check-sat-using (then simplify solve-eqs sat))\n(get-model)"])
		#checkTactics =["\n(check-sat-using (par-or (then solve-eqs smt) (then qfnra-nlsat) (then nlsat) (then simplify qfnra-nlsat) (then ctx-solver-simplify qfnra-nlsat)))\n(get-model)"]
		checkTactics =["\n(check-sat)\n(get-model)","\n(check-sat-using qfnra-nlsat)\n(get-model)"]
		
		for start in startEncoding:
			for check in checkTactics:
				#print check
				encodings.append(mandatoryStartEncoding+start+self.encoding+check)
		return encodings
	
	def getCommand(self):
		return "z3 -T:"+str(self.timeout)+" "
	
	def getFileNamePrefix(self):
		return "z3"
		
	def checkFlagVariables(self,line):
		if ("PlusInfinity" 	in line or  
			"NotANumber" 	in line or
			"PlusZero"		in line or
			"Number"		in line or
			"MinusInfinity"	in line or
			"MinusZero"		in line):
			return True
		return False
	
	def isLineWithFlag(self,line):
		if "flag-" in line:
			return True
		return False
	
	def fromNumberToLabel(self,line):
		tmp=line
		for key,value in self.numberToLabel.items():
			tmp=tmp.replace(key,value)
		return tmp
	
	def hasNumbers(self,inputString):
		return any(char.isdigit() for char in inputString)
	
	def elaborateOutput(self,output):
		res=""
		i=0
		lines=output.split("\n")
		if "unsat" in lines[0]:
			return "unsat"
		elif "error" in lines[0]:
			return "error"
		elif "timeout" in lines[0]:
			return "timeout"
		elif "unknown" in lines[0]:
			return "unknown"
		elif "sat" in lines[0]:
			return output
			'''while i < len(lines):
				if self.checkFlagVariables(lines[i]):
					i=i+2
				else:
					if self.isLineWithFlag(lines[i-1]):
						res=res+self.fromNumberToLabel(lines[i])+"\n"
					else:
						res=res+lines[i]+"\n"
					i=i+1
			return res'''
		else:
			print "Error in the output from the solver."
			exit(0)
