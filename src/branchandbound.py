from mpmath import *
from mpmath import iv
from printing import *
import numpy as np
import copy

class BranchAndBound:
	def __init__(self, deepTree):
		self.thresholdDeepTree=deepTree
		self.solvers=[]
	
	def emptyPriorityLists(self):
		return [],0.0,[]

	def recomputePriorityLists(self,variables):
		priorityList=sorted(variables.values(), key=lambda x: x.priority, reverse = True)
		print "priorityList",priorityList
		sumPriority=self.getSumPriorities(priorityList)
								
		if sumPriority==0.0: #all variables are exausted
			return None,None,None
			
		priorityValues=self.getPriorityForEachVariable(priorityList,sumPriority)
		return priorityList,sumPriority,priorityValues
		
	def getPriorityForEachVariable(self,listVar,sumPriority):
		i=0
		priorities=[]
		while i<len(listVar):
			if sumPriority!=0.0:
				print listVar[i].name,float(listVar[i].priority), float(listVar[i].priority)/sumPriority
				priorities.append(float(listVar[i].priority)/sumPriority)
			else:
				priorities.append(0.0)
			i=i+1
		return priorities
		
	def getSumPriorities(self,listVar):
		acc=0.0
		for var in listVar:
			acc=acc+var.priority
		return acc
	
	def giveMeAVariable(self,priorityList,priorityValues):
		return priorityList[0]
	
	#0 is Real, 1 is FP
	def decideNextToSplit(self,realVars,FPVars):
		countReal=len(realVars)
		countFP=len(FPVars)
		tot=float(countReal+countFP)
		#print "Real: "+str(countReal/tot)
		#print "FP: "+str(countFP/tot)
		res=np.random.choice([0,1], 1, p=[countReal/tot,countFP/tot], replace=False)[0]
		#print "Next to split: "+str(res)
		return res
		
	def producePaving(self, iterator, solver, flag):
		
		iv.prec=1000
		
		nextSplit=self.decideNextToSplit(solver.RealVariables,solver.FPVariables)
		
		if len(solver.RealVariables)==0 and len(solver.FPVariables)==0:
			print "No variables to split!"
			exit(0)
			
		if len(solver.RealVariables)==0:
			flag=1
			
		if len(solver.FPVariables)==0:
			flag=0
				
		if iterator<self.thresholdDeepTree:
			if flag==0:
				
				priorityList,sumPriority,priorityValues=self.recomputePriorityLists(solver.RealVariables)
				#print priorityList,sumPriority,priorityValues
				if priorityList==None and sumPriority==None and priorityValues==None:
					return []#self.producePaving(iterator+1, solver, 1)
				
				var=self.giveMeAVariable(priorityList,priorityValues)
				
				middlePowerExp=var.middlePoint
				
				if middlePowerExp=="nan":
					return []#self.producePaving(iterator+1, solver, 1)
				else:
					newSolver=copy.deepcopy(solver)
					del newSolver.RealVariables[var.name]
					newSolver.addVariableReal(var.name,var.lb,middlePowerExp)
					del solver.RealVariables[var.name]
					solver.addVariableReal(var.name,middlePowerExp,var.ub)
					self.producePaving(iterator+1, newSolver, nextSplit)
					self.producePaving(iterator+1, solver, nextSplit)
				
			elif flag==1:
				priorityList,sumPriority,priorityValues=self.recomputePriorityLists(solver.FPVariables)
				
				if priorityList==None and sumPriority==None and priorityValues==None:
					return []#self.producePaving(iterator+1, solver, 0)
					
				var=self.giveMeAVariable(priorityList,priorityValues)
									
				middlePowerExp=var.middlePoint
				
				if middlePowerExp=="nan":
					return []#self.producePaving(iterator+1, solver, 0)
				else:
					
					newSolver=copy.deepcopy(solver)

					realCounterVar=solver.realPrivateCounterpartFP[solver.nameforPrivateCounterpart+var.name]
					
					del newSolver.realPrivateCounterpartFP[solver.nameforPrivateCounterpart+var.name]
					del newSolver.FPVariables[var.name]
					
					newSolver.addVariableFP(var.name,realCounterVar.lb,middlePowerExp,var.mantissa,var.exponent,"")
					
					del solver.realPrivateCounterpartFP[newSolver.nameforPrivateCounterpart+var.name]
					del solver.FPVariables[var.name]
					
					solver.addVariableFP(var.name,middlePowerExp,realCounterVar.ub,var.mantissa,var.exponent,"")
					
					self.producePaving(iterator+1, newSolver, nextSplit)
					self.producePaving(iterator+1, solver, nextSplit)
			else:
				print "Flag can be 1 or 0"
				exit(-1)
		else:
			self.solvers.append(solver)
			return
