from src.fpryacc import *
from src.solverExecutor import *
from src.z3wrapper import *
from src.branchandbound import *
import src.modelSolverLS as LS
import time
import concurrent.futures
import copy 

def compute(text, currentSolver, deepThreshold, timeout, debug, index, tmpDir):
	
	tmpsolver=copy.deepcopy(currentSolver)

	real_variables= tmpsolver.RealVariables
	coverFP_variables= tmpsolver.realPrivateCounterpartFP
	fp_variables= tmpsolver.FPVariables
	

	startTime=time.time()
	print "Start Encoding!"
	myYacc=FPRyacc(text,tmpsolver,False,True,debug)

	z3 = z3wrapper(tmpsolver.getEncoding(),timeout)
	print "End Encoding!"
	print "Start Solving!"
	solverList = [z3]
	executor = solverExecutor(solverList,tmpDir)
	retOutput = executor.execute(index)
	endTime = time.time()
	print "End Solving!"
	
	print "Info-Output: "+str(retOutput)
	print "Info-Time: "+str(endTime-startTime)
	
	if "timeout" in retOutput:
		print "Start BaB!"
		bnb=BranchAndBound(deepThreshold)
		bnb.producePaving(0,currentSolver,1)
		print "Finish BaB!"
		return retOutput, index, bnb.solvers
	elif "unknown" in retOutput:
		print "unknown detected!!"
		exit(-1)
	elif "unsat" in retOutput:
		return retOutput, index, []
	elif "sat" in retOutput:
		print "Start BaB!"
		bnb=BranchAndBound(deepThreshold)
		bnb.producePaving(0,currentSolver,1)
		print "Finish BaB!"
		return retOutput, index, bnb.solvers
	else:
		print "I do not know whats going on"
		exit(-1)

debug=False

filepath="./input.txt"

tmpDir = "./tmp"
if os.path.exists(tmpDir):
	shutil.rmtree(tmpDir)
os.makedirs(tmpDir)

f= open(filepath,"r")
text=f.read()
text=text[:-1]	
f.close()

rounding="rnd-to-nearest-even"
print "Start Validator Parser!"
initsolver=LS.modelSolverLS(rounding)
myYaccOnlyVariables=FPRyacc(text,initsolver,True,False,debug) #extract only variables
print "End Parser!"

solversList=[]
solversList.append(initsolver)
deepThreshold=1
iteratorSolvers=0

timeout=10.0
#maxtimeout=120.0

maxLenghtList=2000
results = []
pool = concurrent.futures.ProcessPoolExecutor(max_workers=multiprocessing.cpu_count())

while iteratorSolvers < len(solversList):

	results = []
	
	tmpIteratorSolver=iteratorSolvers
	
	for currentSolver in solversList[tmpIteratorSolver:]:
		results.append(pool.submit(compute, text, currentSolver, deepThreshold, timeout, debug, iteratorSolvers,tmpDir))
		iteratorSolvers=iteratorSolvers+1
		
	for res in concurrent.futures.as_completed(results):
		satOrUnsatOrTimeout, indexParent, childrenSolver=res.result()
		solversList[indexParent].status=satOrUnsatOrTimeout
		if len(solversList)<maxLenghtList:
			if len(childrenSolver)>=1:
				solversList[indexParent].isLeaf=False
				solversList=solversList+childrenSolver
		#timeout=min(timeout+0.5,maxtimeout)
		#for solver in tmpResult:
		#	solver.printVariables()
	
	print "i: "+str(iteratorSolvers)
	print "len: "+str(len(solversList))
	#print solversList
	#raw_input()

counterUnsat=0
counterSat=0
counterTimeout=0
for solver in solversList:
	if solver.isLeaf:
		if solver.status=="unsat":
			counterUnsat=counterUnsat+1
		elif solver.status=="timeout":
			counterTimeout=counterTimeout+1
		elif "sat" in solver.status:
			counterSat=counterSat+1
		else:
			print "Problem in the analysis"
			exit(-1)
			
print "Sat: "+str(counterSat)
print "Timeout: "+str(counterTimeout)
print "Unsat: "+str(counterUnsat)

print "Tot: "+str(counterSat+counterTimeout+counterUnsat)
print "Prob: "+str(float(counterSat+counterTimeout)/(counterSat+counterUnsat+counterTimeout))
