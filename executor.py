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
	print "Start Encoding! (original problem)"
	myYacc=FPRyacc(text,tmpsolver,False,True,debug)
	print "End Encoding!  (original problem)"
	
	print "Start Solving!  (original problem)"
	z3 = z3wrapper(tmpsolver.getEncoding(),timeout)
	solverList = [z3]
	executor = solverExecutor(solverList,tmpDir)
	retOutput = executor.execute(index)
	endTime = time.time()
	print "End Solving!  (original problem)"
	
	print "Info-(original problem)-Output: "+str(retOutput)
	print "Info-(original problem)-Time: "+str(endTime-startTime)
	
	if "timeout" in retOutput:
		print "Start BaB!"
		bnb=BranchAndBound(deepThreshold)
		bnb.producePaving(0,currentSolver,1)
		print "Finish BaB!"
		currentSolver.status=retOutput
		return bnb.solvers
	elif "unknown" in retOutput:
		print "unknown detected!!"
		exit(-1)
	elif "unsat" in retOutput:
		currentSolver.status=retOutput
		return []
	elif "sat" in retOutput:
		currentSolver.status=retOutput
		print "Start BaB!"
		bnb=BranchAndBound(deepThreshold)
		bnb.producePaving(0,currentSolver,1)
		print "Finish BaB!"
		return bnb.solvers
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

timeout=3.0
maxtimeout=30.0

maxLenghtList=10000000
results = []
pool = concurrent.futures.ProcessPoolExecutor(max_workers=multiprocessing.cpu_count())

while iteratorSolvers < len(solversList):
	results = []
	
	tmpIteratorSolver=iteratorSolvers
	
	for currentSolver in solversList[tmpIteratorSolver:]:
		#tmp_solver=copy.deepcopy(currentSolver)
		results.append(pool.submit(compute, text, currentSolver, deepThreshold, timeout, debug, iteratorSolvers,tmpDir))
		iteratorSolvers=iteratorSolvers+1
		
	for res in concurrent.futures.as_completed(results):
		tmpResult=res.result()
		solversList=solversList+tmpResult
		timeout=min(timeout+0.5,maxtimeout)
		for solver in tmpResult:
			solver.printVariables()
	
	print "i: "+str(iteratorSolvers)
	print "len: "+str(len(solversList))
	#print solversList
	#raw_input()
