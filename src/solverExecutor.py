import shlex
import shutil
import subprocess
import multiprocessing
import concurrent.futures
import os
import signal
import sys

def call_proc(cmd,solver,procDict):
	p = subprocess.Popen(shlex.split(cmd), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
	procDict[p.pid]=1
	out, err = p.communicate()
	return out, err

class solverExecutor:
	
	def __init__(self,listSolvers,tmpDir):
		self.listSolvers=listSolvers
		self.tmpDir = tmpDir
		
	def execute(self,index):
		
		pool = concurrent.futures.ThreadPoolExecutor(max_workers=multiprocessing.cpu_count()) 
		results = []
		i=0
		processes={}
		
		retOutput=""
		
		for solver in self.listSolvers:
			for encoding in solver.getEncodings():
				filename=self.tmpDir+"/prob_"+str(index)+"_"+solver.getFileNamePrefix()+"_"+str(i)+".smt2"
				createFile=open(filename,"w+")
				createFile.write(encoding)
				createFile.close()
				command=solver.getCommand()+filename
				results.append(pool.submit(call_proc, command, solver, processes))
				i=i+1
		
		counterUnknown=0
		counterTimeout=0
		for res in concurrent.futures.as_completed(results):
			tmpResult=res.result()
			if tmpResult[1]=="":
				orig_out=tmpResult[0]
				#print orig_out
				#out=orig_out
				out=solver.elaborateOutput(orig_out)
				#print out
				if "sat" in out.lower():
					retOutput=out
					break
				elif "unsat" in out.lower():
					retOutput=out
					break
				elif "error" in out.lower():
					retOutput="solver error"
					break
				elif "timeout" in out.lower():
					counterTimeout=counterTimeout+1
					if counterTimeout==len(results):
						retOutput="timeout"
						break
					pass
				elif "unknown" in out.lower():
					counterUnknown=counterUnknown+1
					if counterUnknown==len(results):
						retOutput="unknown"
						break
					pass
				else:
					print "Error in the solver!!"
					retOutput="solver error"
					break
			else:
				print "Error while calling the solver!"
		
		for proc in processes:
			try:
				os.kill(proc, signal.SIGTERM)
			except:
				continue
		
		for future in results:
			future.cancel()
		
		pool.shutdown(wait=True)
		
		if retOutput=="" and counterTimeout!=0:
			retOutput="timeout"
			
		return retOutput
