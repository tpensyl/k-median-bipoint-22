import pickle,argparse,yaml,signal,json
import numpy as np

from utilities import simplify_mass,replace_inf,init_files
from methods import HeapMethod,LayeredMethod

# BASE = "output/"
BASE = "../../../../../../ssd2/kishen/kmedian/output/"

def handler(signum,frame):
    exit(1)
    
signal.signal(signal.SIGINT, handler)


def main():
	'''
	Input parser
	-n	Number of g thresholds
	-s	Start iteration (optional, current.json required if not 0)
	'''
	parser = argparse.ArgumentParser()
	parser.add_argument('-n','--n', action="store", dest="n", type=int)
	parser.add_argument('--start','-s', action="store", dest="start", type=int, default=0)
	args = parser.parse_args()

	n = args.n+1
	iter_num = args.start

	# Remaining input from params file
	params = {}
	with open("./params/g"+ str(n-1) +".yaml", 'r') as path:
		params = yaml.load(path,Loader=yaml.FullLoader)
	method = params["method"] # heap or layer
	solver = params["solver"] # GLOP, CPLEX, GUROBI, MOSEK, etc

	if iter_num==0:
		if method=="heap":
			init_files(n)
		next_intervals = [
			{"g":params["g"],"b":params["b"],"gammaA":replace_inf(params["gammaA"]),
			"end":False,"value":np.inf,"params":[]}
		]
	else:
		next_intervals = []
		with open(BASE + "g"+str(n-1)+"/heap/current.json","r") as f:
			content = json.load(f)
			next_intervals = content["intervals"]
			if iter_num!= content["iter"]:
				print("Error Iter_num Init")
				exit(1)
	
	mass_stuff = {}
	with open("mass/g" + str(n-1) + "-mass","rb") as f:
		mass_stuff = pickle.load(f)
	mass = mass_stuff[params["mass"]]
	mass = simplify_mass(mass,n)

	if method == "layer":
		LayeredMethod(iter_num,n,mass,next_intervals,max_iters=params["max_iters"],expected=params["expected"],solver=solver)
	elif method == "heap":
		HeapMethod(iter_num,n,mass,next_intervals,max_iters=params["max_iters"],max_jobs=params["max_jobs"],expected=params["expected"],solver=solver)

if __name__=="__main__":
	main()