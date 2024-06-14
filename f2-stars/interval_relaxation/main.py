import pickle,argparse,yaml,signal
import numpy as np
import multiprocessing as mp
from tqdm import tqdm as tqdm

from utilities import simplify_mass,replace_inf
from sql import insert_entries, query_entries, delete_all_entries, dump_entry, create_db
from solvers import LPSolver
from utilities import divide_interval

# Path to output files
BASE = "output/"

# Keyboard Interrupt handler
def handler(signum,frame):
	exit(1)
signal.signal(signal.SIGINT, handler)

# Processing Each Interval
def process_interval(n, mass, iter_num, interval, expected, solver):
	# Solving the LP
	solver = LPSolver(n,mass,interval,iter_num,solver=solver)
	value = solver.solve()
	params = solver.get_params()
	# Updating interval with values to variables
	interval["value"] = value
	interval["params"] = params
	# Dumping processed interval
	entry = [value]
	entry += [x for x in interval["b"]]
	for i in range(len(interval["gammaA"])):
		entry += [interval["gammaA"][i][0],interval["gammaA"][i][1]]
	entry += params.values()
	dump_entry(n-1, tuple(entry))
	# If interval value already within expected, stop
	if value <= expected:
		return
	# Spawning new intervals if value > expected
	new_intervals = []
	new_intervals = divide_interval(interval,n,value)
	entries = []
	for new_interval in new_intervals:
		entry = [new_interval["value"]]
		entry += [x for x in new_interval["b"]]
		for i in range(len(new_interval["gammaA"])):
			entry += [new_interval["gammaA"][i][0],new_interval["gammaA"][i][1]]
		entries.append(tuple(entry))
	if len(entries) > 0:
		insert_entries(n-1, entries)

def main():
	'''
	Input parser
	-n		Number of g thresholds
	-t  	Target Threshold (will stop when all intervals are below this value, not same as "expected")
	-i		Iteration Number (default 0)
	-nproc 	Number of processors (default: mp.cpu_count())
	'''
	parser = argparse.ArgumentParser()
	parser.add_argument('-n', action="store", dest="n", type=int)
	parser.add_argument('-t', action="store", dest="thresh", type=float)
	parser.add_argument('-i', action="store", dest="iter", type=int, default=0)
	parser.add_argument('-nproc', action="store", dest="nproc", type=int, default=mp.cpu_count())
	args = parser.parse_args()

	# Input Params
	n = args.n+1 # Works for n=1+1 or 2+1
	iter_num = args.iter
	thresh = args.thresh
	init = iter_num==0 # init if 0th iteration
	nproc = args.nproc

	# Remaining input from params file
	params = {}
	with open(f"./params/g{n-1}.yaml", 'r') as path:
		params = yaml.load(path,Loader=yaml.FullLoader)
	solver = params["solver"] # GLOP, CPLEX, GUROBI, MOSEK, etc
	expected = params["expected"]

	# Function to Fetch Intervals from DB
	def fetch_intervals():
		intervals = []
		results = query_entries(n-1, thresh, params["max_jobs"])
		for result in results:
			intervals.append({
				"g": params["g"],
				"b": [result[2],result[3]],
				"gammaA": [[result[i],result[i+1]] for i in range(4,4+len(result[4:]),2)],
				"end": False,
				"value": result[1],
				"params":[],
			})
		return intervals
	
	if init: # Init interval
		delete_all_entries(n-1)
		next_intervals = [{
			"g": params["g"],
			"b": params["b"],
			"gammaA": replace_inf(params["gammaA"]),
			"end": False,
			"value": np.inf,
			"params":[],
		}]
	else: # Fetch Intervals from DB
		next_intervals = fetch_intervals()
		
	# print(next_intervals)
	
	# Load algorithms' probability mass from pickle files
	mass_stuff = {}
	with open(f"mass/g{n-1}-mass","rb") as f:
		mass_stuff = pickle.load(f)
	mass = mass_stuff[params["mass"]]
	mass = simplify_mass(mass,n)
	
	# Start Multiprocessing and main loop
	pool = mp.Pool(nproc)
	for it in range(iter_num, iter_num+params["max_iters"]):
		print("iter =",it, flush=True)
		if len(next_intervals) == 0:
			print("Done",flush=True)
			break
		# Spawn parallel processes to process intervals
		jobs = []
		for interval in next_intervals:
			job = pool.apply_async(process_interval,(n,mass,it,interval,expected,solver))
			jobs.append(job)
		for job in tqdm(jobs):
			job.get()
		
		# Fetching new intervals
		next_intervals = fetch_intervals()
	pool.close()
	pool.join()


if __name__=="__main__":
	main()