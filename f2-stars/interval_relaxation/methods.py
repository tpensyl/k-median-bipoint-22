import numpy as np
import time
import multiprocessing as mp
from tqdm import tqdm

from solvers import LPSolver
from utilities import divide_interval, dump_results, heap_dump, get_next


def update(queue,mdict):
    results = []
    next_intervals = []
    worst = 0
    while 1:
        curr = queue.get()
        if curr == []:
            mdict['results'] = results
            mdict['next'] = next_intervals
            mdict["worst"] = worst
            break
        interval,new_intervals = curr
        worst = max(worst,interval["value"])
        results.append(interval)
        next_intervals += new_intervals

def process(args,queue):
    interval,mass,n,expected,iter_num,solver = args
    solver = LPSolver(n,mass,interval,iter_num,solver=solver)
    value = solver.solve()
    params = solver.get_params()
    interval["value"] = value; interval["params"] = params
    new_intervals = []
    if value <= expected:
        interval["end"] = True
    else:
        new_intervals = divide_interval(interval,n,value)
    queue.put([interval,new_intervals])


def HeapMethod(iter_num,n,mass,next_intervals,max_iters=1000,max_jobs=1000,expected=1.3102,solver="CPLEX"):
    manager = mp.Manager()
    mdict = manager.dict()
    queue = manager.Queue()
    pool = mp.Pool(4+mp.cpu_count())
    start = time.time()
    st = time.time()

    while iter_num<max_iters and len(next_intervals)>0:
        jobs = []
        watcher = pool.apply_async(update,(queue,mdict))
        for interval in next_intervals:
            job = pool.apply_async(process,((interval,mass,n,expected,iter_num,solver),queue))
            jobs.append(job)
        
        for job in tqdm(jobs):
            job.get()
        queue.put([])
        watcher.get()
        results = mdict["results"]
        new_intervals = mdict["next"]
        iter_num+=1
        ed = time.time()
        total_time = ed-st
        dump_results(mdict["worst"],results,next_intervals,iter_num,n,total_time,method="heap")
        st = time.time()
        heap_dump(new_intervals,n)
        next_intervals = get_next(n,method="heap",iter_num=iter_num, max_jobs=max_jobs)
        print("iter =",iter_num,"iter worst =",mdict["worst"],"time:",total_time)

    end = time.time()
    print("Total Time:",end-start,"seconds")
    pool.close()
    pool.join()

def LayeredMethod(iter_num,n,mass,next_intervals,max_iters=100,expected=1.3102,solver="CPLEX"):
    manager = mp.Manager()
    mdict = manager.dict()
    queue = manager.Queue()
    pool = mp.Pool(mp.cpu_count()+4)
    
    while iter_num<max_iters:
        jobs = []
        st = time.time()
        watcher = pool.apply_async(update,(queue,mdict))
        for interval in next_intervals:
            job = pool.apply_async(process,((interval,mass,n,expected,iter_num,solver),queue))
            jobs.append(job)
        
        for job in tqdm(jobs):
            job.get()
        queue.put([])
        watcher.get()
        results = mdict["results"]
        next_intervals = mdict["next"]
        end = time.time()
        print("iter =",iter_num,"worst =",mdict["worst"],"# intervals next =",len(next_intervals),"time:",end-st)
        iter_num+=1
        dump_results(mdict["worst"],results,next_intervals,iter_num,n,end-st)
    
    pool.close()
    pool.join()