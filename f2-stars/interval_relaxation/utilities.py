import sympy as sp
import json,heapq
import numpy as np

# BASE = "output/"
BASE = "../../../../../../ssd2/kishen/kmedian/output/"

# files  = ["%.4f"%i for i in  np.linspace(1.304,1.309,6)]+["%.4f"%i for i in  np.linspace(1.3100,1.3109,10)]
# files += ["%.4f"%i for i in  np.linspace(1.311,1.319,9)]+["1.32","1.33"]
files  = ["%.4f"%i for i in  np.linspace(2.6060,2.6095,8)]
files += ["%.4f"%i for i in  np.linspace(2.610,2.619,10)]+["%.4f"%i for i in  np.linspace(2.62,2.7,9)]
files += ["2.8","2.9","3"]
files = files[::-1]
files_val = [float(i) for i in files]

def replace_inf(l):
	final = []
	for val in l:
		if val[1]=="inf":
			final.append([val[0],np.inf])
		else:
			final.append(val)
	return final

def find_bound(expr,upper,lower,flag="upper",flag1=0):
    expr = expr.factor()
    num,den = sp.fraction(expr)
    if num.coeff(sp.symbols("b"))==-1 and flag1==0:
        num,den = -num,-den
    if num.coeff(sp.symbols("b"))==1 and flag1==1:
        num,den = -num,-den
    num,den = num.expand(),den.expand()
    num_pos,num_neg = num.coeff(1),num.coeff(-1)
    den_pos,den_neg = den.coeff(1),den.coeff(-1)
    num_pos_args = num_pos.args if (len(num_pos.args) > 0 and type(num_pos) not in [sp.Min,sp.Max]) else [num_pos]
    num_neg_args = num_neg.args if (len(num_neg.args) > 0 and type(num_neg) not in [sp.Min,sp.Max]) else [num_neg]
    den_pos_args = den_pos.args if (len(den_pos.args) > 0 and type(den_pos) not in [sp.Min,sp.Max]) else [den_pos]
    den_neg_args = den_neg.args if (len(den_neg.args) > 0 and type(den_neg) not in [sp.Min,sp.Max]) else [den_neg]
    if flag=="upper":
        numu = 0
        denl = 0
        for term in num_pos_args:
            if type(term)==sp.Min:
                out = []
                for arg in term.args:
                    out.append(find_bound(arg,upper,lower,"upper"))
                numu += sp.Min(*out)
            elif type(term)==sp.Max:
                out = []
                for arg in term.args:
                    out.append(find_bound(arg,upper,lower,"upper"))
                numu += sp.Max(*out)
            else:
                numu += term.subs([(sym,upper[str(sym)]) for sym in term.free_symbols])
        for term in num_neg_args:
            if type(term)==sp.Min:
                out = []
                for arg in term.args:
                    out.append(find_bound(arg,upper,lower,"lower"))
                numu -= sp.Min(*out)
            elif type(term)==sp.Max:
                out = []
                for arg in term.args:
                    out.append(find_bound(arg,upper,lower,"lower"))
                numu -= sp.Max(*out)
            else:
                numu -= term.subs([(sym,lower[str(sym)]) for sym in term.free_symbols])
        for term in den_pos_args:
            if type(term)==sp.Min:
                out = []
                for arg in term.args:
                    out.append(find_bound(arg,upper,lower,"lower"))
                denl += sp.Min(*out)
            elif type(term)==sp.Max:
                out = []
                for arg in term.args:
                    out.append(find_bound(arg,upper,lower,"lower"))
                denl += sp.Max(*out)
            else:
                denl += term.subs([(sym,lower[str(sym)]) for sym in term.free_symbols])
        for term in den_neg_args:
            if type(term)==sp.Min:
                out = []
                for arg in term.args:
                    out.append(find_bound(arg,upper,lower,"upper"))
                denl -= sp.Min(*out)
            elif type(term)==sp.Max:
                out = []
                for arg in term.args:
                    out.append(find_bound(arg,upper,lower,"upper"))
                denl -= sp.Max(*out)
            else:
                denl -= term.subs([(sym,upper[str(sym)]) for sym in term.free_symbols])
        return numu/denl
    elif flag=="lower":
        numl = 0
        denu = 0
        for term in num_pos_args:
            if type(term)==sp.Min:
                out = []
                for arg in term.args:
                    out.append(find_bound(arg,upper,lower,"lower"))
                numl += sp.Min(*out)
            elif type(term)==sp.Max:
                out = []
                for arg in term.args:
                    out.append(find_bound(arg,upper,lower,"lower"))
                numl += sp.Max(*out)
            else:
                numl += term.subs([(sym,lower[str(sym)]) for sym in term.free_symbols])
        for term in num_neg_args:
            if type(term)==sp.Min:
                out = []
                for arg in term.args:
                    out.append(find_bound(arg,upper,lower,"upper"))
                numl -= sp.Min(*out)
            elif type(term)==sp.Max:
                out = []
                for arg in term.args:
                    out.append(find_bound(arg,upper,lower,"upper"))
                numl -= sp.Max(*out)
            else:
                numl -= term.subs([(sym,upper[str(sym)]) for sym in term.free_symbols])
        for term in den_pos_args:
            if type(term)==sp.Min:
                out = []
                for arg in term.args:
                    out.append(find_bound(arg,upper,lower,"upper"))
                denu += sp.Min(*out)
            elif type(term)==sp.Max:
                out = []
                for arg in term.args:
                    out.append(find_bound(arg,upper,lower,"upper"))
                denu += sp.Max(*out)
            else:
                denu += term.subs([(sym,upper[str(sym)]) for sym in term.free_symbols])
        for term in den_neg_args:
            if type(term)==sp.Min:
                out = []
                for arg in term.args:
                    out.append(find_bound(arg,upper,lower,"lower"))
                denu -= sp.Min(*out)
            elif type(term)==sp.Max:
                out = []
                for arg in term.args:
                    out.append(find_bound(arg,upper,lower,"lower"))
                denu -= sp.Max(*out)
            else:
                denu -= term.subs([(sym,lower[str(sym)]) for sym in term.free_symbols])
        return numl/denu

def simplify_mass(mass,n):
    upper = {'gammaA%d'%i: sp.symbols('gammaA%d_max'%i) for i in range(2,n+1)}
    lower = {'gammaA%d'%i: sp.symbols('gammaA%d_min'%i) for i in range(2,n+1)}
    upper["b"]=sp.symbols("b_max")
    lower["b"]=sp.symbols("b_min")
    upper["gammaC%d"%n] = sp.Min(1,upper["gammaA%d"%n])
    lower["gammaC%d"%n] = sp.Min(1,lower["gammaA%d"%n])
    upper["gammaC%dp"%n] = sp.Min(1,upper["gammaA%d"%n])
    lower["gammaC%dp"%n] = sp.Min(1,lower["gammaA%d"%n])
    for i in range(n-1,1,-1):
        upper['gammaC%d'%i] = sp.Min(upper['gammaA%d'%i],1-sp.Add(*[lower['gammaC%d'%j] for j in range(i+1,n+1)]))
        lower['gammaC%d'%i] = sp.Min(lower['gammaA%d'%i],1-sp.Add(*[upper['gammaC%d'%j] for j in range(i+1,n+1)]))
        upper['gammaC%dp'%i] = sp.Min(1,sp.Add(*[upper['gammaA%d'%j] for j in range(i,n+1)]))
        lower['gammaC%dp'%i] = sp.Min(1,sp.Add(*[lower['gammaA%d'%j] for j in range(i,n+1)]))

    new_mass = []
    for alg in mass:
        new_alg = []
        for exp in alg:
            if type(exp)==int:
                new_alg.append([exp,exp])
                continue
            # print(exp)
            expr = sp.sympify(exp)
            expr = expr.subs([(sp.Add(*[sp.symbols('gammaC%d'%j) for j in range(i,n+1)]),sp.symbols("gammaC%dp"%i)) for i in range(2,n+1)])
            # print(expr)
            if exp[:5]=="Max(1":
                term1,term2 = expr.args
                new_alg.append([
                    [find_bound(term1,upper,lower,"lower"),find_bound((1-term1).simplify(),upper,lower,"upper",1)],
                    [find_bound(term1,upper,lower,"upper"),find_bound((1-term1).simplify(),upper,lower,"lower",1)],
                    [find_bound(term2,upper,lower,"lower",1),find_bound((1-term2).simplify(),upper,lower,"upper",0)],
                    [find_bound(term2,upper,lower,"upper",1),find_bound((1-term2).simplify(),upper,lower,"lower",0)]
                ])
            else:
                flag = 1 if exp[:9] == "1 - b/Max" else 0
                new_alg.append([
                    [find_bound(expr,upper,lower,"lower",flag),find_bound((1-expr).simplify(),upper,lower,"upper",1-flag)],
                    [find_bound(expr,upper,lower,"upper",flag),find_bound((1-expr).simplify(),upper,lower,"lower",1-flag)]
                ])
        #     print(new_alg[-1])
        #     print()
        # print("-"*14)
        new_mass.append(new_alg)
    return new_mass

def divide_interval(interval,n,value):
    intervals = []
    num = n # b + n-1 gammaA (+ n-1 gammaC)
    curr = 0
    while curr< 1<<num:
        bin_curr = bin(curr)[2:][::-1]
        bin_curr = [int(i) for i in bin_curr] + [0]*(num-len(bin_curr))
        bs = []
        gammaAs = []
        # gammaCs = []
        flag = 0
        for ind,val in enumerate(bin_curr):
            if ind==0:
                bs = sorted([interval["b"][val],np.sum(interval["b"])/2])
            elif 1<=ind and ind<n: # ind -> [1,n-1], we need [0,n-2], hence ind-1
                if val==0 and interval["gammaA"][ind-1] == [2,np.inf]:
                    flag=1
                gammaAs.append(sorted([interval["gammaA"][ind-1][val],2 if (interval["gammaA"][ind-1][1] == np.inf) else np.sum(interval["gammaA"][ind-1])/2]))
            # else: # ind -> [n,2*n-2], we need [0,n-2], hence ind-n
            #     gammaCs.append(sorted([interval["gammaC"][ind-n][val],np.sum(interval["gammaC"][ind-n])/2]))
        if not flag:
            intervals.append({"g":interval["g"],"b":bs,"gammaA":gammaAs,"end":False,"value":value,"params":[]})
        curr+=1
    return intervals

def init_files(n):
    for file_name in files:
        # if file_name=="1.30" or file_name=="1.310":
        #     with open(BASE+"g"+str(n-1)+"/heap/heap_"+file_name+".json","w") as f:
        #         json.dump({"length":0,"worst":0,"heap":[]},f,indent=4)
        # else:
        with open(BASE+"g"+str(n-1)+"/heap/heap_"+file_name+".json","w") as f:
            json.dump({"length":0,"intervals":[]},f,indent=4)


def get_next(n,method,iter_num,max_jobs=1000):
    next_intervals = []
    if method=="layer":
        with open(BASE + "g"+str(n-1)+"/"+method+"/next_intervals"+".json","r") as f:
            items = json.load(f)
            next_intervals = items["next"]
    elif method=="heap":
        rem = max_jobs
        for file_name in files:
            content = []
            # if file_name=="1.30" or file_name=="1.310":
            #     with open(BASE + "g"+str(n-1)+"/" +method+ "/heap_"+file_name+".json","r") as f:
            #         content = json.load(f) # {"length","worst","heap"}
            #         heap = content["heap"]
            #         more = [json.loads(heapq.heappop(heap)[1]) for num in range(min(content["length"],max_jobs))]
            #         next_intervals+=more
            #         rem-=len(more)
            #     with open(BASE + "g"+str(n-1)+"/" +method+ "/heap_"+file_name+".json","w") as f:
            #         json.dump({"length":len(heap),"worst":(0 if len(heap)==0 else -heap[0][0]),"heap":heap},f,indent=4)
            # else:
            with open(BASE + "g"+str(n-1)+"/"+method+"/heap_"+file_name+".json","r") as f:
                content = json.load(f) # {"length","intervals"}
                more = content["intervals"][:min(content["length"],rem)]
                content["intervals"] = content["intervals"][min(content["length"],rem):]
                content["length"] = len(content["intervals"])
                next_intervals+=more
                rem-=len(more)
            with open(BASE + "g"+str(n-1)+"/"+method+"/heap_"+file_name+".json","w") as f:
                json.dump(content,f,indent=4)
            if rem==0:
                break
        with open(BASE + "g"+str(n-1)+"/"+method+"/current"+".json","w") as f:
            json.dump({"Number of Intervals":len(next_intervals),"intervals":next_intervals,"iter":iter_num},f,indent=4)
       
    return next_intervals

def heap_dump(new_intervals,n):
    intervals_map = {name:[] for name in files}
    for inter in new_intervals:
        w = inter["value"]
        for ind,item in enumerate(files_val):
            if w>=item:
                intervals_map[files[ind]].append(inter)
                break
        else:
            print("Something's Wrong")
            exit(1)
    for file_name in files:
        # if file_name=="1.30" or file_name=="1.310":
        #     with open(BASE + "g"+str(n-1)+"/heap/heap_"+file_name+".json","r") as f:
        #         content = json.load(f) # {"length","worst","heap"}
        #     with open(BASE + "g"+str(n-1)+"/heap/heap_"+file_name+".json","w") as f:
        #         for interval in intervals_map[file_name]:
        #             heapq.heappush(content["heap"],[-interval["value"],json.dumps(interval)])
        #         content["length"] += len(intervals_map[file_name])
        #         content["worst"] = (0 if content["length"]==0 else -content["heap"][0][0])
        #         json.dump(content,f,indent=4)
        # else:
        if len(intervals_map[file_name]) >0:
            with open(BASE + "g"+str(n-1)+"/heap/heap_"+file_name+".json","r") as f:
                content = json.load(f) # {"length","intervals"}
            with open(BASE + "g"+str(n-1)+"/heap/heap_"+file_name+".json","w") as f:
                content["intervals"] += intervals_map[file_name]
                content["length"] += len(intervals_map[file_name])
                json.dump(content,f,indent=4)

def dump_results(worst,results,next_intervals,iter_num,n,exec_time,method="layer"):
    done_intervals = [inter for inter in results if inter['end']]
    not_done_intervals = [inter for inter in results if not inter['end']]
    with open(BASE + "g"+str(n-1)+"/"+method+"/iter"+str(iter_num)+".json","w") as f:
        json.dump({"iter_num":iter_num,"Number of intervals":len(results),"time":exec_time,"worst":worst,"Number done:":len(done_intervals),"Number not done:":len(not_done_intervals),"done results":done_intervals,"not done results":not_done_intervals},f,indent=4)
    if method == "layer":
        with open(BASE + "g"+str(n-1)+"/"+method+"/next_intervals"+".json","w") as f:
            json.dump({"iter_num":iter_num,"length":len(next_intervals),"next":next_intervals},f,indent=4)