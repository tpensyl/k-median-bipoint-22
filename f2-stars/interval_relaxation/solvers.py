import numpy as np
import cvxpy as cp
import sympy as sp
from ortools.linear_solver import pywraplp


class LPSolver:
    def __init__(self,n,mass,interval,iter_num,solver="GLOP")->None:
        self.n = n
        self.solver = solver
        self.iter_num = iter_num
        self.g = interval["g"]
        self.b = interval["b"]
        self.interval = interval # Ex: "gammaA":[(l,u),(l,u),]
        self.mass = self.assign_mass(mass)
        self.constraints = []
        self.flag = 0
        if solver == "GLOP":
            self.prob = pywraplp.Solver.CreateSolver('GLOP')
        self.gen_basic(); self.gen_cons()
        if solver != "GLOP":
            self.prob = cp.Problem(cp.Maximize(self.X),self.constraints)
        if solver == "GLOP":
            # self.prob.SetSolverSpecificParametersAsString('solution_feasibility_tolerance:1e-5')
            for constraint in self.constraints:
                self.prob.Add(constraint)
            self.prob.Maximize(self.X)

    def assign_mass(self,mass):
        new_mass = []
        pairs = [(sp.symbols('gammaA%d_max'%(i+2)),self.interval["gammaA"][i][1]) for i in range(self.n-1)]
        pairs += [(sp.symbols('gammaA%d_min'%(i+2)),self.interval["gammaA"][i][0]) for i in range(self.n-1)]
        pairs += [(sp.symbols("b_max"),self.interval["b"][1]),(sp.symbols("b_min"),self.interval["b"][0])]
        for alg in mass:
            new_alg = []
            for term in alg:
                if type(term[0])==int:
                    new_alg.append(term)
                else:
                    if self.iter_num == 0:
                        new_alg.append([0,1])
                        continue
                    l1,l2,u1,u2 = term[0][0].subs(pairs),term[0][1].subs(pairs),term[1][0].subs(pairs),term[1][1].subs(pairs)
                    record = [["Actual:",l1,l2,u1,u2]]
                    if list(set([l1,l2,u1,u2])) == [sp.zoo]:
                        l1 = 1
                        l2 = 0
                        u1 = 0
                        u2 = 1
                    l1,l2 = 0 if l1 in [sp.zoo,sp.nan] else np.max([0,np.min([1,l1])]), 1 if l2 in [sp.zoo,sp.nan] else np.max([0,np.min([1,l2])])
                    u1,u2 = 1 if u1 in [sp.zoo,sp.nan] else np.max([0,np.min([1,u1])]), 0 if u2 in [sp.zoo,sp.nan] else np.max([0,np.min([1,u2])])
                    l2,u2 = 1-l2,1-u2
                    record.append(["After Rounding:",l1,l2,u1,u2])
                    if len(term)>2:
                        l3,l4,u3,u4 = term[2][0].subs(pairs),term[2][1].subs(pairs),term[3][0].subs(pairs),term[3][1].subs(pairs)
                        record.append(["Extra Actual:",l3,l4,u3,u4])
                        l3,l4 = 0 if l3 in [sp.zoo,sp.nan] else np.max([0,np.min([1,l3])]), 1 if l4 in [sp.zoo,sp.nan] else np.max([0,np.min([1,l4])])
                        u3,u4 = 1 if u3 in [sp.zoo,sp.nan] else np.max([0,np.min([1,u3])]), 0 if u4 in [sp.zoo,sp.nan] else np.max([0,np.min([1,u4])])
                        l4,u4 = 1-l4,1-u4
                        record.append(["Extra After Rounding:",l3,l4,u3,u4])
                        l = np.max([np.max([l1,l2]),np.max([l3,l4])])
                        u = np.max([np.min([u1,u2]),np.min([u3,u4])])
                    else:
                        l = np.max([l1,l2])
                        u = np.min([u1,u2])
                    debug=False
                    if debug:
                        print(term)
                        print(self.interval)
                        for item in record:
                            print(*item)
                        print("l =",l,"u =",u)
                        print("-"*14)
                    new_alg.append([l,u])
                    
            new_mass.append(new_alg)
        return new_mass
    
    def gen_basic(self):
        self.X = cp.Variable(name="X") if self.solver != "GLOP" else self.prob.NumVar(0, self.prob.infinity(), 'X')
        if self.solver=="GLOP":
            self.varDAB = [self.prob.NumVar(0, self.prob.infinity(), "d1A"+str(i+1)+"B"+str(j+1)) for i in range(self.n) for j in range(self.n)]
            self.varDAC = [self.prob.NumVar(0, self.prob.infinity(), "d1A"+str(i+1)+"C"+str(j+1)) for i in range(self.n) for j in range(self.n)]
            self.varDB  = [self.prob.NumVar(0, self.prob.infinity(), "d2A"+str(i+1)+"B"+str(j+1)) for i in range(self.n) for j in range(self.n)]
            self.varDC  = [self.prob.NumVar(0, self.prob.infinity(), "d2A"+str(i+1)+"C"+str(j+1)) for i in range(self.n) for j in range(self.n)]
        else:
            self.varDAB = [cp.Variable(name="d1A"+str(i+1)+"B"+str(j+1)) for i in range(self.n) for j in range(self.n)]
            self.varDAC = [cp.Variable(name="d1A"+str(i+1)+"C"+str(j+1)) for i in range(self.n) for j in range(self.n)]
            self.varDB  = [cp.Variable(name="d2A"+str(i+1)+"B"+str(j+1)) for i in range(self.n) for j in range(self.n)]
            self.varDC  = [cp.Variable(name="d2A"+str(i+1)+"C"+str(j+1)) for i in range(self.n) for j in range(self.n)]
        D1 = cp.sum(self.varDAB+self.varDAC) if self.solver != "GLOP" else sum(self.varDAB+self.varDAC)
        D2 = cp.sum(self.varDB+self.varDC) if self.solver != "GLOP" else sum(self.varDB+self.varDC)
        self.D1=D1
        self.D2=D2
        self.basic_constraints  = [self.X>=1] + [d >= 0 for d in self.varDAB+self.varDAC+self.varDB+self.varDC]
        # self.basic_constraints += [1 >= D2*(self.b[0])+D1*(1-self.b[1])]
        self.basic_constraints += [1 >= D2+(D1-D2)*(1-self.b[1]),D2<=D1]
        # self.basic_constraints += [self.X <= self.b[1]*(3-2*self.b[0])*D2+(1-self.b[0])*D1]
        self.basic_constraints += [self.X <= 1+2*self.b[1]*(1-self.b[0])*D2]
        self.constraints += self.basic_constraints

    def gen_cons(self):
        self.alg_constraints = []
        for alg in self.mass:
            constraint = []
            for i in range(self.n):
                for j in range(self.n):
                    d1 = self.varDAB[self.n*i+j] # LP variables 
                    d2 = self.varDB[self.n*i+j] # LP variables : CVXPY variables
                    p1 = alg[i]; p2 = alg[self.n+j]
                    p3_min = np.min([alg[self.n+w][0] for w in range(i+1)])
                    if i==0:
                        g=1
                    elif j<=i:
                        g = 1/self.g[i-1]
                    elif j>i:
                        g = 1+(1/self.g[i-1]-1)*(1-p3_min)
                    # g = 1 if i==0 else 1/self.g[i-1]
                    constraint.append(p2[1]*d2+(1-p2[0])*d1+(1-p2[0])*(1-p1[0])*g*(d1+d2))
                    d1 = self.varDAC[self.n*i+j]
                    d2 = self.varDC[self.n*i+j]
                    p1 = alg[i]; p2 = alg[2*self.n+j]
                    p3_min = np.min([alg[self.n+w][0] for w in range(i+1)])
                    if i==self.n-1:
                        g=1
                    elif i==0:
                        g = self.g[i]
                    else:
                        g = self.g[i]+(1-self.g[i])*(1-p3_min)
                    # g = 1 if i==self.n-1 else self.g[i]
                    constraint.append(p2[1]*d2+(1-p2[0])*d1+(1-p2[0])*(1-p1[0])*g*(d1+d2))
            if self.solver == "GLOP":
                self.alg_constraints += [self.X <= sum(constraint)]
            else:
                self.alg_constraints += [self.X <= cp.sum(constraint)]
        self.constraints += self.alg_constraints

    def solve(self):
        if self.solver == "GLOP":
            self.prob.Solve()
        else:
            self.prob.solve(solver=self.solver)
        '''self.prob.value = inf (unbounded) or -inf (infeasible) or Finite Value'''
        value = self.prob.Objective().Value() if self.solver == "GLOP" else self.prob.value
        return value
        
    def get_params(self):
        value = self.prob.Objective().Value() if self.solver == "GLOP" else self.prob.value
        if value in [np.inf,None]:
            return {"status":"unbounded"}
        output = {}
        for variable in self.prob.variables():
            output[variable.name()] = np.float(variable.value) if self.solver != "GLOP" else np.float(variable.solution_value())
        return output
        # for ind,constraint in enumerate(self.alg_constraints):
        #     if constraint.dual_value > 1e-6:
        #         print("Alg:",ind,"\tValue:",constraint.dual_value)
        #         print(*self.mass[ind][:,0])

class GradientDescent:
    def __init__(self):
        pass


# def assign_mass(self,mass):
    #     new_mass = []
    #     pairs = [(sp.symbols('gammaA%d_max'%(i+2)),self.interval["gammaA"][i][1]) for i in range(self.n-1)]
    #     pairs += [(sp.symbols('gammaA%d_min'%(i+2)),self.interval["gammaA"][i][0]) for i in range(self.n-1)]
    #     pairs += [(sp.symbols("b_max"),self.interval["b"][1]),(sp.symbols("b_min"),self.interval["b"][0])]
    #     for alg in mass:
    #         new_alg = []
    #         for term in alg:
    #             if type(term[0])==int:
    #                 new_alg.append(term)
    #             else:
    #                 ln,ld,un,ud = term[0][0].subs(pairs),term[0][1].subs(pairs),term[1][0].subs(pairs),term[1][1].subs(pairs)
    #                 if len(term[0])>2:
    #                     ln2,ld2,un2,ud2 = term[0][2].subs(pairs),term[0][3].subs(pairs),term[1][2].subs(pairs),term[1][3].subs(pairs)
    #                 if np.inf in [ln,ld] or -np.inf in [ln,ld]:
    #                     l = self.handle_inf(term[0][0],term[0][1],pairs,"l")
    #                 else:
    #                     l = 0 if ln==0 else (ln*np.inf if ld==0 else ln/ld)
    #                 if np.inf in [un,ud] or -np.inf in [un,ud]:
    #                     u = self.handle_inf(term[1][0],term[1][1],pairs,"u")
    #                 else:
    #                     u = 0 if un==0 else (un*np.inf if ud==0 else un/ud)
    #                 if len(term[0])>2:
    #                     if np.inf in [ln2,ld2] or -np.inf in [ln2,ld2]:
    #                         l2 = self.handle_inf(term[0][2],term[0][3],pairs,"l")
    #                     else:
    #                         l2 = 0 if ln2==0 else (ln2*np.inf if ld2==0 else ln2/ld2)
    #                     if np.inf in [un2,ud2] or -np.inf in [un2,ud2]:
    #                         u2 = self.handle_inf(term[1][2],term[1][3],pairs,"u")
    #                     else:
    #                         u2 = 0 if un2==0 else (un2*np.inf if ud2==0 else un2/ud2)
    #                     l = np.max([l,l2,0])
    #                     u = np.max([u,u2,0])
    #                 if [np.min([1,np.max([0,l])]),np.min([1,np.max([0,u])])]==[1,0]:
    #                     print(term)
    #                     print(self.interval)
    #                     print(ln,ld,un,ud)
    #                     print(l,u)
    #                 l,u = np.min([1,np.max([0,l])]),np.min([1,np.max([0,u])])
    #                 new_alg.append([l,u])
                    
    #         new_mass.append(new_alg)
    #     return new_mass

    # def handle_inf(self,term,pairs,flag="l"):
    #     inds = [i+2 for i in range(len(self.interval["gammaA"])) if self.interval["gammaA"][i][1]==np.inf]
    #     num,den = sp.fraction(term)
    #     args = term.free_symbols
    #     print("args:",args)
    #     w1 = [[sp.symbols("gammaA%d_min"%i),sp.symbols("gammaA%d_max"%i)] for i in inds if (sp.symbols("gammaA%d_max"%i) in args)]
    #     print("w1:",w1)
    #     w2 = [i[::-1] for i in w1]
    #     w1p = [i[1] for i in w1]
    #     w2p = [i[0] for i in w1]
    #     num_val = num.subs(pairs)
    #     den_val = den.subs(pairs)
    #     num_pos,num_neg = num.coeff(1),num.coeff(-1)
    #     den_pos,den_neg = den.coeff(1),den.coeff(-1)
    #     if flag=="l":
    #         if self.iter_num==0:
    #             return 0
    #         # if den_val==0:
    #         #     return num_val*np.inf
    #         print(term, num_pos,num_neg,den_pos,den_neg)
    #         print(num_pos.subs(w1)/sp.prod(w1p), ";",num_pos.subs(w1),";",sp.prod(w1p))
    #         num_pos,num_neg = (num_pos.subs(w1)/sp.prod(w1p)).expand(),num_neg.subs(w2)/(sp.prod(w2p)).expand()
    #         ln = num_pos.subs(pairs)-num_neg.subs(pairs)
    #         den_pos,den_neg = (den_pos.subs(w2)/sp.prod(w2p)).expand(),den_neg.subs(w1)/(sp.prod(w1p)).expand()
    #         ld = den_pos.subs(pairs)-den_neg.subs(pairs)
    #         l = 0 if ln==0 else (ln*np.inf if ld==0 else ln/ld)
    #         return l
    #     elif flag=="u":
    #         if self.iter_num==0:
    #             return 1
    #         # if den_val==0:
    #         #     return num_val*np.inf
    #         print(term, num_pos,num_neg,den_pos,den_neg)
    #         print(num_pos.subs(w1)/sp.prod(w1p), ";",num_pos.subs(w1),";",sp.prod(w1p))
    #         num_pos,num_neg = (num_pos.subs(w2)/sp.prod(w2p)).expand(),num_neg.subs(w1)/(sp.prod(w1p)).expand()
    #         un = num_pos.subs(pairs)-num_neg.subs(pairs)
    #         den_pos,den_neg = (den_pos.subs(w1)/sp.prod(w1p)).expand(),den_neg.subs(w2)/(sp.prod(w2p)).expand()
    #         ud = den_pos.subs(pairs)-den_neg.subs(pairs)
    #         u = 1 if (un==0 and ud==0) else (un*np.inf if ud==0 else un/ud)
    #         return u
