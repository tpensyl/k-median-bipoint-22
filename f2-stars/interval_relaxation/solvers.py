import numpy as np
import cvxpy as cp
import sympy as sp
from ortools.linear_solver import pywraplp


"""
LPSolver Class:
    Given an interval, it creates the LP instance and solves it.
"""
class LPSolver:
    def __init__(self,n,mass,interval,iter_num,solver="GLOP")->None:
        self.n = n
        self.solver = solver               # [CPLEX, MOSEK, GLOP, GUROBI]
        self.iter_num = iter_num           # Current Iteration
        self.g = interval["g"]             # The g-threshold values
        self.b = interval["b"]             # Interval range for b
        self.interval = interval           # Ex: "gammaA":[(l,u),(l,u),]
        self.mass = self.assign_mass(mass) # Computes upper and lower bounds for the probability mass, given interval
        self.constraints = []              # List containing LP constraints
        self.flag = 0
        if solver == "GLOP":
            self.prob = pywraplp.Solver.CreateSolver('GLOP')
        self.gen_basic(); self.gen_cons()  # Generate variables and constraints
        if solver != "GLOP":
            self.prob = cp.Problem(cp.Maximize(self.X),self.constraints)
        if solver == "GLOP":
            self.prob.SetSolverSpecificParametersAsString('solution_feasibility_tolerance:100000')
            # self.prob.SetSolverSpecificParametersAsString('use_dual_simplex: true')
            # self.prob.SetSolverSpecificParametersAsString('primal_feasibility_tolerance:1e-6')
            # self.prob.SetSolverSpecificParametersAsString('dual_feasibility_tolerance:1e-12')
            for constraint in self.constraints:
                self.prob.Add(constraint)
            self.prob.Maximize(self.X)

    def assign_mass(self,mass): # Function to compute the probability mass given interval
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
    
    def gen_basic(self): # Function to generate variables and basic constraints
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
        self.basic_constraints  = [self.X >= 1] + [d >= 0 for d in self.varDAB+self.varDAC+self.varDB+self.varDC]
        self.basic_constraints += [D2+(D1-D2)*(1-self.b[1]) <= 1, D2<=D1] # aD1+bD2 <= 1
        # self.basic_constraints += [self.X <= 2+4*self.b[1]*(1-self.b[0])*D2] # X <= aD1+b(3-2b)D2
        self.basic_constraints += [self.X <= 2-0.00536*self.b[0] + 2*(2-0.00536*self.b[0])*self.b[1]*(1-self.b[0])*D2] # X<=(2-eta*b)(aD1+b(3-2b)D2)
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
                # self.alg_constraints += [self.X <= 2*sum(constraint)]
                self.alg_constraints += [self.X <= (2-0.00536*self.b[0])*sum(constraint)]
            else:
                # self.alg_constraints += [self.X <= 2*cp.sum(constraint)]
                self.alg_constraints += [self.X <= (2-0.00536*self.b[0])*cp.sum(constraint)]
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
            output[variable.name()] = np.float64(variable.value) if self.solver != "GLOP" else np.float64(variable.solution_value())
        return output
        # for ind,constraint in enumerate(self.alg_constraints):
        #     if constraint.dual_value > 1e-6:
        #         print("Alg:",ind,"\tValue:",constraint.dual_value)
        #         print(*self.mass[ind][:,0])

class GradientDescent:
    def __init__(self):
        pass