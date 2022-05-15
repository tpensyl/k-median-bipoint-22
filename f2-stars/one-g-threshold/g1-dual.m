(* ::Package:: *)

(* ::Title:: *)
(*F2-Stars*)


SetOptions[EvaluationNotebook[],CellContext->Notebook, PrintPrecision->8]
SetOptions[Plot3D, AxesLabel->Automatic,
	PlotStyle->Opacity[.7], ClippingStyle->None,
	BoundaryStyle -> Directive[Black, Thick]];
SetOptions[ListPlot3D, AxesLabel->Automatic,
	PlotStyle->Opacity[.7], ClippingStyle->None,
	BoundaryStyle -> Directive[Black, Thick]];


(* ::Subsection::Closed:: *)
(*Description:*)


(* ::Text:: *)
(*i1, i2: Closest facilities in F1,F2 for client j.*)
(*Form F2 stars, connect each i \[Element] F1 to its closest i' \[Element] F2.*)
(*Let X be the set of facilities in F2 with at least one leaf. Add arbitrary facilities to X, if necessary, such that |F1|=|X|.*)
(*Let Y = F2 \[Dash] X.*)
(**)
(*Let \[Sigma]_X(i), \[Sigma]_Y(i) be the nearest facilities to i in X and Y, respectively.*)
(*For each i \[Element] F1, let *)
(*	g_i = d(i, X)/d(i, Y) = d(i,\[Sigma]_X(i)) / d(i,\[Sigma]_Y(i)).*)
(**)
(*Fix g, and let *)
(*	F1A \[LeftArrow] {i \[Element] F1 |  g_i < g}*)
(*\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]	F1B \[LeftArrow] {i \[Element] F1 |  g_i >= g}*)
(*	F2A \[LeftArrow] \[Sigma]_X(F1A)*)
(*	F2A \[LeftArrow] \[Sigma]_X(F1B)\[Dash] F2A*)
(*\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]	Arbitrarily assign rest of X such that |F1A|=|F2A|, |F1B| = |F2B|.*)
(*\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]	F2C = \[Sigma]_Y(F1B)*)
(*	F2D = Y-F2C*)
(*Let, *)
(*	\[Gamma]_B = |F2B|/|Y| = |F1B|/|Y|*)
(*	\[Gamma]_C = |F2C|/|Y|  <= \[Gamma]_B*)
(*	Also, 0 <= \[Gamma]_C <= 1*)


(* ::Subsection::Closed:: *)
(*Setting up the NLP:*)


(* ::Subsubsection:: *)
(*Probability Mass*)


(* ::Text:: *)
(*Let A(p1a,p2a,p1b,p2b,p2c,p2d) give proportions.*)
(*massSafe: p1B+p2B = 1; Either shift mass from F2C to F2D or F2D to F2C*)
(*massbgamma0: Shifting mass from F2C+F2D to F1B+F2B*)
(*	i)  b - \[Gamma]B<=0: Sufficient mass not available, hence p2D=p2C=0. Then, distribute mass between F1B and F2B.*)
(*	ii) b - \[Gamma]B>=0: Sufficient mass available for p1B=p2B=1. Then, shift remaining mass either from F2C to F2D or F2D to F2C.*)
(*massbgamma1: Shifting mass from F1B+F2B to F2C+F2D*)
(*	i)  b + \[Gamma]B<=1: Sufficient mass not available, hence p1B=p2B=0. Then, distribute mass between F2C and F2D.*)
(*	ii) b + \[Gamma]B>=1: Sufficient mass available for p2D=p2C=1. Then, shift remaining mass either from F1B to F2B or F2B to F1B.*)
(*massOnlyC: Shifting mass from F1B+F2B+F2D to only F2C. Always possible to make p2C=1 as per definition.*)
(*	i)  \[Gamma]_C>=b: Less mass remaining, either p1B gets it or p2B gets it.*)
(*	ii) \[Gamma]_C<=b: *)
(*		a) b <= \[Gamma]_B+\[Gamma]_C: Available mass can be distributed between F1B and F2B.*)
(*		b) b >= \[Gamma]_B+\[Gamma]_C: Additional mass available such that p1B=p2B=1. Give remaining mass to p2D (Always possible).*)


(* Commented ones are either invalid inputs, or were found to be redundant *)
massSafe={{1,0,1,0,x,y},{0,1,1,0,x,y},{1,0,0,1,x,y},{0,1,0,1,x,y},
          {1,0,1,0,z,w},{0,1,1,0,z,w},{1,0,0,1,z,w},{0,1,0,1,z,w}}/.{
	x->Min[1,b/gammaC],y->Max[0,(b-gammaC)/(1-gammaC)],z->Max[0,1-(1-b)/gammaC],w->Min[1,b/(1-gammaC)]};
massbgamma0={{1,0,1,x,y1,z1},{1,0,x,1,y1,z1},{0,1,1,x,y1,z1},{0,1,x,1,y1,z1}
	{1,0,1,x,y2,z2},{1,0,x,1,y2,z2},{0,1,1,x,y2,z2},{0,1,x,1,y2,z2}}/.{
	x->Min[1,b/gammaB], y1->Max[0,1-(1-b+gammaB)/gammaC],z1->Max[Min[1,(b-gammaB)/(1-gammaC)],0],
	y2->Max[Min[1,(b-gammaB)/gammaC],0],z2->Max[0,(b-gammaB-gammaC)/(1-gammaC)]};
massbgamma1={{1,0,0,x,y1,z1},{1,0,x,0,y1,z1},{0,1,0,x,y1,z1},{0,1,x,0,y1,z1},
	{1,0,0,x,y2,z2},{1,0,x,0,y2,z2},{0,1,0,x,y2,z2},{0,1,x,0,y2,z2}}/.{
	x->Max[0,1-(1-b)/gammaB], y1->Min[Max[0,1-(1-b-gammaB)/gammaC],1],z1->Min[1,(b+gammaB)/(1-gammaC)],
	y2->Min[1,(b+gammaB)/gammaC],z2->Min[Max[0,(b+gammaB-gammaC)/(1-gammaC)],1]};
massOnlyC={{1,0,x,y,1,z},{0,1,x,y,1,z},{1,0,y,x,1,z},{0,1,y,x,1,z}}/.{
	x->Max[Min[1,(b-gammaC)/gammaB],0], y->Min[Max[0,1-(gammaC-b)/gammaB],1],z->Max[0,(b-gammaB-gammaC)/(1-gammaC)]};
massCombos={{0,1,0,1,b,b} (*11: combine 2,5*)
			,{1,0,1,0,b,b} (*29 combine 1,3*)
			,{0,1,1,0,b,b} (*30: flatten 4*)
            ,{0,1,1,x,y,y}/.{x->Min[1,b/gammaB],y->Max[0,b-gammaB]}(*31: flatten 7*)
            ,{1,0,1,x,y,y}/.{x->Min[1,b/gammaB],y->Max[0,b-gammaB]}(*32: flatten 6*)
			(*{0,1,0,y,x,x}/.{x->Min[1,b+gammaB],y->Max[0,1-(1-b)/gammaB]}*)(*flatten 9, but this is cheating *)
			,{1,0,1,x,mu*x,mu*x}/.{x->b/(gammaB+mu)}/.{mu->1/2(1+1/g)} (* 33: further flatten 29 and 32 *)
			,{0,1,1,x,y,y}/.{x->1-g*mu,y->1-mu}/.{mu->(1-b+gammaB)/(1+g*gammaB)} (* 34 futher flatten 30 and 31 *)
};


CheckMass[mass_]:=FullSimplify[{gA,gA,gammaB,gammaB,gammaC,1-gammaC}.(mass-{a,b,a,b,b,b})/.{a->1-b},
	{0<b<1,0<gammaB<1}]
CheckMass/@massCombos (* check if the mass balances; it should equal zero *)


(* ::Subsubsection::Closed:: *)
(*Client Costs*)


(* ::Text:: *)
(*Client cost is bounded by*)
(*	p[i2]*d2 + p[i2']*d1 + p[i2'i1']*d(i1,i3)*)
(*where i3 is either \[Sigma]_X(i1) or \[Sigma]_Y(i1). The bound used for d(i1,i3) varies by client type, but is always some constant times (d1+d2).*)


varD1={d1aa,d1ab,d1ac,d1ad,d1ba,d1bb,d1bc,d1bd};
varD2={d2aa,d2ab,d2ac,d2ad,d2ba,d2bb,d2bc,d2bd};

Cf1[d1_,d2_,p1_,p2_,g_]:=p2*d2+(1-p2)*d1+(1-p2)(1-p1)*g*(d1+d2)
(* If \[Sigma]_X(i1)!=i2, then we may try connecting to both before falling back on \[Sigma]_Y(i1) *)
Cf1b[d1_,d2_,p1_,p2_,p3_,g1_,g2_]:=p2*d2+(1-p2)*d1+(1-p2)(1-p1)*(p3*g1+(1-p3)(g2))*(d1+d2)

cost[p1a_,p2a_,p1b_,p2b_,p2c_,p2d_] := Total@{
	Cf1[d1aa,d2aa,p1a,p2a,1],         (*Clients in JAA*)
	Cf1[d1ab,d2ab,p1a,p2b,1],         (*Clients in JAB*)
	Cf1[d1ac,d2ac,p1a,p2c,g],         (*Clients in JAC*)
	Cf1[d1ad,d2ad,p1a,p2d,g],         (*Clients in JAD*)
	Cf1[d1ba,d2ba,p1b,p2a,1/g],       (*Clients in JBA*)
	Cf1[d1bb,d2bb,p1b,p2b,1/g],       (*Clients in JBB*)
	Cf1[d1bc,d2bc,p1b,p2c,1],         (*Clients in JBC*)
	Cf1[d1bd,d2bd,p1b,p2d,1]          (*Clients in JBD*)
}
costLiSven = b*(3-2b)Total[varD2]+(1-b)*Total[varD1];


(* ::Subsubsection:: *)
(*Variables and Constraints:*)


allMass=Join[massSafe,massbgamma0,massbgamma1,massOnlyC,massCombos];
Length@allMass
algs=cost@@#&/@allMass;
algsWithMass=Table[{algCost->cost@@allMass[[i]],algMass->Style[allMass[[i]],PrintPrecision->2],algIndex->i},{i,1,Length[allMass]}];
constrAlg = Z<=#&/@algs;

varNonLin={b,g,gammaB,gammaC};
vars=Union[varD1,varD2,varNonLin,{Z}];

constrD1D2=MapThread[#1<=#2&,{varD2,varD1}];
constrD1D2g=MapThread[#1+g(#1+#2)>=#2+(#1+#2)&,{{d1ac, d1ad},{d2ac, d2ad}}];
constrBasic = Join[{Z>=0,0<=b<=1,0<=gammaB,0<=gammaC<=1,gammaC<=gammaB},#>=0&/@Union[varD1,varD2],{Total[varD1]*(1-b)+Total[varD2]*b==1}];
constrAlgLiSven = Z<=costLiSven;


(* ::Subsection::Closed:: *)
(*Utility Methods*)


(* Show tight algorithms *)
EvaluateAlgs[params_,algIset_:;;]:=(
		{algCost, Style[algMass,PrintPrecision->2], algIndex}/.#&/@algsWithMass[[algIset]]
	)/.params
EvaluateAlgsByCost[params_,algIset_:;;]:=Grid[SortBy[EvaluateAlgs[params,algIset],First]~Prepend~{"Alg Cost ", "Alg Mass","Alg Index"},Alignment->Left]
EvaluateAlgsByMass[params_,algIset_:;;]:=Grid[SortBy[EvaluateAlgs[params,algIset],#[[2]]&]~Prepend~{"Alg Cost ", "Alg Mass","Alg Index"},Alignment->Left]
EvaluateAlgsByIndex[params_,algIset_:;;]:=Grid[SortBy[EvaluateAlgs[params,algIset],#[[3]]&]~Prepend~{"Alg Cost ", "Alg Mass","Alg Index"},Alignment->Left]


(* type checking: needed for multiple optional arguments and generally helpful for debugging *)
IndexQ[i_]:=(i==All || i==(1;;All) || And@@IntegerQ/@i) (* allow passing ;; or All for index subset *)
EquationQ[eq_]:=Not@FreeQ[eq,(Equal|LessEqual|Less|Greater|GreaterEqual)]||eq (* contains one of =,<,<=,>,>=, or trivially true *)

(* We will fix the value of g, and let the adversary set the mass variable gamma *)
SolveNLP[g1hat_,iter_,algI_,constrExtra_:{}]:=
	NMaximize[{Z, constrAlg[[algI]], constrBasic, constrAlgLiSven, g==g1hat, constrExtra,
		.6 <= b <= .7, .1 <= gammaB, .1 <= gammaC <= .9 (* manual hints. some problems with gamma12->0, but also maybe valid *)
	}, vars~Union~{g}, MaxIterations->iter][[2]]
SolveNLP[g1hat_,iter_,algI_:;;]:=SolveNLP[g1hat,iter,algI,{}]

(* If we fix non-linear variables, remaining system is linear and very fast/accurate *)
SolveLP[nonLinParams_,algI:_?IndexQ:All,constrExtra:{___?EquationQ}:{}]:=
	NMaximize[{Z, constrAlg[[algI]], constrBasic, constrAlgLiSven, constrExtra}/.nonLinParams,
		Union[varD1,varD2,{Z}]][[2]]~Join~nonLinParams;
SolveLPatSol[fullSol_,algI:_?IndexQ:All,constrExtra:{___?EquationQ}:{}]:=SolveLP[ExtractNonLin[fullSol], algI,constrExtra]
ExtractNonLin[sol_]:=Select[sol,MemberQ[varNonLin,#[[1]]]&]

createVar[terms__]:=ToExpression@StringJoin@@ToString/@List[terms]


(* ::Subsection::Closed:: *)
(*Solving the NLP*)


algsI7={8,22,28,29,30,31,32}; (* re-add some algo. Graphically, (with some heuristic), 5(8 now) seems to be the 'most complete' algo to add.*)
algsI8={4,8,22,28,29,30,31,32};
algsI7b={4,8,22,29,30,31,32}; (* our in-between wasn't actually special here *)
algsI6b={4,8,22,30,31,33};
algsI5={4,8,22,33,34};
algsI=algsI5
ghat=0.6586
solNLP=SolveNLP[ghat,300,algsI]


sol=SolveLPatSol[solNLP,algsI5(*, constrD1D2~Union~constrD1D2g*)];
Column@{Z/.sol,Chop[sol, .0001],EvaluateAlgsByMass[sol,algsI5]}


(* ::Subsection:: *)
(*Result*)


(* ::Text:: *)
(*By setting g=.6586, we get approximation factor 1.31019*)
(**)
(*This file uses a minimal set of 5 algos to achieve this. *)
(**)
(*I think this NLP could be simplified by padding such that |F2C|=min{|F2B|,|Y|}, to eliminate need for gammaC variable.*)


(* ::Section:: *)
(*Dual*)


Protect[u];
ToDual[algs_,varsD1_,varsD2_]:=Module[{varsU},
varsU=Table[u[i],{i,1,Length@algs}];
{{alpha, Join[
	#<=(1-b)alpha&/@( varsU.Table[Coefficient[alg,var],{alg,algs},{var,varsD1}] ),
	#<=b*alpha&/@( varsU.Table[Coefficient[alg,var],{alg,algs},{var,varsD2}] ),
	{Total[varsU]>=1}, #>=0&/@varsU]
}, varsU~Append~alpha}
]
SolveDualLP[nonLinParams_,algI:_?IndexQ:All,constrExtra:{___?EquationQ}:{}]:=Module[{tdual, dualOpt, dualSol},
	tdual = ToDual[algs[[algI]]~Append~costLiSven,varD1,varD2];
	{dualOpt, dualSol} = Minimize[Append[tdual[[1]],constrExtra]/.ExtractNonLin@nonLinParams,tdual[[2]]];
	dualSol
]~Join~nonLinParams
EvaluateDual[params_,algIset_:;;]:=Join[
	{{"u[alg]", "Alg Mass","Alg Index"}},
	Table[{u[i], Style[algMass,PrintPrecision->2], algIndex}/.algsWithMass[[algIset[[i]]]],{i,1,Length[algIset]}],
	{{u[Length@algIset+1],Style[{a,a,a,b,b,b,b,b,b},PrintPrecision->2]/.{a->1-b},"LS"}}
]/.params



algsI=algsI7b
solDual=SolveDualLP[sol,algsI]
Grid@EvaluateDual[%,algsI] 


(* ::Subsection:: *)
(*Explore Dual*)


(* Initialize manipulate *)
{b0,g0,gammaB0,gammaC0}={b,g,gammaB,gammaC}/.sol;


BigFractionStyle = Style[#, DefaultOptions -> {FractionBoxOptions -> {AllowScriptLevelChange -> False}}] &;
algsI=algsI5
constrExtra={};
Manipulate[
    {tb,tgammaB,tgammaC}={pb,pgammaB,pgammaC}; (* allow saving of modifications *)
    msolDual = SolveDualLP[{b->pb,gammaB->pgammaB,gammaC->Min[1,pgammaB],g->pg},algsI(*,{u[i1]>=eps1}*)];
	mtmp=Total[u[#]*allMass[[algsI[[#]]]]&/@{i1,i2,3}]/Total[u[#]&/@{i1,i2,3}] /.msolDual;
    BigFractionStyle@Column@{alpha/.msolDual, Grid@EvaluateDual[msolDual,algsI],
	(* What mass would be needed to combine first and second algos *)
	mtmp, mtmp[[5]]/mtmp[[4]],{algsI[[i2]],algsI[[i1]]},1/2(1+1/g)}/.msolDual
   ,{{pb,b0},0,1,.001},{{pgammaB,gammaB0},.01,1.5,.001},{{pgammaC,gammaC0},.01,1,.001},{{pg,g0},.01,1,.001}
   ,{eps1,0,1,.01},{i1,1,Length@algsI,1},{i2,1,Length@algsI,1}]


{b0,gammaB0,gammaC0}={tb,tgammaB,tgammaC} (* optionally persist modifications *)


(* ::Subsubsection:: *)
(*Explore DUAL - combining the F1=0 cases*)


BigFractionStyle = Style[#, DefaultOptions -> {FractionBoxOptions -> {AllowScriptLevelChange -> False}}] &;
algsI=algsI5
constrExtra={};
Manipulate[
    {tb,tgammaB,tgammaC}={pb,pgammaB,pgammaC}; (* allow saving of modifications *)
    msolDual = SolveDualLP[{b->pb,gammaB->pgammaB,gammaC->Min[1,pgammaB],g->pg},algsI(*,{u[i1]>=eps1}*)];
	mtmp=Total[u[#]*allMass[[algsI[[#]]]]&/@{i1,i2,3}]/Total[u[#]&/@{i1,i2,3}] /.msolDual;
    BigFractionStyle@Column@{alpha/.msolDual, Grid@EvaluateDual[msolDual,algsI],
	(* What mass would be needed to combine first and second algos *)
	mtmp, mtmp[[5]]/mtmp[[4]],{algsI[[i2]],algsI[[i1]]},1/2(1+1/g)}/.msolDual
   (*,{{pb,b0},0,1,.001},{{pgammaB,gammaB0},.01,1.5,.001},{{pgammaC,gammaC0},.01,1,.001},{{pg,g0},.01,1,.001}*)
	,{{pb,2/3},0/60,1,1/12},{{pgammaB,2/3},0/60,1,1/12},{{pg,1/2},0/60,1,1/12}
   ,{eps1,0,1,.01},{i1,1,Length@algsI,1},{i2,1,Length@algsI,1}]


Protect[mu1,mu2]
partialDual2={
	 {b->2/3, g->1/2, mu1->(3 gammaB+5)/(3 gammaB+6),mu2->(3 gammaB+4)/(3 gammaB+6)}
	,{b->2/3, g->2/3, mu1->(3 gammaB+5)/(3 gammaB+6),mu2->(3 gammaB+4)/(3 gammaB+6)}
};
params=partialDual2[[2]]
points=Table[{n,gammaB," ",#[[4]],mu1," "
                          ,#[[5]],mu2," "
				}/.params~Select~(MemberQ[{mu1,mu2},#[[1]]]&)&@(
		Total[u[#]*allMass[[algsI[[#]]]]&/@{1,2,3}] / Total[u[#]&/@{1,2,3}]
	)/.SolveDualLP[Append[#,gammaC->gammaB/.#]&[ params~Join~{b->2/3,gammaB->n/12,g->1/2} ],algsI]
,{n,1,11}];
BigFractionStyle@Grid@points


(* ::Subsubsection:: *)
(*Explore TOOL - combining 30 and 31*)


Plot[{#[[5]]/#[[4]]}&[(u[4]*allMass[[algsI[[4]]]]+u[5]*allMass[[algsI[[5]]]])/(u[4]+u[5])]
	/.SolveDualLP[{b->3/5,gammaB->pgammaB,gammaC->.00001,g->1/3},algsI],{pgammaB,0.01,1},PlotRange->{0,1}]


Plot[{#[[4]],#[[5]]}&[(u[4]*allMass[[algsI[[4]]]]+u[5]*allMass[[algsI[[5]]]])/(u[4]+u[5])]
	/.SolveDualLP[{b->pb,gammaB->(gammaB/.sol),gammaC->.0001,g->ghat},algsI],{pb,0.01,1},PlotRange->{0,1}]


Plot[{#[[4]],#[[5]],#[[5]]/#[[4]]}&[(u[4]*allMass[[algsI[[4]]]]+u[5]*allMass[[algsI[[5]]]])/(u[4]+u[5])]
	/.SolveDualLP[{b->(b/.sol),gammaB->(gammaB/.sol),gammaC->.0001,g->pg},algsI],{pg,0.01,1},PlotRange->{0,1}]


Solve[{(4-3g)/(4+2g)==x5/x4, gammaB*x4+x5==b}, {x4, x5}]


partialDual1={
	{b->3/5, gammaB->1/3, mu->1/3(4+5g)/(5-2g)}, 
	{b->3/5, gammaB->2/5, mu->(1+2g)/(5-2g)}, 
	{b->3/5, gammaB->1/2, mu->1/2(1+5g)/(5-2g)}, 
	{b->3/5, gammaB->3/5, mu->3g/(5-2g)}, 
    {b->2/3, gammaB->1/4, mu->1/4*(5+3g)/(3-g)}, 
	{b->2/3, gammaB->2/7,mu->2/7*(4+3g)/(3-g)}, 
	{b->2/3, gammaB->1/3, mu->1/3*(3+3g)/(3-g)}, 
	{b->2/3, gammaB->2/5,mu->2/5(2+3g)/(3-g)}, 
    {b->2/3, gammaB->1/2,mu->1/2*(1+3g)/(3-g)}, 
	{b->2/3, gammaB->3/5,mu->1/5*(1+9g)/(3-g)}, 
    {b->2/3, gammaB->2/3, mu->2/3*(0+3g)/(3-g)}, 

	{b->2/3, gammaB->3/4, mu->1/4*(-1+9g)/(3-g)}
};
partialDual={
	{b->3/5, mu->(3-5gammaB(1-g))/(5-2g)}, 
	{b->2/3, mu->(2-3gammaB(1-g))/(3-g)}, 
	{b->7/10, mu->(7-10gammaB(1-g))/(10-3g)}, 
	{b->3/4, mu->(3-4gammaB(1-g))/(4-g)}, 
	{mu->(b-gammaB(1-g))/(1-g(1-b))} 
}


b/(1+gammaB/mu)/.{mu->(b-gammaB(1-g))/(1-g(1-b))}//Simplify
b/(mu+gammaB)/.{mu->(b-gammaB(1-g))/(1-g(1-b))}//Simplify
{(b+(-1+g) gammaB)/(1+g gammaB),(1+(-1+b) g)/(1+g gammaB)}


params=partialDual[[5]]
points=Table[{n,g," ",#[[4]],b/(gammaB+mu)," ", b/(1+gammaB/mu),  #[[5]]," "
				, #[[5]]/#[[4]],mu , mu/(#[[5]]/#[[4]])
				}/.params~Select~(#[[1]]==mu&)&@(
		(u[4]*allMass[[algsI[[4]]]]+u[5]*allMass[[algsI[[5]]]])/(u[4]+u[5])
	)/.SolveDualLP[params~Join~({b->.69,gammaB->gm,gammaC->gm,g->1-1/n}/.{gm->.71}/.params),algsI]
,{n,2,6}];
Grid@points


(* ::Subsubsection::Closed:: *)
(*Scratch*)


algsI6test={4,8,29,30,31,32} (*rm 22*)
constrX={Z<=.2*algs[[22]]+.8*algs[[28]]};


algsI=algsI6test
sol3=SolveNLP[ghat,300,algsI,constrX]
sol3=SolveLPatSol[sol3,algsI,constrX];
Column@{Z/.sol3,Chop[sol3, .0001],EvaluateAlgsByMass[sol3,algsI]}


Plot[{u[4],u[5]}/(u[4]+u[5])/.SolveDualLP[{b->(b/.sol),gammaB->pgammaB,gammaC->.0001,g->ghat},algsI6b],{pgammaB,0.01,1},PlotRange->{0,1}]


(* ::Section::Closed:: *)
(*Previous Exploration*)


(* ::Subsection:: *)
(*Do we smoothly and fully optimize for full range of parameters?*)


(* see what optimal value of b is for various gammas. If it's in small range, we can sometimes estimate it as a constant for simplicity. *)
solGrid=ParallelTable[SolveNLP[ghat,250,algsI,{gammaB==gb}],{gb,.1,.9,.05}];
ListPlot[{gammaB,b}/.#&/@solGrid] (* b is usually around .67 *)


(* the extra d-constraints arent immediately valid, but necessary to smooth out small gamma region. to make valid, we would need to split clients into multiple classes, according to which facility is closest *)
Table[Plot[Z-.32tb/.SolveLPatSol[{g->tg,b->tb,algsI,gammaB->.02,gammaC->.02},algsI6b,constrD1D2~Union~constrD1D2g],{tb,.3,.6}], {tg, .5, .7, .05}]


(*plotGrid=Table[Plot[{1.012,Z}/.SolveLPatSol[{g->.6586,b->.01,algsI,gammaB->gamma,gammaC->gamma},algsI6~Join~{i}],{gamma,0,1}],{i,1,8}]*)


sols3=ParallelTable[SolveLPatSol[{g->.6586,b->pb,gammaB->gamma,gammaC->Min[gamma,.9999]},All,constrD1D2~Union~constrD1D2g]
	,{gamma,0.011,1.5,.1},{pb,0.01,1,.04}]~Flatten~1;
points3={gammaB, b, Z}/.#&/@sols3;
plot3=ListPlot3D[points3,ColorFunction->(RGBColor[0,1,0]&),AxesLabel->{"gamma","b","Z"}]



(* with algsI6b, there is maybe some small looseness in outer regions ? *)
sols4=ParallelTable[{SolveLPatSol[{g->.6586,b->pb,gammaB->gamma,gammaC->Min[gamma,.9999]},algsI6b,constrD1D2~Union~constrD1D2g]
	                ,SolveLPatSol[{g->.6586,b->pb,gammaB->gamma,gammaC->Min[gamma,.9999]},All,    constrD1D2~Union~constrD1D2g]}
	,{gamma,0.011,1.5,.1},{pb,0.01,1,.04}]~Flatten~1;
points4={gammaB/.#[[1]], b/.#[[1]], (Z/.#[[1]]) - (Z/.#[[2]])}&/@sols4;
plot4=ListPlot3D[points4,ColorFunction->(RGBColor[1,0,0]&),AxesLabel->{"gamma","b","Z"}]


sols4[[1]]
{gammaB/.#[[1]], b/.#[[1]], (Z/.#[[1]]) - (Z/.#[[2]])}&@%


algsI=algsI7b
solNLP=SolveNLP[ghat,250,algsI]; 
sol=SolveLPatSol[solNLP,algsI]; 
{Z/.solNLP,Z/.sol} (* see looseness in NLP solution *)
Column@{Z/.sol,Chop[sol, .0001],EvaluateAlgsByMass[sol,algsI]}


(* ::Subsection::Closed:: *)
(*Explore Tight Point*)


(* Initialize manipulate *)
{b0,g0,gammaB0,gammaC0}={b,g,gammaB,gammaC}/.sol;


Manipulate[Module[{sol2},
{tb,tgammaB,tgammaC}={pb,pgammaB,pgammaC}; (* allow saving of modifications *)
sol2 = SolveLPatSol[{b->pb,gammaB->pgammaB,gammaC->pgammaC,g->g0},algsI(*~Union~{6,1,5,27}*),constrD1D2~Union~constrD1D2g];
Column@{Z/.sol2,sol2,EvaluateAlgsByCost[sol2,algsI7b]}
],{{pb,b0},0,1,.001},{{pgammaB,gammaB0},.1,1.5,.001},{{pgammaC,gammaC0},.1,1,.001}]



{b0,gammaB0,gammaC0}={tb,tgammaB,tgammaC} (* persist modifications *)
