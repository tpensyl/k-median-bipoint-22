(* ::Package:: *)

(* ::Title:: *)
(*F2-Stars*)


(* ::Subsection::Closed:: *)
(*Notebook Settings*)


SetOptions[EvaluationNotebook[],CellContext->Notebook, PrintPrecision->8]
SetOptions[Plot3D, AxesLabel->Automatic,
	PlotStyle->Opacity[.7], ClippingStyle->None,
	BoundaryStyle -> Directive[Black, Thick]];
Import@FileNameJoin[{ParentDirectory[NotebookDirectory[]],"util","visualizeMass.m"}]
VisualMass2[p_List,opts___]:=VisualMass[p[[{1,3,2,4,5,6}]],2,opts]


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


(* ::Subsubsection::Closed:: *)
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
massbgamma0={{1,0,1,x,y1,z1},{1,0,x,1,y1,z1},{0,1,1,x,y1,z1},{0,1,x,1,y1,z1},
	{1,0,1,x,y2,z2},{1,0,x,1,y2,z2},{0,1,1,x,y2,z2},{0,1,x,1,y2,z2}}/.{
	x->Min[1,b/gammaB], y1->Max[0,1-(1-b+gammaB)/gammaC],z1->Max[Min[1,(b-gammaB)/(1-gammaC)],0],
	y2->Max[Min[1,(b-gammaB)/gammaC],0],z2->Max[0,(b-gammaB-gammaC)/(1-gammaC)]};
massbgamma1={{1,0,0,x,y1,z1},{1,0,x,0,y1,z1},{0,1,0,x,y1,z1},{0,1,x,0,y1,z1},
	{1,0,0,x,y2,z2},{1,0,x,0,y2,z2},{0,1,0,x,y2,z2},{0,1,x,0,y2,z2}}/.{
	x->Max[0,1-(1-b)/gammaB], y1->Min[Max[0,1-(1-b-gammaB)/gammaC],1],z1->Min[1,(b+gammaB)/(1-gammaC)],
	y2->Min[1,(b+gammaB)/gammaC],z2->Min[Max[0,(b+gammaB-gammaC)/(1-gammaC)],1]};
massOnlyC={{1,0,x,y,1,z},{0,1,x,y,1,z},{1,0,y,x,1,z},{0,1,y,x,1,z}}/.{
	x->Max[Min[1,(b-gammaC)/gammaB],0], y->Min[Max[0,1-(gammaC-b)/gammaB],1],z->Max[0,(b-gammaB-gammaC)/(1-gammaC)]};
massCombos={{0,1,0,1,b,b} (*29: combine 4,8*)
	,{1,0,1,0,b,b} (*30 combine 1,5*)
	,{0,1,1,0,b,b} (*31: combine 2,6*)
    ,{0,1,1,x,y,y}/.{x->Min[1,b/gammaB],y->Max[0,b-gammaB]}(*32: flatten _*)
    ,{1,0,1,x,y,y}/.{x->Min[1,b/gammaB],y->Max[0,b-gammaB]}(*33: flatten _*)
	,{1,0,1,x,mu*x,mu*x}/.{x->b/(gammaB+mu)}/.{mu->1/2(1+1/g)} (* 34: further flatten 30 and 33 *)
	,{0,1,1,x,y,y}/.{x->Min[1-g*mu,b/gammaB],y->Max[0,1-mu]}/.{mu->(1-b+gammaB)/(1+g*gammaB)} (* 35: further flatten 31 and 32 TODO handle case when negative*)
	,{0,1,0,x,y,y}/.{x->1-(1-b)*g/(g*gammaB+1), y->1-(1-b)/(g*gammaB+1)}(* 36: CHEAT,but cost is attainable using multiple algorithms. combine 4,8,22*)
	(* 37: cheat, but attainable via convex combo of {0,1,0,1,z,x} and {0,1,0,z,1,x} - b/c we maintain p2c+p2d>=1 *)
	 ,{0,1,0,x,y,y}/.{x->1-Min[(1-b)/gammaB,b/Max[b,1-gammaB]],y->b/Max[b,1-gammaB]}
	(*,{0,1,0,y,x,x}/.{x->Min[1,b+gammaB],y->Max[0,1-(1-b)/gammaB]}*)(* alt cheat, doesn't maintain p2c+p2d>=1*)
}//Simplify;
massLiSven={1-b,b,1-b,b,b,b};


Manipulate[Plot[massCombos[[-1]][[{4,5}]]/.{b->mb,gammaB->mgammaB},{mgammaB,0,2},PlotRange->{-.2,1.2}],{{mb,.6},0,1}];


CheckMass[mass_]:=FullSimplify[{gA,gA,gammaB,gammaB,gammaC,1-gammaC}.(mass-{a,b,a,b,b,b})/.{a->1-b},
	{0<=b<=1,0<gammaB<=1,0<gammaC<1,gammaC<gammaB}]
CheckMass/@allMass (* check if the mass balances; it should equal zero *)


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


(* ::Subsubsection::Closed:: *)
(*Variables and Constraints:*)


allMass=Join[massSafe,massbgamma0,massbgamma1,massOnlyC,massCombos];
algs=Append[cost@@#&/@allMass,costLiSven];
AppendTo[allMass,massLiSven];
Length@algs
algsWithMass=Table[{algCost->algs[[i]],algMass->allMass[[i]],algIndex->i},{i,1,Length[allMass]}];
constrAlg = Z<=#&/@algs;

varNonLin={b,g,gammaB,gammaC};
vars=Union[varD1,varD2,varNonLin,{Z}];

constrD1D2=MapThread[#1<=#2&,{varD2,varD1}];
constrD1D2g=MapThread[#1+g(#1+#2)>=#2+(#1+#2)&,{{d1ac, d1ad},{d2ac, d2ad}}];
constrBasic = Join[{Z>=0,0<=b<=1,0<=gammaB,0<=gammaC<=1,gammaC<=gammaB},#>=0&/@Union[varD1,varD2]
        ,{Total[varD1]*(1-b)+Total[varD2]*b==1}];


(* ::Subsection::Closed:: *)
(*Utility Methods*)


(* Show tight algorithms *)
StyleMass[mass_]:=Style[mass,PrintPrecision->2]
EvaluateAlgs[params_,algIset_:;;]:=(
		{algCost, algMass//StyleMass, VisualMass2[algMass,ImageSize->{100,60}], algIndex}/.#&/@algsWithMass[[algIset]]
	)/.params
EvaluateAlgsByCost[params_,algIset_:;;]:=Grid[SortBy[EvaluateAlgs[params,algIset],First]~Prepend~{"Alg Cost ", "Alg Mass","Alg Index"},Alignment->Left]
EvaluateAlgsByMass[params_,algIset_:;;]:=Grid[SortBy[EvaluateAlgs[params,algIset],#[[2]]&]~Prepend~{"Alg Cost ", "Alg Mass","Alg Index"},Alignment->Left]
EvaluateAlgsByIndex[params_,algIset_:;;]:=Grid[SortBy[EvaluateAlgs[params,algIset],#[[3]]&]~Prepend~{"Alg Cost ", "Alg Mass","Alg Index"},Alignment->Left]


(* type checking: needed for multiple optional arguments and generally helpful for debugging *)
IndexQ[i_]:=(i==All || i==(1;;All) || And@@IntegerQ/@i) (* allow passing ;; or All for index subset *)
EquationQ[eq_]:=Not@FreeQ[eq,(Equal|LessEqual|Less|Greater|GreaterEqual)]||eq (* contains one of =,<,<=,>,>=, or trivially true *)

(* We will fix the value of g, and let the adversary set the mass variable gamma *)
SolveNLP[g1hat_,iter_,algI_,constrExtra_:{}]:=
	NMaximize[{Z, constrAlg[[algI]], constrBasic, g==g1hat, constrExtra,
		.1 <= b <= .9, .1 <= gammaB, .1 <= gammaC <= .9 (* manual hints. some problems with gamma12->0, but also maybe valid *)
	}, vars~Union~{g}, MaxIterations->iter][[2]]
SolveNLP[g1hat_,iter_,algI_:;;]:=SolveNLP[g1hat,iter,algI,{}]

(* If we fix non-linear variables, remaining system is linear and very fast/accurate *)
SolveLP[nonLinParams_,algI:_?IndexQ:All,constrExtra:{___?EquationQ}:{}]:=
	Maximize[{Z, constrAlg[[algI]], constrBasic, constrExtra}/.nonLinParams,
		Union[varD1,varD2,{Z}]][[2]]~Join~nonLinParams;
SolveLPatSol[fullSol_,algI:_?IndexQ:All,constrExtra:{___?EquationQ}:{}]:=SolveLP[ExtractNonLin[fullSol], algI,constrExtra]
ExtractNonLin[sol_]:=Select[sol,MemberQ[varNonLin,#[[1]]]&]

createVar[terms__]:=ToExpression@StringJoin@@ToString/@List[terms]


(* ::Subsection::Closed:: *)
(*Solving the NLP*)


algsI10={-1,1,4,5,6,8,9,11,16,23,28}; (* minimal set of extreme points *)
algsI7={-1,8,23,29,30,31,32,33}; (* re-add some algo. Graphically, (with some heuristic), 5(8 now) seems to be the 'most complete' algo to add.*)
algsI8={-1,4,8,23,29,30,31,32,33};
algsI7b={-1,4,8,23,30,31,32,33}; (* our in-between wasn't actually special here *)
algsI6b={-1,4,8,23,31,32,34};
algsI5={-1,4,8,23,34,35};
algsI3={-1,34,35,36};
algsI6sym={-1,29,30,31,32,33,37}; (* 36 is cost-equivalent to a convex combination of 2 valid algos *)
algsI=algsI6sym
ghat=0.6586066
solNLP=SolveNLP[ghat,300,algsI] (* for much higher speed and accuracy, use exactSolutionForm from later on *)


sol=SolveLPatSol[solNLP,algsI6sym(*, constrD1D2~Union~constrD1D2g*)];
Column@{Z/.sol,Chop[sol, .0001],EvaluateAlgsByMass[sol,algsI]}


(* ::Subsection::Closed:: *)
(*Result*)


(* ::Text:: *)
(*By setting g=0.6586066, we get approximation factor 1.310188885063*)
(**)
(*This file gives several possible algo sets to achieve this. Also a closed form solution for the critical region. *)
(**)
(*Some of the later algorithms are not directly feasible, but are cost equivalent to convex combination of valid algos. (e.g. as long as p2b+p2c>=1)*)
(**)
(*This NLP could be simplified by padding such that |F2C|=min{|F2B|,|Y|}, to fix gammaC:=Min[1,gammaB]. Or using something like alg6sym, the need for variable gammaC vanishes entirely.*)


(* ::Section::Closed:: *)
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
	tdual = ToDual[algs[[algI]],varD1,varD2];
	{dualOpt, dualSol} = Minimize[Append[tdual[[1]],constrExtra]/.ExtractNonLin@nonLinParams,tdual[[2]]];
	dualSol
]~Join~nonLinParams
EvaluateDual[params_,algIset_:;;]:=Join[
	{{"u[alg]", "Alg Mass",,"Global Index","Local Index"}},
	Table[{u[i], algMass//StyleMass, VisualMass2[algMass,ImageSize->{150,80}],
			 algIndex, i}/.algsWithMass[[algIset[[i]]]],{i,1,Length[algIset]}]
]/.params



algsI=algsI3
solDual=SolveDualLP[sol,algsI]
Grid@EvaluateDual[%,algsI] 


(* ::Subsection:: *)
(*Explore Dual*)


(* ::Subsubsection:: *)
(*Manipulate*)


BigFractionStyle = Style[#, DefaultOptions -> {FractionBoxOptions -> {AllowScriptLevelChange -> False}}] &;
algsI=algsI6sym
algsI=algsI3
constrExtra={};
{b0,g0,gammaB0,gammaC0}={b,g,gammaB,gammaC}/.sol;
Manipulate[Module[{msolDual,msolOptBaseline,mCombo},
	mparamsg1 = {b->pb,gammaB->pgammaB,gammaC->pgammaC,g->pg};
    msolDual = SolveDualLP[mparamsg1,algsI,Join[u[#]==0&/@removeI,(u[#]>=eps1&)/@forceI]];
	msolOptBaseline = alpha/.SolveDualLP[mparamsg1,Range@Length@algs];
	mCombo=Total[u[#]*allMass[[algsI[[#]]]]&/@comboI]/Max[.0001,Total[u[#]&/@comboI]];
    BigFractionStyle@Column@{Row@{msolOptBaseline,"(Baseline)"},alpha, {algsI[[comboI]],mCombo},VisualMass2[mCombo,ImageSize->{80,80}]
		, Grid@Select[SortBy[EvaluateDual[msolDual,algsI],#[[2]]&],Chop[#[[1]]]!=0&]}/.msolDual
   ],{{pb,b0},0,1,1/100.},{{pgammaB,gammaB0},1/100,3/2,1/100.},{{pgammaC,gammaC0},1/100,1,1/100},{{pg,g0},1/100,1,1/100.}
   ,{{eps1,.01},0,1,1/100},{{removeI,{}}},{{comboI,Range@Length@algsI}},{{forceI,{}}}]


save2=mparamsg1 (* optionally save modifications *)


tsol=save2;
{{-1},{30,33,34},{31,32,35},{29,37,36}}  (* 3rd column is algsI3, the resp. combos of first two *)
Grid[VisualMass2[allMass[[#]]/.tsol,ImageSize->{100,100}]&/@#&/@%]
{{0.5915267785771386`,0.40847322142286135`,0.6642685851318949`,0.33573141486810515`,0.6666666666666666`,0.6666666666666666`}
,{0.44508027340645356`,0.5549197265935465`,0.8831664282308058`,0.9221109521538706`,0.26402797647432846`,0.26402797647432846`}};
VisualMass2[#/.tsol,ImageSize->{100,100}]&/@%


(* ::Subsubsection::Closed:: *)
(*Exact Rational Form (manual)*)


BigFractionStyle = Style[#, DefaultOptions -> {FractionBoxOptions -> {AllowScriptLevelChange -> False}}] &;
algsI=algsI3
constrExtra={};
Manipulate[
    {tb,tgammaB,tgammaC}={pb,pgammaB,pgammaC}; (* allow saving of modifications *)
    msolDual = SolveDualLP[{b->pb,gammaB->pgammaB,gammaC->Min[1,pgammaB],g->pg},algsI(*,{u[i1]>=eps1}*)];
	mtmp=Total[u[#]*allMass[[algsI[[#]]]]&/@{i1,i2}]/Total[u[#]&/@{i1,i2}] /.msolDual;
    BigFractionStyle@Column@{N[alpha/.msolDual], Grid@EvaluateDual[msolDual,algsI],
	(* What mass would be needed to combine first and second algos *)
	mtmp, {algsI[[i2]],algsI[[i1]]}}/.msolDual
   (*,{{pb,b0},0,1,.001},{{pgammaB,gammaB0},.01,1.5,.001},{{pgammaC,gammaC0},.01,1,.001},{{pg,g0},.01,1,.001}*)
	,{{pb,2/3},0/60,1,1/12},{{pgammaB,2/3},0/60,1,1/12},{{pg,1/2},0/60,1,1/12}
   ,{eps1,0,1,.01},{i1,1,Length@algsI,1},{i2,2,Length@algsI,1}];


(* start figuring out form of solutions by hand, looking for patterns *)
partialDual33to34={
	 {b->1/2, g->1/2, p2cd->(144+12*gammaB*15)/(288+51*12*gammaB+2*144*gammaB^2),
					p2b->(126+12*gammaB*12)/(288+51*12*gammaB+2*144*gammaB^2)}
}
params=partialDual33to34[[1]]
points=Table[{n,gammaB," ",#[[4]],p2b," "
                          ,#[[5]],p2cd," "
				}/.params&@(
		Total[u[#]*allMass[[algsI[[#]]]]&/@{1,2}] / Total[u[#]&/@{1,2}]
	)/.SolveDualLP[Append[#,gammaC->gammaB/.#]&[ params~Join~{b->2/3.,gammaB->n/12,g->1/2.} ],algsI]
,{n,1,11}];
BigFractionStyle@Grid@points;


(* ::Subsubsection::Closed:: *)
(*Automate rational form-finding*)


(* Example: here we parameterized terms have combined algorithms, in terms of gammaB.
   We can then follow up and look in terms of g and b, and try to combine them *)
(* TODO taken the parameters as an argument, with the ability to template out variable; maybe even specify range *)
Clear[MergeAlgos]
MergeAlgos[algsI_List, algsII_List, form_]:=Module[{data,fits,forms},
	data=Transpose@Flatten[Table[
		Join[
			{gammaB,b,g,alpha,u[1],u[2],u[3],u[4]},
			Total[u[#]*allMass[[algsI[[#]]]]&/@algsII] / Total[u[#]&/@algsII]
		]/.SolveDualLP[Append[#,gammaC->gammaB/.#]&[ {b->2/3,gammaB->2/3,g->tg} ],algsI]
	,{tgammaB,51/100,52/100,1/100/5},{tg,66/100,67/100,1/100/6}],1];
	fits=Table[
		Solve@MapThread[#4==form/.{gammaB->#1,b->#2,g->#3}&,{data[[1]],data[[2]],data[[3]],yRow}]
	,{yRow,data}]; (*Print[fits];*)
	forms=Table[If[fit=={},"WRONG FORM",form/.fit[[1]]], {fit,fits}];
	Column@ExpandDenominator@ExpandNumerator@Simplify@forms
]
algsItemp=algsI3;
form=Sum[v[1,i]*x^i,{i,0,3}]/
     Sum[v[2,i]*x^i,{i,0,3}]/. {v[2,0]->1, x->g}
MergeAlgos[algsItemp,{1,2,3,4},form]


(* Detect 2 vars *)
Clear[MergeAlgos]
MergeAlgos[algsI_List, algsII_List, form_]:=Module[{data,fits,forms},
	data=Transpose@Flatten[Table[
		Join[
			{gammaB,b,g,alpha,u[1],u[2],u[3],u[4]},
			Total[u[#]*allMass[[algsI[[#]]]]&/@algsII] / Total[u[#]&/@algsII]
		]/.SolveDualLP[Append[#,gammaC->gammaB/.#]&[ {b->tb,gammaB->tgammaB,g->1/2} ],algsI]
	,{tgammaB,51/100,52/100,1/100/4},{tb,66/100,67/100,1/100/5}],1];
	fits=Table[
		Solve@MapThread[#4==form/.{gammaB->#1,b->#2,g->#3}&,{data[[1]],data[[2]],data[[3]],yRow}]
	,{yRow,data[[{4}]]}]; (*Print[fits];*)
	forms=Table[If[fit=={},"WRONG FORM",form/.fit[[1]]], {fit,fits}];
	Column@ExpandDenominator@ExpandNumerator@Simplify@forms
]
algsItemp=algsI3;
Protect[v];
form=Sum[v[1,i,j]*x^i*y^j,{i,0,2},{j,0,2}]/
	 Sum[v[2,i,j]*x^i*y^j,{i,0,2},{j,0,3}]/. {v[2,0,0]->1, x->gammaB, y->b}
{time,result}=Timing@MergeAlgos[algsItemp,{1,2,3,4},form]/.gammaB->\[Gamma]


(* Detect all 3 vars. *)
Clear[MergeAlgos]
MergeAlgos[algsI_List, algsII_List, form_]:=Module[{data,fits,forms},
	data=Transpose@Flatten[Table[
		Join[
			{gammaB,b,g,alpha,u[1],u[2],u[3],u[4]},
			Total[u[#]*allMass[[algsI[[#]]]]&/@algsII] / Total[u[#]&/@algsII]
		]/.SolveDualLP[Append[#,gammaC->gammaB/.#]&[ {b->tb,gammaB->tgammaB,g->tg} ],algsI]
	,{tgammaB,51/100,52/100,1/100/3},{tb,66/100,67/100,1/100/4},{tg,55/100,56/100,1/100/3}],2];
	fits=Table[
		Solve@MapThread[#4==form/.{gammaB->#1,b->#2,g->#3}&,{data[[1]],data[[2]],data[[3]],yRow}](*//(Print[#];#)&*)
	,{yRow,data}]; (*Print[fits];*)
	forms=Table[If[fit=={},"WRONG FORM",form/.fit[[1]]], {fit,fits}];
	Column[ExpandDenominator@ExpandNumerator@Simplify@forms,Spacings->1]
]
algsItemp=algsI3;
Protect[v];
form=Sum[v[1,i,j,k]*x^i*y^j*z^k,{i,0,2},{j,0,3},{k,0,2}]/
	 Sum[v[2,i,j,k]*x^i*y^j*z^k,{i,0,2},{j,0,3},{k,0,2}]/. {v[2,0,0,0]->1, x->gammaB, y->b, z->g};
{time,result}=Timing@MergeAlgos[algsItemp,{1,2,3,4},form]/.gammaB->\[Gamma];
time
result


(* ::Subsubsection::Closed:: *)
(*Exact Dual feasibility*)


(* Can we use this closed form as a dual feasible solution? *)
fsol={alpha->#1,u[1]->#2,u[2]->#3,u[3]->#4,u[4]->#5}&@@#[[1]]/.{\[Gamma]->gammaB}&@
\!\(\*
TagBox[GridBox[{
{
FractionBox[
RowBox[{
RowBox[{"-", "2"}], "+", 
RowBox[{"4", " ", "b"}], "-", 
RowBox[{"2", " ", 
SuperscriptBox["b", "2"]}], "-", "g", "+", 
RowBox[{"b", " ", "g"}], "-", 
RowBox[{"3", " ", "\[Gamma]"}], "+", 
RowBox[{"2", " ", "b", " ", "\[Gamma]"}], "-", 
RowBox[{"5", " ", "g", " ", "\[Gamma]"}], "+", 
RowBox[{"9", " ", "b", " ", "g", " ", "\[Gamma]"}], "-", 
RowBox[{"4", " ", 
SuperscriptBox["b", "2"], " ", "g", " ", "\[Gamma]"}], "-", 
RowBox[{"6", " ", "g", " ", 
SuperscriptBox["\[Gamma]", "2"]}], "+", 
RowBox[{"4", " ", "b", " ", "g", " ", 
SuperscriptBox["\[Gamma]", "2"]}], "+", 
RowBox[{
SuperscriptBox["g", "2"], " ", 
SuperscriptBox["\[Gamma]", "2"]}]}], 
RowBox[{
RowBox[{"-", "2"}], "+", 
RowBox[{"4", " ", "b"}], "-", 
RowBox[{"2", " ", 
SuperscriptBox["b", "2"]}], "-", "g", "+", 
RowBox[{"3", " ", "b", " ", "g"}], "-", 
RowBox[{"4", " ", 
SuperscriptBox["b", "2"], " ", "g"}], "+", 
RowBox[{"2", " ", 
SuperscriptBox["b", "3"], " ", "g"}], "-", 
RowBox[{"3", " ", "\[Gamma]"}], "+", 
RowBox[{"4", " ", "b", " ", "\[Gamma]"}], "-", 
RowBox[{"2", " ", 
SuperscriptBox["b", "2"], " ", "\[Gamma]"}], "-", 
RowBox[{"5", " ", "g", " ", "\[Gamma]"}], "+", 
RowBox[{"11", " ", "b", " ", "g", " ", "\[Gamma]"}], "-", 
RowBox[{"8", " ", 
SuperscriptBox["b", "2"], " ", "g", " ", "\[Gamma]"}], "+", 
RowBox[{"2", " ", 
SuperscriptBox["b", "3"], " ", "g", " ", "\[Gamma]"}], "-", 
RowBox[{"6", " ", "g", " ", 
SuperscriptBox["\[Gamma]", "2"]}], "+", 
RowBox[{"8", " ", "b", " ", "g", " ", 
SuperscriptBox["\[Gamma]", "2"]}], "-", 
RowBox[{"4", " ", 
SuperscriptBox["b", "2"], " ", "g", " ", 
SuperscriptBox["\[Gamma]", "2"]}], "+", 
RowBox[{
SuperscriptBox["g", "2"], " ", 
SuperscriptBox["\[Gamma]", "2"]}], "-", 
RowBox[{"2", " ", "b", " ", 
SuperscriptBox["g", "2"], " ", 
SuperscriptBox["\[Gamma]", "2"]}], "+", 
RowBox[{"2", " ", 
SuperscriptBox["b", "2"], " ", 
SuperscriptBox["g", "2"], " ", 
SuperscriptBox["\[Gamma]", "2"]}]}]]},
{
FractionBox[
RowBox[{"g", "-", 
RowBox[{"3", " ", "b", " ", "g"}], "+", 
RowBox[{"2", " ", 
SuperscriptBox["b", "2"], " ", "g"}], "-", "\[Gamma]", "+", 
RowBox[{"g", " ", "\[Gamma]"}], "-", 
RowBox[{"b", " ", "g", " ", "\[Gamma]"}], "-", 
RowBox[{"2", " ", "g", " ", 
SuperscriptBox["\[Gamma]", "2"]}], "+", 
RowBox[{
SuperscriptBox["g", "2"], " ", 
SuperscriptBox["\[Gamma]", "2"]}]}], 
RowBox[{
RowBox[{"-", "2"}], "+", 
RowBox[{"4", " ", "b"}], "-", 
RowBox[{"2", " ", 
SuperscriptBox["b", "2"]}], "-", "g", "+", 
RowBox[{"3", " ", "b", " ", "g"}], "-", 
RowBox[{"4", " ", 
SuperscriptBox["b", "2"], " ", "g"}], "+", 
RowBox[{"2", " ", 
SuperscriptBox["b", "3"], " ", "g"}], "-", 
RowBox[{"3", " ", "\[Gamma]"}], "+", 
RowBox[{"4", " ", "b", " ", "\[Gamma]"}], "-", 
RowBox[{"2", " ", 
SuperscriptBox["b", "2"], " ", "\[Gamma]"}], "-", 
RowBox[{"5", " ", "g", " ", "\[Gamma]"}], "+", 
RowBox[{"11", " ", "b", " ", "g", " ", "\[Gamma]"}], "-", 
RowBox[{"8", " ", 
SuperscriptBox["b", "2"], " ", "g", " ", "\[Gamma]"}], "+", 
RowBox[{"2", " ", 
SuperscriptBox["b", "3"], " ", "g", " ", "\[Gamma]"}], "-", 
RowBox[{"6", " ", "g", " ", 
SuperscriptBox["\[Gamma]", "2"]}], "+", 
RowBox[{"8", " ", "b", " ", "g", " ", 
SuperscriptBox["\[Gamma]", "2"]}], "-", 
RowBox[{"4", " ", 
SuperscriptBox["b", "2"], " ", "g", " ", 
SuperscriptBox["\[Gamma]", "2"]}], "+", 
RowBox[{
SuperscriptBox["g", "2"], " ", 
SuperscriptBox["\[Gamma]", "2"]}], "-", 
RowBox[{"2", " ", "b", " ", 
SuperscriptBox["g", "2"], " ", 
SuperscriptBox["\[Gamma]", "2"]}], "+", 
RowBox[{"2", " ", 
SuperscriptBox["b", "2"], " ", 
SuperscriptBox["g", "2"], " ", 
SuperscriptBox["\[Gamma]", "2"]}]}]]},
{
FractionBox[
RowBox[{
RowBox[{"-", "2"}], "+", 
RowBox[{"6", " ", "b"}], "-", 
RowBox[{"6", " ", 
SuperscriptBox["b", "2"]}], "+", 
RowBox[{"2", " ", 
SuperscriptBox["b", "3"]}], "-", 
RowBox[{"2", " ", "g"}], "+", 
RowBox[{"6", " ", "b", " ", "g"}], "-", 
RowBox[{"6", " ", 
SuperscriptBox["b", "2"], " ", "g"}], "+", 
RowBox[{"2", " ", 
SuperscriptBox["b", "3"], " ", "g"}], "-", 
RowBox[{"2", " ", "\[Gamma]"}], "+", 
RowBox[{"4", " ", "b", " ", "\[Gamma]"}], "-", 
RowBox[{"2", " ", 
SuperscriptBox["b", "2"], " ", "\[Gamma]"}], "-", 
RowBox[{"6", " ", "g", " ", "\[Gamma]"}], "+", 
RowBox[{"16", " ", "b", " ", "g", " ", "\[Gamma]"}], "-", 
RowBox[{"14", " ", 
SuperscriptBox["b", "2"], " ", "g", " ", "\[Gamma]"}], "+", 
RowBox[{"4", " ", 
SuperscriptBox["b", "3"], " ", "g", " ", "\[Gamma]"}], "-", 
RowBox[{"4", " ", "g", " ", 
SuperscriptBox["\[Gamma]", "2"]}], "+", 
RowBox[{"8", " ", "b", " ", "g", " ", 
SuperscriptBox["\[Gamma]", "2"]}], "-", 
RowBox[{"4", " ", 
SuperscriptBox["b", "2"], " ", "g", " ", 
SuperscriptBox["\[Gamma]", "2"]}]}], 
RowBox[{
RowBox[{"-", "2"}], "+", 
RowBox[{"4", " ", "b"}], "-", 
RowBox[{"2", " ", 
SuperscriptBox["b", "2"]}], "-", "g", "+", 
RowBox[{"3", " ", "b", " ", "g"}], "-", 
RowBox[{"4", " ", 
SuperscriptBox["b", "2"], " ", "g"}], "+", 
RowBox[{"2", " ", 
SuperscriptBox["b", "3"], " ", "g"}], "-", 
RowBox[{"3", " ", "\[Gamma]"}], "+", 
RowBox[{"4", " ", "b", " ", "\[Gamma]"}], "-", 
RowBox[{"2", " ", 
SuperscriptBox["b", "2"], " ", "\[Gamma]"}], "-", 
RowBox[{"5", " ", "g", " ", "\[Gamma]"}], "+", 
RowBox[{"11", " ", "b", " ", "g", " ", "\[Gamma]"}], "-", 
RowBox[{"8", " ", 
SuperscriptBox["b", "2"], " ", "g", " ", "\[Gamma]"}], "+", 
RowBox[{"2", " ", 
SuperscriptBox["b", "3"], " ", "g", " ", "\[Gamma]"}], "-", 
RowBox[{"6", " ", "g", " ", 
SuperscriptBox["\[Gamma]", "2"]}], "+", 
RowBox[{"8", " ", "b", " ", "g", " ", 
SuperscriptBox["\[Gamma]", "2"]}], "-", 
RowBox[{"4", " ", 
SuperscriptBox["b", "2"], " ", "g", " ", 
SuperscriptBox["\[Gamma]", "2"]}], "+", 
RowBox[{
SuperscriptBox["g", "2"], " ", 
SuperscriptBox["\[Gamma]", "2"]}], "-", 
RowBox[{"2", " ", "b", " ", 
SuperscriptBox["g", "2"], " ", 
SuperscriptBox["\[Gamma]", "2"]}], "+", 
RowBox[{"2", " ", 
SuperscriptBox["b", "2"], " ", 
SuperscriptBox["g", "2"], " ", 
SuperscriptBox["\[Gamma]", "2"]}]}]]},
{
FractionBox[
RowBox[{
RowBox[{
RowBox[{"-", "2"}], " ", "b"}], "+", 
RowBox[{"4", " ", 
SuperscriptBox["b", "2"]}], "-", 
RowBox[{"2", " ", 
SuperscriptBox["b", "3"]}], "+", 
RowBox[{"2", " ", "b", " ", "g"}], "-", 
RowBox[{"4", " ", 
SuperscriptBox["b", "2"], " ", "g"}], "+", 
RowBox[{"2", " ", 
SuperscriptBox["b", "3"], " ", "g"}], "-", 
RowBox[{"2", " ", "b", " ", "g", " ", "\[Gamma]"}], "+", 
RowBox[{"4", " ", 
SuperscriptBox["b", "2"], " ", "g", " ", "\[Gamma]"}], "-", 
RowBox[{"2", " ", 
SuperscriptBox["b", "3"], " ", "g", " ", "\[Gamma]"}], "+", 
RowBox[{"2", " ", "b", " ", 
SuperscriptBox["g", "2"], " ", "\[Gamma]"}], "-", 
RowBox[{"4", " ", 
SuperscriptBox["b", "2"], " ", 
SuperscriptBox["g", "2"], " ", "\[Gamma]"}], "+", 
RowBox[{"2", " ", 
SuperscriptBox["b", "3"], " ", 
SuperscriptBox["g", "2"], " ", "\[Gamma]"}]}], 
RowBox[{
RowBox[{"-", "2"}], "+", 
RowBox[{"4", " ", "b"}], "-", 
RowBox[{"2", " ", 
SuperscriptBox["b", "2"]}], "-", "g", "+", 
RowBox[{"3", " ", "b", " ", "g"}], "-", 
RowBox[{"4", " ", 
SuperscriptBox["b", "2"], " ", "g"}], "+", 
RowBox[{"2", " ", 
SuperscriptBox["b", "3"], " ", "g"}], "-", 
RowBox[{"3", " ", "\[Gamma]"}], "+", 
RowBox[{"4", " ", "b", " ", "\[Gamma]"}], "-", 
RowBox[{"2", " ", 
SuperscriptBox["b", "2"], " ", "\[Gamma]"}], "-", 
RowBox[{"5", " ", "g", " ", "\[Gamma]"}], "+", 
RowBox[{"11", " ", "b", " ", "g", " ", "\[Gamma]"}], "-", 
RowBox[{"8", " ", 
SuperscriptBox["b", "2"], " ", "g", " ", "\[Gamma]"}], "+", 
RowBox[{"2", " ", 
SuperscriptBox["b", "3"], " ", "g", " ", "\[Gamma]"}], "-", 
RowBox[{"6", " ", "g", " ", 
SuperscriptBox["\[Gamma]", "2"]}], "+", 
RowBox[{"8", " ", "b", " ", "g", " ", 
SuperscriptBox["\[Gamma]", "2"]}], "-", 
RowBox[{"4", " ", 
SuperscriptBox["b", "2"], " ", "g", " ", 
SuperscriptBox["\[Gamma]", "2"]}], "+", 
RowBox[{
SuperscriptBox["g", "2"], " ", 
SuperscriptBox["\[Gamma]", "2"]}], "-", 
RowBox[{"2", " ", "b", " ", 
SuperscriptBox["g", "2"], " ", 
SuperscriptBox["\[Gamma]", "2"]}], "+", 
RowBox[{"2", " ", 
SuperscriptBox["b", "2"], " ", 
SuperscriptBox["g", "2"], " ", 
SuperscriptBox["\[Gamma]", "2"]}]}]]},
{
FractionBox[
RowBox[{
RowBox[{
RowBox[{"-", "2"}], " ", "b", " ", "g"}], "+", 
RowBox[{"4", " ", 
SuperscriptBox["b", "2"], " ", "g"}], "-", 
RowBox[{"2", " ", 
SuperscriptBox["b", "3"], " ", "g"}], "-", 
RowBox[{"2", " ", "b", " ", "g", " ", "\[Gamma]"}], "+", 
RowBox[{"2", " ", 
SuperscriptBox["b", "2"], " ", "g", " ", "\[Gamma]"}], "-", 
RowBox[{"2", " ", "b", " ", 
SuperscriptBox["g", "2"], " ", "\[Gamma]"}], "+", 
RowBox[{"4", " ", 
SuperscriptBox["b", "2"], " ", 
SuperscriptBox["g", "2"], " ", "\[Gamma]"}], "-", 
RowBox[{"2", " ", 
SuperscriptBox["b", "3"], " ", 
SuperscriptBox["g", "2"], " ", "\[Gamma]"}], "-", 
RowBox[{"2", " ", "b", " ", 
SuperscriptBox["g", "2"], " ", 
SuperscriptBox["\[Gamma]", "2"]}], "+", 
RowBox[{"2", " ", 
SuperscriptBox["b", "2"], " ", 
SuperscriptBox["g", "2"], " ", 
SuperscriptBox["\[Gamma]", "2"]}]}], 
RowBox[{
RowBox[{"-", "2"}], "+", 
RowBox[{"4", " ", "b"}], "-", 
RowBox[{"2", " ", 
SuperscriptBox["b", "2"]}], "-", "g", "+", 
RowBox[{"3", " ", "b", " ", "g"}], "-", 
RowBox[{"4", " ", 
SuperscriptBox["b", "2"], " ", "g"}], "+", 
RowBox[{"2", " ", 
SuperscriptBox["b", "3"], " ", "g"}], "-", 
RowBox[{"3", " ", "\[Gamma]"}], "+", 
RowBox[{"4", " ", "b", " ", "\[Gamma]"}], "-", 
RowBox[{"2", " ", 
SuperscriptBox["b", "2"], " ", "\[Gamma]"}], "-", 
RowBox[{"5", " ", "g", " ", "\[Gamma]"}], "+", 
RowBox[{"11", " ", "b", " ", "g", " ", "\[Gamma]"}], "-", 
RowBox[{"8", " ", 
SuperscriptBox["b", "2"], " ", "g", " ", "\[Gamma]"}], "+", 
RowBox[{"2", " ", 
SuperscriptBox["b", "3"], " ", "g", " ", "\[Gamma]"}], "-", 
RowBox[{"6", " ", "g", " ", 
SuperscriptBox["\[Gamma]", "2"]}], "+", 
RowBox[{"8", " ", "b", " ", "g", " ", 
SuperscriptBox["\[Gamma]", "2"]}], "-", 
RowBox[{"4", " ", 
SuperscriptBox["b", "2"], " ", "g", " ", 
SuperscriptBox["\[Gamma]", "2"]}], "+", 
RowBox[{
SuperscriptBox["g", "2"], " ", 
SuperscriptBox["\[Gamma]", "2"]}], "-", 
RowBox[{"2", " ", "b", " ", 
SuperscriptBox["g", "2"], " ", 
SuperscriptBox["\[Gamma]", "2"]}], "+", 
RowBox[{"2", " ", 
SuperscriptBox["b", "2"], " ", 
SuperscriptBox["g", "2"], " ", 
SuperscriptBox["\[Gamma]", "2"]}]}]]}
},
DefaultBaseStyle->"Column",
GridBoxAlignment->{"Columns" -> {{Left}}, "ColumnsIndexed" -> {}, "Rows" -> {}, "RowsIndexed" -> {}, "Items" -> {}, "ItemsIndexed" -> {}},
GridBoxItemSize->{"Columns" -> {{Automatic}}, "ColumnsIndexed" -> {}, "Rows" -> {{Automatic}}, "RowsIndexed" -> {}, "Items" -> {}, "ItemsIndexed" -> {}},
GridBoxSpacings->{"Columns" -> {{Automatic}}, "ColumnsIndexed" -> {}, "Rows" -> {{1}}, "RowsIndexed" -> {}, "Items" -> {}, "ItemsIndexed" -> {}}],
"Column"]\);


(* Initialize manipulate *)
{b0,g0,gammaB0,gammaC0}=Rationalize[#,1/1000]&/@({b,g,gammaB,gammaC}/.sol)


(* check dual feasibility of fsol *)
algsI=algsI3
constrExtra={};
Manipulate[
    {tb,tgammaB,tgammaC}={pb,pgammaB,pgammaC}; (* allow saving of modifications *)
	params={b->pb,gammaB->pgammaB,gammaC->pgammaC,g->pg};
    {ToDual[algs[[algsI3]],varD1,varD2]/.fsol/.params,
	(*Total[u[#]*allMass[[algsI3[[#]]]]&/@Range[Length@algsI3]]/Total[u[#]&/@Range[Length@algsI3]]/.fsol/.params//N*)
	Grid@EvaluateDual[Join[fsol/.params,params]//N,algsI6sym]}
   ,{{pb,b0},0,1,1/1000},{{pgammaB,gammaB0},1/1000,3/2,1/1000},{{pgammaC,gammaC0},1/100,1,.1/100}
	,{{pg,g0},1/100,1,1/100}
   ]


{b0,gammaB0,gammaC0}={tb,tgammaB,tgammaC} (* optionally persist modifications *)


(* These are the inequalities we must prove, for dual feasibility. *)
Column[ToDual[algs[[algsI3]],varD1,varD2][[1,2]],Spacings->2]


(* Let's apply our solution. Manually multiply both sides of each eq by the denominator to help M out.*)
hardFeasConstr1=( FullSimplify[#/.fsol, {0<b<1,0<g<1,gammaB>0}]&/@
			ToDual[algs[[algsI3]],varD1,varD2][[1,2]] )~Select~(Not@TrueQ@#&)


(* We see many of the constraints M can directly simplify to True. Of the remaining, most require condition: *)
feasZoneReq1=(1-g)*gammaB<=b
FullSimplify[hardFeasConstr1,{0<b<1,0<g<1,gammaB>0,feasZoneReq1}]~Select~(Not@TrueQ@#&)
(* This leaves one remaining inequality, which is a non negativity constraint for u[1] = Li-Sven. *)
feasZoneReq2=%[[1]];
(* We can now visualize the region for which this dual form is feasible *)
RegionPlot3D[And[feasZoneReq1,feasZoneReq2],{b,0,1},{gammaB,0,2},{g,0,1},AxesLabel->Automatic]


(* infeasibility zone worst cost is 1.274 , so seems safely away from the critical area.*)
sol1=SolveNLP[ghat,300,algsI,{(1-g) gammaB>=b}]
sol2=SolveNLP[ghat,300,algsI,{gammaB<=g (1+2 b^2+gammaB+(-2+g) gammaB^2-b (3+gammaB))}]


(* ::Subsubsection::Closed:: *)
(*Explore DUAL - combining the F1=0 cases*)


BigFractionStyle = Style[#, DefaultOptions -> {FractionBoxOptions -> {AllowScriptLevelChange -> False}}] &;
algsI=algsI5
constrExtra={};
Manipulate[
    {tb,tgammaB,tgammaC}={pb,pgammaB,pgammaC}; (* allow saving of modifications *)
    msolDual = SolveDualLP[{b->pb,gammaB->pgammaB,gammaC->Min[1,pgammaB],g->pg},algsI(*,{u[i1]>=eps1}*)];
	mtmp=Total[u[#]*allMass[[algsI[[#]]]]&/@{i1,i2,3}]/Total[u[#]&/@{i1,i2,3}] /.msolDual;
    BigFractionStyle@Column@{N[alpha/.msolDual], Grid@EvaluateDual[msolDual,algsI],
	(* What mass would be needed to combine first and second algos *)
	{1 - (1-b)*g/(g*gammaB+1), 1 - (1-b)/(g*gammaB+1)},
	mtmp, mtmp[[5]]/mtmp[[4]],{algsI[[i2]],algsI[[i1]]},1/2(1+1/g)}/.msolDual
   (*,{{pb,b0},0,1,.001},{{pgammaB,gammaB0},.01,1.5,.001},{{pgammaC,gammaC0},.01,1,.001},{{pg,g0},.01,1,.001}*)
	,{{pb,2/3},0/60,1,1/12},{{pgammaB,2/3},0/60,1,1/12},{{pg,1/2},0/60,1,1/12}
   ,{eps1,0,1,.01},{i1,1,Length@algsI,1},{i2,1,Length@algsI,1}]


Protect[mu1,mu2]
partialDual2={
	 {mu1->1 - (1-b)*g/(g*gammaB+1), mu2->1 - (1-b)/(g*gammaB+1)}
	,{b->1/2, mu1->1 - 1/2 * g/(g*gammaB+1), mu2->1 - 1/2 * 1/(g*gammaB+1)}
	,{b->2/3, mu1->1 - 1/3 * g/(g*gammaB+1), mu2->1 - 1/3 * 1/(g*gammaB+1)}
	,{b->2/3, mu1->1 - 4/(12gammaB+12/g), mu2->1 - 48/(12g)/(12gammaB+12/g)}
	,{b->2/3, g->3/12, mu1->1 - 4/(12gammaB+48), mu2->1 - 16/(12gammaB+48)}
	,{b->2/3, g->4/12, mu1->1 - 4/(12gammaB+36), mu2->1 - 12/(12gammaB+36)}
	,{b->2/3, g->6/12, mu1->1 - 4/(12gammaB+24), mu2->1 - 8/(12gammaB+24)}
	,{b->2/3, g->8/12, mu1->1 - 4/(12gammaB+18), mu2->1 - 6/(12gammaB+18)}
};
params=partialDual2[[1]]
points=Table[{n,gammaB," ",#[[4]],mu1," "
                          ,#[[5]],mu2," "
				}/.params~Select~(MemberQ[{mu1,mu2},#[[1]]]&)&@(
		Total[u[#]*allMass[[algsI[[#]]]]&/@{1,2,3}] / Total[u[#]&/@{1,2,3}]
	)/.SolveDualLP[Append[#,gammaC->gammaB/.#]&[ params~Join~{b->2/3,gammaB->n/12,g->1/2} ],algsI]
,{n,1,11}];
BigFractionStyle@Grid@points


(* ::Subsubsection::Closed:: *)
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


(* ::Text:: *)
(**)


(* ::Section::Closed:: *)
(*Exact form*)


(* ::Subsection::Closed:: *)
(*Result*)


(* Exact form (for some critical region - see Exact Dual feasibility) found in Dual -> Automate Rational Form-Finding. Hard-coded here. *)
exactSolutionForm=(-2+4 b-2 b^2-g+b g-3 \[Gamma]+2 b \[Gamma]-5 g \[Gamma]+9 b g \[Gamma]-4 b^2 g \[Gamma]-6 g \[Gamma]^2+4 b g \[Gamma]^2+g^2 \[Gamma]^2)/(-2+4 b-2 b^2-g+3 b g-4 b^2 g+2 b^3 g-3 \[Gamma]+4 b \[Gamma]-2 b^2 \[Gamma]-5 g \[Gamma]+11 b g \[Gamma]-8 b^2 g \[Gamma]+2 b^3 g \[Gamma]-6 g \[Gamma]^2+8 b g \[Gamma]^2-4 b^2 g \[Gamma]^2+g^2 \[Gamma]^2-2 b g^2 \[Gamma]^2+2 b^2 g^2 \[Gamma]^2)
exactSolutionForm=exactSolutionForm/.\[Gamma]->gammaB;
Clear[SolveX]
SolveX[g1hat_,iter_:100]:=
	NMaximize[{Z, Z<=exactSolutionForm, 0<b<1, 0<gammaB, g==g1hat},{b,gammaB,g,Z}, MaxIterations->iter][[2]]
solX=SolveX[0.6586066,300]


(* ::Subsection::Closed:: *)
(*High Precision g*)


(*SetOptions[EvaluationNotebook[],CellContext->Notebook, PrintPrecision->22]
tpoints=Table[{g, NMaximize[{exactSolutionForm,0<b<1,0<gammaB},{b,gammaB},PrecisionGoal->15,AccuracyGoal->15,MaxIterations->10000][[1]]},{g,.65860655,.65860665,.00000001}]
ListPlot[tpoints]
SortBy[tpoints,Last][[1,1]]*)


(* ::Subsection::Closed:: *)
(*Analyze Maximum*)


(* ::Subsubsection::Closed:: *)
(*Maximize in gammaB*)


(* maximum should occur when either the derivative is zero, or at a boundary point *)
gammaBXVertex = Solve[D[exactSolutionForm,gammaB]==0,gammaB]//FullSimplify
gammaBXCrit = Join[gammaBXVertex,{{gammaB->0},{gammaB->Infinity}}]~Simplify~{0<b<1,0<g<=1};
(* restrict to real and non negative critical values of gammaB *)
gammaBXValid = Piecewise[{{Limit[exactSolutionForm,#[[1]]],Im[gammaB]==0&&gammaB>=0}/.#},-Infinity]&/@gammaBXCrit;
(*gammaBXMax = Max@@FullSimplify[gammaBXValid,{0<b<1,0<g}]*) (* It erroneously simplifies away the "Real" check *)
Plot3D[Max@@gammaBXValid,{b,0.001,1},{g,0.001,1}]


solX = SolveX[ghat,1000]
gammaB/.gammaBXCrit/.solX (* looks like opts occurs at 2nd critical point *)
(*Plot3D[gammaBXValid,{b,0.6,.75},{g,0.4,.9},PlotStyle->{Read,Green,Blue,Purple},PlotRange->{1.29,1.32}]*) (* confirm *)
optXbg = FullSimplify[exactSolutionForm/.gammaBXCrit[[2]],{0<b<1,0<g<=1}]
optXbgRegion = Simplify[(Im[gammaB]==0&&gammaB>=0)/.gammaBXCrit[[2]],{0<b<1,0<g<=1}]
Plot3D[{optXbg,Z/.solX},{b,0.55,.75},{g,0.3,.9},RegionFunction->Function[{b,g,Z},optXbgRegion]]
gammaB/.gammaBXCrit[[2]]/.solX (* note we are well away from zero - opt doesn't lie on boundary *)
D[optXbg,{g,2}]; (* too complex to try to solve closed form for g *)
(* the function is like a mountain pass: there's a single choke point, so setting g there is enough (vs as f(b)) *)


(* ::Subsubsection::Closed:: *)
(*Maximize in g*)


(* Suppose we fix gamma and let the adversary set g. Complicating factor: adversary may also set gamma_max. Ignore for now *)
gXVertex = Solve[D[exactSolutionForm,g]==0,g]~FullSimplify~{gammaB>0,0<b<1};
(*gXDeterminant = Cases[g/.gXVertex, Power[_, 1/2], Infinity][[-1]]*)
gXCrit = Join[gXVertex,{{g->0},{g->1}}]~Simplify~{0<b<1,0<gammaB}
gXValid = Piecewise[{{Limit[exactSolutionForm,#[[1]]],Im[g]==0&&g>=0}/.#},-Infinity]&/@gXCrit;
(*Plot3D[gXValid,{b,0.001,1},{gammaB,0.001,1.5},PlotStyle->{Red,Blue,Green,Purple}]*) (* Second critical point achieves max *)
Plot3D[{gXValid[[2]],Z/.solX},{b,0.65,.69},{gammaB,0.45,.6}] (* Another saddle point. *)


(* ::Subsubsection::Closed:: *)
(*Maximize in b*)


bXVertex = Solve[D[exactSolutionForm,b]==0,b]; (* 3 cubic solutions *)
bXCrit = Join[bXVertex,{{b->0},{b->1}}];
(*bXValid = Piecewise[{{exactSolutionForm,Im[b]==0&&b>=0}/.#},-Infinity]&/@bXCrit;*) (*M hangs trying to plot this*)
(*bplotX=Plot3D[exactSolutionForm/.bXCrit[[#]],{g,0.001,1},{gammaB,0.001,1.2}
	,PlotStyle->{Red,Blue,Green,Purple,Cyan}[[#]]]&/@Range[5]*) (*Takes awhile but works. first sol is usually max *)
bplotN=Plot3D[NMaximize[{exactSolutionForm,0<b<1},{b}][[1]],{g,0.001,1},{gammaB,0.001,1.2}] (*easier to just maximize numerically*)


Show[bplotN, Plot3D[Z/.solX,{g,0.001,1},{gammaB,0.001,1.2},PlotStyle->{Orange,Opacity[.6]}]]


(* ::Subsection::Closed:: *)
(*Randomization*)


(* Can we use exact form to randomize or discretize? Assume for now we can handle the infeasible regions elsewhere *)
(* Requires 'exactSolutionForm' from Dual Result section *)
(* This doesn't seem to improve things *)
optX=exactSolutionForm
Manipulate[
	tsol3=NMaximize[{Z,(Z<=optX/.{g->#[[1]],gammaB->#[[2]]}&)/@{{ghat1,gam1},{ghat2,gam2}},
		0<b<1,ghat1<=ghat2<=1,gam1>=gam2>0}
		,{Z,b,gam1,gam2}][[2]]~Join~{g1->ghat1,g2->ghat2}
,{{ghat1,.642},0.001,1},{{ghat2,.833},0.001,1}]


{feasZoneReq1,feasZoneReq2}/.{gammaB->gam1,g->g1}/.tsol
{feasZoneReq1,feasZoneReq2}/.{gammaB->gam2,g->g2}/.tsol


(* As would be expected, adding a 3rd point also doesn't help. This approach is just too weak. Perhaps
   because it doesn't take advantage of relationship between d-variables in the different sets? Or do we 
   actually need algorithms which don't meet this form (e.g. that specialize in FB2 or FB3, etc.) *)
Manipulate[
	tsol3=NMaximize[{Z,(Z<=optX/.{g->#[[1]],gammaB->#[[2]]}&)/@{{ghat1,gam1},{ghat2,gam2},{ghat3,gam3}},
		0<b<1,ghat1<=ghat2<=ghat3<=1,gam1>=gam2>=gam3>0}
		,{Z,b,gam1,gam2,gam3}][[2]]~Join~{g1->ghat1,g2->ghat2,g3->ghat3}
,{{ghat1,.642},0.001,1},{{ghat2,.6586},0.001,1},{{ghat3,.833},0.001,1}]


(* ::Subsection::Closed:: *)
(*Randomization 2*)


(* even if we enforce total d-variable sums, it's not enough *)
D2opt=Total@varD2/.SolveLPatSol[SolveX[ghat,50]~Join~ {gammaC->.01},algsI]
Z/.SolveLPatSol[SolveX[ghat,50]~Join~ {gammaC->.01},algsI,{Total[varD2]==D2opt}]
Z/.SolveLPatSol[SolveX[ghat-.01,50]~Join~ {gammaC->.01},algsI,{Total[varD2]==D2opt}]
Z/.SolveLPatSol[SolveX[ghat+.01,50]~Join~ {gammaC->.01},algsI,{Total[varD2]==D2opt}]


(* ::Section::Closed:: *)
(*Other Exploration*)


(* ::Subsection::Closed:: *)
(*Do we smoothly and fully optimize for full range of parameters?*)


(* see what optimal value of b is for various gammas. If it's in small range, we can sometimes estimate it as a constant for simplicity. *)
solGrid=ParallelTable[SolveNLP[ghat,250,algsI,{gammaB==gb}],{gb,.1,.9,.05}];
ListPlot[{gammaB,b}/.#&/@solGrid] (* b is usually around .67 *)


(* the extra d-constraints arent immediately valid, but necessary to smooth out small gamma region. to make valid, we would need to split clients into multiple classes, according to which facility is closest *)
Table[Plot[Z-.32tb/.SolveLPatSol[{g->tg,b->tb,algsI,gammaB->.02,gammaC->.02},algsI6b,constrD1D2~Union~constrD1D2g],{tb,.3,.6}], {tg, .5, .7, .05}]


(*plotGrid=Table[Plot[{1.012,Z}/.SolveLPatSol[{g->.6586,b->.01,algsI,gammaB->gamma,gammaC->gamma},algsI6~Join~{i}],{gamma,0,1}],{i,1,8}]*)


sols3=ParallelTable[SolveLPatSol[{g->.6586,b->pb,gammaB->gamma,gammaC->Min[gamma,.9999]},All,constrD1D2~Union~constrD1D2g]
	,{gamma,0.011,1.2,.1},{pb,0.01,1,.04}]~Flatten~1;
points3={gammaB, b, Z}/.#&/@sols3;
plot3=ListPlot3D[points3,ColorFunction->(RGBColor[0,1,0]&),AxesLabel->{"gamma","b","Z"}];
plot3X=Plot3D[exactSolutionForm/.g->.6586,{gammaB,0,1.2},{b,0,1},ColorFunction->(RGBColor[0,0,1]&)];
Show[plot3,plot3X]



(* closed form is loose for b,gamma close to 1, and often invalid for b<.5 , even with d1/d2 constraints*)
sols3=ParallelTable[SolveLPatSol[{g->.6586,b->pb,gammaB->gamma,gammaC->Min[gamma,.9999]},All
	(*,constrD1D2~Union~constrD1D2g*)],{gamma,0.011,1.2,.05},{pb,0.01,1,.04}]~Flatten~1;
pointsDel={gammaB, b, exactSolutionForm - Z}/.#&/@sols3;
Max[#[[2]]&/@Select[pointsDel,#[[3]]<-10^-10&]]
plot3=ListPlot3D[pointsDel,AxesLabel->{"gamma","b","Z"},PlotRange->{-.001,.001}]



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
{b0,g0,gammaB0,gammaC0}=Rationalize[{b,g,gammaB,gammaC}/.sol,1/1000];


(* we can compare closed form solution... it is loose or invalid in some edge cases *)
algsI={-1,29,30,31,32,33,37}
Manipulate[Module[{sol2},
{tb,tgammaB,tgammaC,tg}={pb,pgammaB,pgammaC,pg}; (* allow saving of modifications *)
sol2 = SolveLPatSol[{b->pb,gammaB->pgammaB,gammaC->pgammaC,g->pg},algsI(*~Union~{6,1,5,27}*),constrD1D2~Union~constrD1D2g];
Column@{Grid@{{"Closed form",#,N@#}&[exactSolutionForm/.sol2],{"LP sol",#,N@#}&[Z/.sol2]},sol2,EvaluateAlgsByMass[sol2,algsI]}
],{{pb,b0},0,1,1/1000},{{pgammaB,gammaB0},1/1000,3/2,1/1000},{{pgammaC,gammaC0},1/1000,1,1/1000},{{pg,g0},1/1000,1,1/1000}]//N



{b0,gammaB0,gammaC0,g0}={tb,tgammaB,tgammaC,tg} (* persist modifications *)


algsI6sym
