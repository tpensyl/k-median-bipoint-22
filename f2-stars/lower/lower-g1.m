(* ::Package:: *)

(* ::Subsection:: *)
(*Notebook Settings*)


SetOptions[EvaluationNotebook[],CellContext->Notebook, PrintPrecision->9]
SetOptions[Plot3D, AxesLabel->Automatic,
	PlotStyle->Opacity[.7], ClippingStyle->None,
	BoundaryStyle -> Directive[Black, Thick]];
Import@FileNameJoin[{ParentDirectory[NotebookDirectory[]],"util","visualizeMass.m"}]
VisualMass2[p_List,opts___]:=VisualMass[Join[{0,0},p][[{1,3,2,4,5,6}]],2,opts]


(* ::Subsection::Closed:: *)
(*Description:*)


(* ::Text:: *)
(*Consider the case where all g_i are uniform. This means we may take advantage of the g-bounds in both directions, for all i_1.*)


(* ::Subsection:: *)
(*Setting up the NLP:*)


(* ::Subsubsection::Closed:: *)
(*Client Costs*)


(* ::Text:: *)
(*Client cost is bounded by*)
(*	p[i2]*d2 + p[i2']*d1 + p[i2'i1']*d(i1,i3)*)
(*where i3 is either \[Sigma]_X(i1) or \[Sigma]_Y(i1). The bound used for d(i1,i3) varies by client type, but is always some constant times (d1+d2).*)


varD1={d1a2b2,d1a2c1,d1a2c2}; (* ex d1_a2 _c2 is between a2 and c2 *)
varD2={d2a2b2,d2a2c1,d2a2c2};

Cf1[d1_,d2_,p1_,p2_,g_]:=p2*d2+(1-p2)*d1+(1-p2)*(1-p1)*g*(d1+d2)
(* If \[Sigma]_X(i1)!=i2, then we may try connecting to both before falling back on \[Sigma]_Y(i1) *)
(*Cf1b[d1_,d2_,p1_,p2_,p3_,g1_,g2_]:=p2*d2+(1-p2)*d1+(1-p2)*(1-p1)*(p3*g1+(1-p3)(g2))*(d1+d2)*)

costSplit[pa2_,pb2_,pc1_,pc2_] := {
	Cf1[d1a2b2,d2a2b2,pa2,pb2,1/g],   (* J_a2 _b2  : a2 and b2 *)
    Cf1[d1a2c1,d2a2c1,pa2,pc1,g],
    Cf1[d1a2c2,d2a2c2,pa2,pc2,g]
}
cost[pa2_,pb2_,pc1_,pc2_] := Total@costSplit[pa2,pb2,pc1,pc2]

costLiSven = b*(3-2b)Total[varD2]+(1-b)*Total[varD1];


(* ::Subsubsection::Closed:: *)
(*Probability Mass*)


CheckMass[mass_]:=FullSimplify@Simplify[{gammaA2,gammaA2,1-gammaC2,gammaC2}.(mass-{a,b,b,b})/.{a->1-b},
	{0<=b<=1,0<gammaA2,0<gammaC2<1,gammaC2<=gammaA2}]


inputFile=FileNameJoin[{NotebookDirectory[],"data","g1-lower-mass-22.json"}];
rawMass = Map[ToExpression,#,{2}]&["massAll"/.Import[inputFile]];
CheckMass/@rawMass (* check if the mass balances; it should equal zero *)
massLiSven={1-b,b,b,b};


(* ::Subsubsection::Closed:: *)
(*Handcrafted Hybrid Algorithms*)


hybridMass={
	{1,0,b,b},
	{1,Min[1,b/gammaA2],x2,x2}/.x2->Max[0,b-gammaA2],
	{0,1,b,b},
	{0,x2,x1,x1}/.{x2->1-Min[(1-b)/gammaA2,b/Max[b,1-gammaA2]],x1->b/Max[b,1-gammaA2]}
};
CheckMass/@hybridMass (* check if the mass balances; it should equal zero *)


(* ::Subsubsection::Closed:: *)
(*Variables and Constraints:*)


rawMass2=Join[rawMass,hybridMass];
algs=Prepend[cost@@#&/@rawMass2,costLiSven];
mass=Prepend[rawMass2,massLiSven];

algsWithMass=Table[{algCost->algs[[i]],algMass->mass[[i]],algIndex->i},{i,1,Length@mass}];
constrAlg = Z<=#&/@algs;

varNonLin = Union[{gammaA2,gammaC2,b,g}];
vars=Union[varD1,varD2,{Z},varNonLin];
(*constrD1D2=MapThread[#1<=#2&,{varD2,varD1}];*)
constrBasic = Join[{Z>=0,0<=b<=1,0<g<=1},#>=0&/@Union[varD1,varD2,{gammaA2,gammaC2}]
	,{gammaC2<=gammaA2,gammaC2<=1, Total[varD1]*(1-b)+Total[varD2]*b==1}];


(* ::Subsubsection::Closed:: *)
(*Utility Methods*)


(* Show tight algorithms *)
StyleMass[mass_]:=Style[mass,PrintPrecision->2]
EvaluateAlgs[params_,algIset_:;;]:=(
		{algCost, algMass//StyleMass, VisualMass2[algMass,ImageSize->{90,45}], algIndex}/.#&/@algsWithMass[[algIset]]
	)/.params
EvaluateAlgsByCost[params_,algIset_:;;]:=Grid[SortBy[EvaluateAlgs[params,algIset],First]~Prepend~{"Alg Cost ", "Alg Mass","Alg Index"},Alignment->Left]
EvaluateAlgsByMass[params_,algIset_:;;]:=Grid[SortBy[EvaluateAlgs[params,algIset],#[[2]]&]~Prepend~{"Alg Cost ", "Alg Mass","Alg Index"},Alignment->Left]
EvaluateAlgsByIndex[params_,algIset_:;;]:=Grid[SortBy[EvaluateAlgs[params,algIset],#[[3]]&]~Prepend~{"Alg Cost ", "Alg Mass","Alg Index"},Alignment->Left]


(* ::Subsubsection::Closed:: *)
(*Define NLP*)


(* type checking: needed for multiple optional arguments and generally helpful for debugging *)
IndexQ[i_]:=(i==All || i==(1;;All) || And@@IntegerQ/@i) (* allow passing ;; or All for index subset *)
EquationQ[eq_]:=Not@FreeQ[eq,(Equal|LessEqual|Less|Greater|GreaterEqual)]||eq (* contains one of =,<,<=,>,>=, or trivially true *)

defaultHints={};
SolveNLP[iter_,algI_,constrExtra:{___?EquationQ}:defaultHints]:=
	NMaximize[{Z, constrAlg[[algI]], constrBasic, constrExtra
	}, vars, MaxIterations->iter][[2]]
SolveNLP[iter_,algI_:;;]:=SolveNLP[g1hat,iter,algI,{}]

(* If we fix non-linear variables, remaining system is linear and very fast/accurate *)
SolveLP[nonLinParams_,algI:_?IndexQ:All,constrExtra:{___?EquationQ}:{}]:=
	Maximize[{Z, constrAlg[[algI]], constrBasic, constrExtra}/.nonLinParams,
		Union[varD1,varD2,{Z}]][[2]]~Join~nonLinParams;
SolveLPatSol[fullSol_,algI:_?IndexQ:All,constrExtra:{___?EquationQ}:{}]:=SolveLP[ExtractNonLin[fullSol], algI,constrExtra]
ExtractNonLin[sol_]:=Select[sol,MemberQ[varNonLin,#[[1]]]&]

createVar[terms__]:=ToExpression@StringJoin@@ToString/@List[terms]


(* ::Subsection:: *)
(*Solving the NLP*)


algsI4sym={1,16,17,18,19};
solNLP=SolveNLP[1000,algsI4sym]


SolveLPatSol[solNLP,All]


sol1={b->0.6800467217296743`,d1a2b2->0.7221789990503936`,d1a2c1->0.3083614625762051`,d1a2c2->0.657366263186447`,d2a2b2->0.2893790360526419`,d2a2c1->0.123561253926822`,d2a2c2->0.2634084010370487`,g->0.5001915247579782`,gammaA2->0.7478080814766489`,gammaC2->0.6806952373022075`,Z->1.2943241958108767`};
sol2={d1a2b2->0.7221789677811981`,d1a2c1->0.7074147297606694`,d1a2c2->0.2583130741405334`,d2a2b2->0.28937904450669083`,d2a2c1->0.28346297490130995`,d2a2c2->0.1035067399240481`,Z->1.2943241953196447`,b->0.6800467825706328`,g->0.999999999882676`,gammaA2->0.7478079899766032`,gammaC2->0.2674802082916519`};
EvaluateAlgsByMass[sol2,algsI4sym]


(* ::Section:: *)
(*Dual*)


(* ::Subsection::Closed:: *)
(*Define*)


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
	Table[{u[i], algMass//StyleMass, VisualMass2[algMass,ImageSize->{90,45}],
			 algIndex, i}/.algsWithMass[[algIset[[i]]]],{i,1,Length[algIset]}]
]/.params



algsI=algsI4sym
solDual=SolveDualLP[solNLP,algsI]
Grid@EvaluateDual[%,algsI] 


(* ::Subsection:: *)
(*Explore Dual*)


(* ::Subsubsection:: *)
(*Manipulate*)


BigFractionStyle = Style[#, DefaultOptions -> {FractionBoxOptions -> {AllowScriptLevelChange -> False}}] &;
algsI=algsI4sym; sol=solNLP;
constrExtra={};
{b0,g0,gammaA20,gammaC20}={b,g,gammaA2,gammaC2}/.sol;
Manipulate[Module[{msolDual,msolOptBaseline,mCombo},
	mparamsg1 = {b->pb,gammaA2->pgammaA2,gammaC2->pgammaC2,g->pg};
    msolDual = SolveDualLP[mparamsg1,algsI,Join[u[#]==0&/@removeI,(u[#]>=eps1&)/@forceI]];
	msolOptBaseline = alpha/.SolveDualLP[mparamsg1,Range@Length@algs];
	mCombo=Total[u[#]*mass[[algsI[[#]]]]&/@comboI]/Max[.0001,Total[u[#]&/@comboI]];
    BigFractionStyle@Column@{Row@{msolOptBaseline,"(Baseline)"},alpha, {algsI[[comboI]],mCombo},
		{b/(1+gammaA2),(b+gammaA2)/(1+gammaA2)},VisualMass2[mCombo,ImageSize->{80,80}]
		, Grid@Select[SortBy[EvaluateDual[msolDual,algsI],#[[2]]&],Chop[#[[1]]]!=0&]}/.msolDual
   ],{{pb,b0},0,1,1/100.},{{pgammaA2,gammaA20},1/1000,3/2,1/100.},{{pgammaC2,gammaC20},1/100,1,1/100},{{pg,g0},1/100,1,1/100.}
   ,{{eps1,.01},0,1,1/100.},{{removeI,{}}},{{comboI,{2,3}(*Range[Length@algsI][[2;;]]*)}},{{forceI,{}}}]


save2=mparamsg1 (* optionally save modifications *)


(* ::Subsubsection:: *)
(*Automate rational form-finding*)


(* Example: here we parameterized terms have combined algorithms, in terms of gammaB.
   We can then follow up and look in terms of g and b, and try to combine them *)
(* TODO taken the parameters as an argument, with the ability to template out variable; maybe even specify range *)
Clear[MergeAlgos]
MergeAlgos[algsI_List, algsII_List, form_]:=Module[{data,fits,forms},
	data=Transpose@Flatten[Table[
		Join[
			{gammaC2,b,g,alpha-1,u[1],u[2],u[3],u[4],u[5]},
			Total[u[#]*mass[[algsI[[#]]]]&/@algsII] / Total[u[#]&/@algsII]
		]/.SolveDualLP[Append[#,gammaC2->gammaA2/.#]&[ {b->75/100,gammaA2->85/100,g->tg} ],algsI]
	,{tg,90/100,91/100,1/100/6}],0];
	fits=Table[
		Solve@MapThread[#4==form/.{gammaA2->#1,b->#2,g->#3}&,{data[[1]],data[[2]],data[[3]],yRow}]
	,{yRow,data}]; (*Print[fits];*)
	forms=Table[If[fit=={},"WRONG FORM",form/.fit[[1]]], {fit,fits}];
	Column@ExpandDenominator@ExpandNumerator@Simplify@forms
]
algsItemp=algsI4sym;
form=Sum[v[1,i]*x^i,{i,0,2}]/
     Sum[v[2,i]*x^i,{i,0,2}]/. {v[2,0]->1, x->g}
MergeAlgos[algsItemp,{2,3,4,5},form]


(* Detect 2 vars *)
Clear[MergeAlgos]
MergeAlgos[algsI_List, algsII_List, form_]:=Module[{data,fits,forms},
	data=Transpose@Flatten[Table[
		Join[
			{gammaA2,b,g,alpha-1,u[1],u[2],u[3],u[4],u[5]},
			Total[u[#]*mass[[algsI[[#]]]]&/@algsII] / Total[u[#]&/@algsII]
		]/.SolveDualLP[Append[#,gammaC2->gammaA2/.#]&[ {b->tb,gammaA2->tgammaB,g->1} ],algsI]
	,{tgammaB,78/100,79/100,1/100/4},{tb,68/100,69/100,1/100/5}],1];
(*Print[data];*)
	fits=Table[
		Solve@MapThread[#4==form/.{gammaA2->#1,b->#2,g->#3}&,{data[[1]],data[[2]],data[[3]],yRow}]
	,{yRow,data}]; (*Print[fits];*)
	forms=Table[If[fit=={},"WRONG FORM",form/.fit[[1]]], {fit,fits}];
	Column@ExpandDenominator@ExpandNumerator@Simplify@forms
]
algsItemp=algsI4sym;
Protect[v];
form=Sum[v[1,i,j]*x^i*y^j,{i,0,2},{j,0,3}]/
	 Sum[v[2,i,j]*x^i*y^j,{i,0,2},{j,0,3}]/. {v[2,0,0]->1, x->gammaA2, y->b};
{time,result}=Timing@MergeAlgos[algsItemp,{4,5},form]/.gammaA2->\[Gamma]


(* Detect all 3 vars. *)
Clear[MergeAlgos]
MergeAlgos[algsI_List, algsII_List, form_]:=Module[{data,fits,forms},
	data=Transpose@Flatten[Table[
		Join[
			{gammaA2,b,g,alpha-1,u[1],u[2],u[3],u[4]},
			Total[u[#]*mass[[algsI[[#]]]]&/@algsII] / Total[u[#]&/@algsII]
		][[{1,2,3,4}]]/.SolveDualLP[Append[#,gammaC2->gammaA2/.#]&[ {b->tb,gammaA2->tgammaB,g->tg} ],algsI]
	,{tgammaB,84/100,85/100,1/100/4},{tb,76/100,77/100,1/100/5},{tg,89/100,90/100,1/100/4}],2];
	fits=Table[
		Solve@MapThread[#4==form/.{gammaA2->#1,b->#2,g->#3}&,{data[[1]],data[[2]],data[[3]],yRow}]
	,{yRow,data}]; (*Print[fits];*)
	forms=Table[If[fit=={},"WRONG FORM",form/.fit[[1]]], {fit,fits}];
	Column[ExpandDenominator@ExpandNumerator@Simplify@forms,Spacings->1]
]
algsItemp=algsI4sym;
Protect[v];
form=Sum[v[1,i,j,k]*x^i*y^j*z^k,{i,0,2},{j,0,3},{k,0,2}]/
	 Sum[v[2,i,j,k]*x^i*y^j*z^k,{i,0,2},{j,0,3},{k,0,2}]/. {v[2,0,0,0]->1, x->gammaA2, y->b, z->g};
{time,result}=Timing@MergeAlgos[algsItemp,{2,3,4,5},form]/.gammaA2->\[Gamma];
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


(* ::Subsubsection:: *)
(*Scratch*)


exactg1=(2 b \[Gamma]-2 b^2 \[Gamma])/(1-3 b+2 b^2+2 \[Gamma]-3 b \[Gamma]+2 b^2 \[Gamma]+\[Gamma]^2)
exactg2=(2 b \[Gamma]-2 b^2 \[Gamma])/(2-4 b+2 b^2+3 \[Gamma]-4 b \[Gamma]+2 b^2 \[Gamma])


Maximize[{X,X<=exactg1,X<=exactg2,0<b<1,1>\[Gamma]>1/2},{b,\[Gamma],X}]//FullSimplify
%//N



