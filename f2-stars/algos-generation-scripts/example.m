(* ::Package:: *)

(* ::Title:: *)
(*Example File*)


SetOptions[EvaluationNotebook[],CellContext->Notebook, PrintPrecision->9]


(* ::Section:: *)
(*Setting up the NLP:*)


(* ::Subsection::Closed:: *)
(*Creating Variables*)


createVar[symb_,num_]:=ToExpression[symb<>ToString[num]];
createVarAB[symb_,grp1_,num1_,grp2_,num2_]:=ToExpression[symb<>grp1<>ToString[num1]<>grp2<>ToString[num2]];

initialize[t_] := (
	n = t+1;
	inds = Range[n];
	gammaAs = createVar@@#&/@({"gammaA",#}&/@inds);
	gammaCs = createVar@@#&/@({"gammaC",#}&/@inds);
	gammaCs = gammaCs/.{gammaC1->1-Total[gammaCs[[2;;]]]};
	cond = Union[{0<=b<=1},0<=#<=1&/@gammaCs,MapThread[#1<=#2&,{gammaCs[[2;;]],gammaAs[[2;;]]}]];
);


(* ::Subsection::Closed:: *)
(*Client Costs*)


Cf1[d1_,d2_,p1_,p2_,g_]:=p2*d2+(1-p2)*d1+(1-p2)*(1-p1)*g*(d1+d2)
(* If \[Sigma]_X(i1)!=i2, then we may try connecting to both before falling back on \[Sigma]_Y(i1) *)
Cf1b[d1_,d2_,p1_,p2_,p3_,g1_,g2_]:=p2*d2+(1-p2)*d1+(1-p2)*(1-p1)*(p3*g1+(1-p3)(g2))*(d1+d2)

Pair[a_,b_]:=(Return[{a,b}]);

cost[ps_]:= (
	pAs = ps[[;;n]];pBs = ps[[n+1;;2*n]];pCs = ps[[2*n+1;;]] ;
	pairs = Flatten[Outer[Pair,Range[n],Range[n]],1];
	costs = Cf1[createVarAB["d1","A",#[[1]],"B",#[[2]]],createVarAB["d2","A",#[[1]],"B",#[[2]]],pAs[[#[[1]]]],pBs[[#[[2]]]],If[#[[1]]==1,1,1/createVar["g",#[[1]]-1]]]&/@pairs;
	costs = Union[costs,Cf1[createVarAB["d1","A",#[[1]],"C",#[[2]]],createVarAB["d2","A",#[[1]],"C",#[[2]]],pAs[[#[[1]]]],pCs[[#[[2]]]],If[#[[1]]==n,1 ,createVar["g",#[[1]]]]]&/@pairs];
	Return[Total[costs]];
);


(* ::Subsection::Closed:: *)
(*Get Algorithms*)


Get[FileNameJoin[{NotebookDirectory[], "One-g-mass-30.wl"}]];
Get[FileNameJoin[{NotebookDirectory[], "One-g-reduced-mass-22.wl"}]];
(*Get[FileNameJoin[{NotebookDirectory[], "Two-g-mass-864.wl"}]];
Get[FileNameJoin[{NotebookDirectory[], "Two-g-reduced-mass-166.wl"}]];*)


(* ::Subsection::Closed:: *)
(*Variables and Constraints:*)


t = 1;
initialize[t];


pairs= Flatten[Outer[Pair,Range[n],Range[n]],1];
varDAB = createVarAB["d1","A",#[[1]],"B",#[[2]]]&/@pairs;
varDAC = createVarAB["d1","A",#[[1]],"C",#[[2]]]&/@pairs;
varDB = createVarAB["d2","A",#[[1]],"B",#[[2]]]&/@pairs;
varDC = createVarAB["d2","A",#[[1]],"C",#[[2]]]&/@pairs;


Length@reducedMass
algs=cost@@{#}&/@reducedMass;
algsWithMass={cost@@{#},{#}}&/@reducedMass;
constrAlg = X<=#&/@algs;


varD1=Union[varDAB,varDAC];
varD2=Union[varDB,varDC];
vars=Union[varD1,varD2,{X,b},gammaAs[[2;;]],gammaCs[[2;;]]];
constrBasic = Join[{X>=1},#>=0&/@Union[varD1,varD2],cond,{Total[varD1]*(1-b)+Total[varD2]*b==1}];
constrAlgLiSven = X<=b*(3-2b)Total[varD2]+(1-b)*Total[varD1];


(* ::Text:: *)
(*We will fix the value of g1,g2, and let the adversary set the mass variable gamma*)


g1hat= 0.6;
algsI=Range[Length[reducedMass]];
Length@algsI


(* ::Subsection::Closed:: *)
(*Define NLP*)


hints1 = Join[{.3 <= b <= .8, .01 <= gammaA2 <= .99, X>=.5, (* manual hints *)
		.01<=gammaC2<=.99, .01<=gammaC2(* hints *)}];
gs = {g1};


(* TODO allow specify starting point? *)
Clear@SolveNLP
SolveNLP[ghats_,iter_,hints_,algI_:;;]:=
	NMaximize[Union[{X, constrAlg[[algI]], constrBasic, constrAlgLiSven, hints},MapThread[#1==#2&,{gs,ghats}]],
	vars~Union~gs, MaxIterations->iter][[2]]
(*SolveNLP[g1hat,g2hat,100]*)


(* ::Section::Closed:: *)
(*Result*)


algsI
Length@algsI
{g1hat}
sol=SolveNLP[{g1hat},1000,hints1,algsI]
(*SolveLPatSol[sol,algsI]*)



