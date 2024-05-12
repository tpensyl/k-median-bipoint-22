(* ::Package:: *)

On[Assert]
SetOptions[EvaluationNotebook[],CellContext->Notebook, PrintPrecision->7]


phi=(1+Sqrt[5])/2;


(* ::Text:: *)
(*GOAL of this specific file is to get gap instances  in terms of b, for optimal use with bi-point generation factor which is given in terms of b.*)


(* ::Section:: *)
(*True Integrality App*)


(* ::Text:: *)
(*Let's define family of bipartite solutions:*)
(*In this family, we separate leaves (F2) into F2A and F2B. Let JA, JB be clients connected to them. *)
(*gamma:= |F1|/|F2B|.    (We already have |F2A|=|F1|)*)


polytope[gamma_] = {
	{p1,p2a,p2b} . {gamma,gamma,1}=={1-b,b,b} . {gamma,gamma,1},
	0<=p1<=1, 0<=p2a<=1, 0<=p2b<=1
};
extremePoints = {
	(*{1-b,b,b},*)
	(*{1,b/(1+gamma),b/(1+gamma)},*)
	{0,Max[0,1-(1-b)/gamma],Min[1,b+gamma]},
	{Max[0,1-(1-b)/gamma],0,Min[1,b+gamma]},
	{0,1,b},
	{1,0,b},
	{1,Min[1,b/gamma],Max[0,b-gamma]},
	{Min[1,b/gamma],1,Max[0,b-gamma]}
};
AssertValidPoint[mass_]:=(*Assert[*)
	FullSimplify[
		k = {1-b,b,b} . {gamma,gamma,1};
		mass . {gamma,gamma,1}==k
	,{0<gamma,0<=b<=1}]
(*]*)
AssertValidPoint/@extremePoints


(* ::Text:: *)
(*d(F1,F2A)=g    d(F1,F2B)=1*)
(**)
(*F2A represents the leaves which are sparsely connected, so if i1 and i2 are closed, their closest 3rd facility is in F2B, at distance d1+1/g*(d1+d2).*)
(**)
(*F2B is leaves which are highly connected, and may always assume at least one f1 is open to allow for the F2-bound. BUT, they also have option 'of cheap' F1-bound at cost d1+g*(d1+d2).*)


CA[d1_,d2_,p1_,p2_]:=p2*d2 + Min[1-p2,p1]*d1 + Max[1-p1-p2,0](d1+1/g(d1+d2))
CB[d1_,d2_,p1_,p2_]:=p2*d2 + (1-p2)p1*d1 + (1-p2)(1-p1)(d1+Min[g(d1+d2),2d2])
PointCost[p1_,p2a_,p2b_]:=CA[d1a,d2a,p1,p2a] + CB[d1b,d2b,p1,p2b]


(* ::Text:: *)
(*Maximize over all parameters: *)


sol=NMaximize[{X,
	(X<=#&)/@(PointCost@@#&/@extremePoints),
	(d1a+d1b)(1-b)+(d2a+d2b)b==1,
	0<gamma, 0<=d1a, 0<=d2a, 0<=d1b, 0<=d2b, 0<b<1, 0<=g<=1
}
,{d1a,d2a,d1b,d2b,b,g,gamma,X},MaxIterations->200]
Sqrt[phi]//N
extremePoints/.sol[[2]]
PointCost@@#&/@extremePoints/.sol[[2]]


(* ::Text:: *)
(*Fix b and maximize over remaining parameters*)


FindGap[pb_,pMaxIterations_:100]:=NMaximize[{X,
	(X<=#&)/@(PointCost@@#&/@extremePoints),
	(d1a+d1b)(1-b)+(d2a+d2b)b==1,
	0<gamma, 0<=d1a, 0<=d2a, 0<=d1b, 0<=d2b, 0<=b<=1, 0<g<=1
}/.{b->pb}
,{d1a,d2a,d1b,d2b,g,gamma,X},MaxIterations->pMaxIterations]
FindGap[.673,500]


ListPlot[ParallelTable[{b,Quiet@FindGap[b][[1]]},{b,0,1,.02}]]


(* ::Section:: *)
(*Lower Bound Under Algorithm Restriction*)


(* ::Text:: *)
(*We consider the class of algorithms which only use d1+2d2 bound when (F1,F2) are open in proportion (a,b). In all other cases they use backup bound 2d1+d2. This is not a true lower bound on all algorithms but does give a stronger lower bound for the algorithms were currently considering in our golden paper with its hierarchies.*)
(**)
(*Using the same mass sets from above turns out to be overgeneralized. We can see adversary sets g=1, which effectively means that there is no difference between F2A,F2B - this means the same lower pound could be obtained by  could be modeled more simply as a single set F2.  Maybe it would be useful to also split F1, where one part does not have 1/g bound. (This thought comes just from trying to think of how to generalize the degree partitioning strategy to non homogeneous F1 bounds, in current thoughts about what a counterexample might be.) *)


extremePoints2 = {
	{1,b/(1+gamma),b/(1+gamma)},
	{0,Max[0,1-(1-b)/gamma],Min[1,b+gamma]},
	{Max[0,1-(1-b)/gamma],0,Min[1,b+gamma]},
	{0,1,b},
	{1,0,b},
	{1,Min[1,b/gamma],Max[0,b-gamma]}
};
AssertValidPoint/@extremePoints2


C2[d1_,d2_,p1_,p2_,g_]:=p2*d2 + (1-p2)p1*d1 + (1-p2)(1-p1)(d1+g(d1+d2))
PointCost2[p1_,p2a_,p2b_]:=C2[d1a,d2a,p1,p2a,1/g] + C2[d1b,d2b,p1,p2b,g]
LSCost:=(1-b)(d1a+d1b)+b(3-2b)(d2a+d2b)


(* ::Text:: *)
(*Maximize over all parameters: *)


sol2=NMaximize[{X,
	(X<=#&)/@Append[PointCost2@@#&/@extremePoints2,LSCost],
	(d1a+d1b)(1-b)+(d2a+d2b)b==1,
	0<gamma, 0<=d1a, 0<=d2a, 0<=d1b, 0<=d2b, 0<b<1, 0<=g<=1
}
,{d1a,d2a,d1b,d2b,b,g,gamma,X},MaxIterations->1000]
Sqrt[phi]//N


FindGap2[pb_]:=NMaximize[{X,
	(X<=#&)/@Append[PointCost2@@#&/@extremePoints2,LSCost],
	(d1a+d1b)(1-b)+(d2a+d2b)b==1,
	0<gamma, 0<=d1a, 0<=d2a, 0<=d1b, 0<=d2b, 0<=b<=1, 0<g<=1
}/.{b->pb}
,{d1a,d2a,d1b,d2b,g,gamma,X}]
FindGap2[.680]


range={b,0,1,.02}
ListPlot[{ParallelTable[{b,Quiet@FindGap[b][[1]]},range], 
	      ParallelTable[{b,Quiet@FindGap2[b][[1]]},range]}]


PointCost2@@#&/@extremePoints2/.sol2[[2]]
extremePoints2/.sol2[[2]]



