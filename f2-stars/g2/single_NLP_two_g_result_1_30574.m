(* ::Package:: *)

(* ::Title:: *)
(*F2-Stars*)


(* ::Subsection:: *)
(*Notebook Settings*)


SetOptions[EvaluationNotebook[],CellContext->Notebook, PrintPrecision->7]
SetOptions[Plot3D, AxesLabel->Automatic,
	PlotStyle->Opacity[.7], ClippingStyle->None,
	BoundaryStyle -> Directive[Black, Thick]];
Import@FileNameJoin[{ParentDirectory[NotebookDirectory[]],"util","visualizeMass.m"}]


(* ::Subsection::Closed:: *)
(*Description:*)


(* ::Text:: *)
(*i1, i2: Closest facilities in F1,F2 for client j.*)
(*Form F2 stars, connect each i \[Element] F1 to its closest i' \[Element] F2.*)
(*Let X be the set of facilities in F2 with at least one leaf. Add arbitrary facilities to X, if necessary, such that |F1|=|X|.*)
(*Let Y=F3 = F2 \[Dash] X.*)
(**)
(*Let \[Sigma]_X(i), \[Sigma]_Y(i) be the nearest facilities to i in X and Y, respectively.*)
(*For each i \[Element] F1, let *)
(*	g_i = d(i, X)/d(i, Y) = d(i,\[Sigma]_X(i)) / d(i,\[Sigma]_Y(i)).*)
(*	*)
(*Fix g1,g2, and let *)
(*	F11 \[LeftArrow] {x \[Element] F1 |  g_x < g1}*)
(*	F12 \[LeftArrow] {x \[Element] F1 |  g1<=g_x < g2}*)
(*	F13 \[LeftArrow] {x \[Element] F1 |  g_i >= g2}*)
(*	F21 \[LeftArrow] \[Sigma]_X(F11)*)
(*	F22 \[LeftArrow] \[Sigma]_X(F12)\[Dash] F21*)
(*	F23 \[LeftArrow] \[Sigma]_X(F13)\[Dash] F21\[Dash]F22*)
(*\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]	Arbitrarily assign rest of X such that |F11|=|F21|, |F12| = |F22|,|F13| = |F23|.*)
(*\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]	F33 = \[Sigma]_Y(F13)*)
(*	F32 = \[Sigma]_Y(F12)\[Dash]F33*)
(*	F31 = \[Sigma]_Y(F11)\[Dash]F33-F32*)
(*Let, *)
(*	\[Gamma]_12 = |F22|/|Y| = |F12|/|Y|*)
(*	\[Gamma]_13 = |F23|/|Y| = |F13|/|Y|*)
(*	\[Gamma]_32 = |F32|/|Y|  <= \[Gamma]_12*)
(*	\[Gamma]_33 = |F33|/|Y|  <= \[Gamma]_13*)
(*	Also, 0 <= \[Gamma]_32, \[Gamma]_33 <= 1*)


(* ::Subsection:: *)
(*Setting up the NLP:*)


(* ::Subsubsection::Closed:: *)
(*Client Costs*)


(* ::Text:: *)
(*Client cost is bounded by*)
(*	p[i2]*d2 + p[i2']*d1 + p[i2'i1']*d(i1,i3)*)
(*where i3 is either \[Sigma]_X(i1) or \[Sigma]_Y(i1). The bound used for d(i1,i3) varies by client type, but is always some constant times (d1+d2).*)


varD1 = {d111,d112,d113,d121,d122,d123,d131,d132,d133,d1131,d1132,d1133,d1231,d1232,d1233,d1331,d1332,d1333};
varD2 = {d211,d212,d213,d221,d222,d223,d231,d232,d233,d311,d312,d313,d321,d322,d323,d331,d332,d333};

Cf1[d1_,d2_,p1_,p2_,g_]:=p2*d2+(1-p2)*d1+(1-p2)*(1-p1)*g*(d1+d2)
(* If \[Sigma]_X(i1)!=i2, then we may try connecting to both before falling back on \[Sigma]_Y(i1) *)
Cf1b[d1_,d2_,p1_,p2_,p3_,g1_,g2_]:=p2*d2+(1-p2)*d1+(1-p2)*(1-p1)*(p3*g1+(1-p3)(g2))*(d1+d2)

(*## # Copy and paste from python script ## #*)
(* Let me know if I should consider some other notation, this is a little messy, especially the 'd' variables  *)
costSplit[p11_,p12_,p13_,p21_,p22_,p23_,p31_,p32_,p33_] := {
	Cf1[d111,d211,p11,p21,1],    (* J11  : F11 and F21 *)
	Cf1[d112,d212,p11,p22,1],    (* J12  : F11 and F22 *)
	Cf1[d113,d213,p11,p23,1],    (* J13  : F11 and F23 *)
	Cf1[d1131,d311,p11,p31,g1],  (* J1_ 31: F11 and F31 *)(* See d1131 as d1_ 1,31 *)
	Cf1[d1132,d312,p11,p32,g1],  (* J1_ 32: F11 and F32 *)
	Cf1[d1133,d313,p11,p33,g1],  (* J1_ 33: F11 and F33 *)
	Cf1[d121,d221,p12,p21,1/g1], (* J21  : F12 and F21 *)
	Cf1[d122,d222,p12,p22,1/g1], (* J22  : F12 and F22 *)
	Cf1[d123,d223,p12,p23,1 + (1/g1-1)*(1-Min[p22,p21])], (* J23  : F12 and F23 *)
	Cf1[d1231,d321,p12,p31,g2 + (1-g2)*(1-Min[p22,p21])],  (* J2_ 31: F12 and F31 *)
	Cf1[d1232,d322,p12,p32,g2 + (1-g2)*(1-Min[p22,p21])],  (* J2_ 32: F12 and F32 *)
	Cf1[d1233,d323,p12,p33,g2 + (1-g2)*(1-Min[p22,p21])],  (* J2_ 33: F12 and F33 *)
	Cf1[d131,d231,p13,p21,1/g2], (* J31  : F13 and F21 *)
	Cf1[d132,d232,p13,p22,1/g2], (* J32  : F13 and F22 *)
	Cf1[d133,d233,p13,p23,1/g2], (* J33  : F13 and F23 *)
	Cf1[d1331,d331,p13,p31,1],   (* J3_ 31: F13 and F31 *)
	Cf1[d1332,d332,p13,p32,1],   (* J3_ 32: F13 and F32 *)
	Cf1[d1333,d333,p13,p33,1]    (* J3_ 33: F13 and F33 *)
}
cost[p11_,p12_,p13_,p21_,p22_,p23_,p31_,p32_,p33_] := Total@costSplit[p11,p12,p13,p21,p22,p23,p31,p32,p33]

costLiSven = b*(3-2b)Total[varD2]+(1-b)*Total[varD1];


(* ::Subsubsection::Closed:: *)
(*Client Cost (Old)*)


(*the cost function  had a flaw in J2_ 31, J2_ 32, J2_ 33 , since a g2-bound may not always be available*)
costSplitOld[p11_,p12_,p13_,p21_,p22_,p23_,p31_,p32_,p33_] := {
	Cf1[d111,d211,p11,p21,1],    (* J11  : F11 and F21 *)
	Cf1[d112,d212,p11,p22,1],    (* J12  : F11 and F22 *)
	Cf1[d113,d213,p11,p23,1],    (* J13  : F11 and F23 *)
	Cf1[d1131,d311,p11,p31,g1],  (* J1_ 31: F11 and F31 *)(* See d1131 as d1_ 1,31 *)
	Cf1[d1132,d312,p11,p32,g1],  (* J1_ 32: F11 and F32 *)
	Cf1[d1133,d313,p11,p33,g1],  (* J1_ 33: F11 and F33 *)
	Cf1[d121,d221,p12,p21,1/g1], (* J21  : F12 and F21 *)
	Cf1[d122,d222,p12,p22,1/g1], (* J22  : F12 and F22 *)
	Cf1[d123,d223,p12,p23,1/g1], (* J23  : F12 and F23 *)
	Cf1[d1231,d321,p12,p31,g2],  (* J2_ 31: F12 and F31 *)
	Cf1[d1232,d322,p12,p32,g2],  (* J2_ 32: F12 and F32 *)
	Cf1[d1233,d323,p12,p33,g2],  (* J2_ 33: F12 and F33 *)
	Cf1[d131,d231,p13,p21,1/g2], (* J31  : F13 and F21 *)
	Cf1[d132,d232,p13,p22,1/g2], (* J32  : F13 and F22 *)
	Cf1[d133,d233,p13,p23,1/g2], (* J33  : F13 and F23 *)
	Cf1[d1331,d331,p13,p31,1],   (* J3_ 31: F13 and F31 *)
	Cf1[d1332,d332,p13,p32,1],   (* J3_ 32: F13 and F32 *)
	Cf1[d1333,d333,p13,p33,1]    (* J3_ 33: F13 and F33 *)
}
cost[p11_,p12_,p13_,p21_,p22_,p23_,p31_,p32_,p33_] := Total@costSplit[p11,p12,p13,p21,p22,p23,p31,p32,p33]

costLiSven = b*(3-2b)Total[varD2]+(1-b)*Total[varD1];


(* ::Subsubsection::Closed:: *)
(*Probability Mass*)


(* ::Text:: *)
(*Let A(p11,p12,p13,p21,p22,p23,p31,p32,p33) give proportions.*)


rawMass = {{0,Min[1,Max[0,(b - gamma13 - gamma32)/gamma12]],1,1,1,Min[1,Max[0,(b - gamma32)/gamma13]],Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,b/gamma32],Min[1,Max[0,(b - gamma12 - gamma13 - gamma32)/gamma33]]},
	{1,Min[1,Max[0,(b - gamma32 - gamma33)/gamma12]],Min[1,Max[0,(b - gamma12 - gamma32 - gamma33)/gamma13]],0,Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma12],Min[1,Max[0,(b + gamma13 - gamma32 - gamma33)/gamma13]],Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{0,Min[1,b/gamma12],1,1,1,0,Min[1,Max[0,(-b + gamma12 + gamma32)/(gamma32 + gamma33 - 1)]],Min[1,Max[0,(b - gamma12)/gamma32]],Max[0,(b - gamma12 + gamma33 - 1)/gamma33]},
	{1,1,Min[1,(b + gamma13 - gamma33)/gamma13],0,0,Min[1,Max[0,(b - gamma33)/gamma13]],Max[0,(-b + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma13 - gamma33)/gamma32]],1},
	{0,0,1,1,1,Min[1,Max[0,(b - gamma33)/gamma13]],Min[1,Max[0,(-b + gamma13 + gamma33)/(gamma32 + gamma33 - 1)]],Max[0,(b - gamma13 + gamma32 - 1)/gamma32],Min[1,b/gamma33]},
	{0,1,Min[1,Max[0,(b - gamma33)/gamma13]],1,0,Min[1,(b + gamma13 - gamma33)/gamma13],Min[1,Max[0,(-b + gamma13 + gamma33)/(gamma32 + gamma33 - 1)]],Max[0,(b - gamma13 + gamma32 - 1)/gamma32],1},
	{0,Min[1,Max[0,(b - gamma32 - gamma33)/gamma12]],Min[1,Max[0,(b + gamma13 - gamma32 - gamma33)/gamma13]],1,Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma12],Min[1,Max[0,(b - gamma12 - gamma32 - gamma33)/gamma13]],Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{1,Min[1,Max[0,(b + gamma12 - gamma32 - gamma33)/gamma12]],0,0,Min[1,Max[0,(b - gamma32 - gamma33)/gamma12]],Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma13],Max[0,(-b + gamma12 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{0,Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma12],Max[0,(b - gamma12 + gamma13 - 1)/gamma13],1,Min[1,Max[0,(b + gamma13 - 1)/gamma12]],0,Min[1,Max[0,(-b - gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)]],1,1},
	{0,0,Min[1,Max[0,(b - gamma32 - gamma33)/gamma13]],1,1,1,Max[0,(-b + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,b/gamma32],Min[1,Max[0,(b - gamma32)/gamma33]]},
	{0,Min[1,b/gamma12],Min[1,Max[0,(b - gamma12 - gamma32)/gamma13]],1,1,1,Max[0,(-b + gamma12 + gamma13 + gamma32)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma12)/gamma32]],0},
	{1,1,1,0,Min[1,Max[0,(b + gamma33 - 1)/gamma12]],Max[0,(b - gamma12 + gamma33 - 1)/gamma13],Min[1,Max[0,(-b + gamma32)/(gamma32 + gamma33 - 1)]],Min[1,b/gamma32],0},
	{1,1,1,0,Min[1,Max[0,(b - gamma13)/gamma12]],Min[1,b/gamma13],Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma12 - gamma13 - gamma33)/gamma32]],Min[1,Max[0,(b - gamma12 - gamma13)/gamma33]]},
	{1,1,1,0,Min[1,b/gamma12],0,Max[0,(-b + gamma12 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma12 - gamma33)/gamma32]],Min[1,Max[0,(b - gamma12)/gamma33]]},
	{0,1,Min[1,Max[0,(b - gamma12 + gamma13 - gamma32 - gamma33)/gamma13]],1,Min[1,(b + gamma13 - gamma33)/gamma12],0,Max[0,(-b + gamma12 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma12 + gamma13 - gamma33)/gamma32]],1},
	{0,Min[1,Max[0,(b + gamma13 - 1)/gamma12]],0,1,1,Max[0,(b - gamma12 + gamma13 - 1)/gamma13],Min[1,Max[0,(-b - gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)]],Min[1,(b + gamma13 - gamma33)/gamma32],1},
	{1,Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma12],Min[1,Max[0,(b - gamma12 + gamma13 - gamma32 - gamma33)/gamma13]],0,Min[1,Max[0,(b + gamma13 - gamma32 - gamma33)/gamma12]],Min[1,Max[0,(b - gamma12 - gamma32 - gamma33)/gamma13]],Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{1,Max[0,(b + gamma12 - gamma13 - 1)/gamma12],Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma13],0,0,Min[1,Max[0,(b + gamma12 - 1)/gamma13]],Min[1,Max[0,(-b - gamma12 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)]],1,1},
	{0,Min[1,Max[0,(b + gamma12 - gamma32 - gamma33)/gamma12]],Min[1,Max[0,(b - gamma32 - gamma33)/gamma13]],1,0,Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma13],Max[0,(-b + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{0,1,1,1,Max[0,(b - gamma13 + gamma32 - 1)/gamma12],Min[1,Max[0,(b + gamma32 + gamma33 - 1)/gamma13]],Min[1,-b/(gamma32 + gamma33 - 1)],0,Min[1,Max[0,(b - gamma13 + gamma32 + gamma33 - 1)/gamma33]]},
	{1,1,Max[0,(b - gamma12 + gamma13 - 1)/gamma13],0,Min[1,Max[0,(b + gamma13 - 1)/gamma12]],0,Min[1,Max[0,(-b - gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)]],Min[1,(b + gamma13 - gamma33)/gamma32],1},
	{0,Max[0,(b + gamma12 - gamma13 - 1)/gamma12],Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma13],1,0,Min[1,Max[0,(b + gamma12 - 1)/gamma13]],Min[1,Max[0,(-b - gamma12 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)]],1,1},
	{0,1,Min[1,(b + gamma13 - gamma33)/gamma13],1,Min[1,Max[0,(b - gamma13 - gamma32 - gamma33)/gamma12]],Min[1,Max[0,(b - gamma33)/gamma13]],Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma13 - gamma33)/gamma32]],1},
	{0,Min[1,Max[0,(b - gamma13 - gamma33)/gamma12]],Min[1,b/gamma13],1,1,1,Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma12 - gamma13 - gamma33)/gamma32]],Min[1,Max[0,(b - gamma13)/gamma33]]},
	{1,1,Min[1,Max[0,(b - gamma33)/gamma13]],0,0,Min[1,(b + gamma13 - gamma33)/gamma13],Min[1,Max[0,(-b + gamma13 + gamma33)/(gamma32 + gamma33 - 1)]],Max[0,(b - gamma13 + gamma32 - 1)/gamma32],1},
	{0,1,1,1,Min[1,b/gamma12],Max[0,(b - gamma12 + gamma33 - 1)/gamma13],Min[1,Max[0,(-b + gamma12)/(gamma32 + gamma33 - 1)]],Min[1,Max[0,(b - gamma12 + gamma32 + gamma33 - 1)/gamma32]],0},
	{0,Min[1,Max[0,(b - gamma33)/gamma12]],Min[1,(b + gamma13 - gamma33)/gamma13],1,1,Min[1,Max[0,(b - gamma12 - gamma33)/gamma13]],Max[0,(-b + gamma12 + gamma13 + gamma33)/(gamma32 + gamma33 - 1)],0,1},
	{0,1,0,1,Min[1,Max[0,(b - gamma32 - gamma33)/gamma12]],Min[1,Max[0,(b + gamma13 - gamma32 - gamma33)/gamma13]],Max[0,(-b + gamma12 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,(b + gamma13 - gamma33)/gamma32],1},
	{0,Max[0,(b - gamma13 + gamma32 - 1)/gamma12],Min[1,Max[0,(b + gamma13 + gamma32 - 1)/gamma13]],1,1,Min[1,Max[0,(b + gamma32 - 1)/gamma13]],Min[1,(-b - gamma13 + gamma33)/(gamma32 + gamma33 - 1)],0,1},
	{0,Min[1,Max[0,(b - gamma32 - gamma33)/gamma12]],Min[1,Max[0,(b - gamma12 - gamma32 - gamma33)/gamma13]],1,1,1,Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma33)/gamma32]],Min[1,b/gamma33]},
	{0,Min[1,Max[0,(b - gamma13 - gamma32 - gamma33)/gamma12]],Min[1,Max[0,(b - gamma33)/gamma13]],1,1,Min[1,(b + gamma13 - gamma33)/gamma13],Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma13 - gamma33)/gamma32]],1},
	{0,Min[1,Max[0,(b + gamma32 + gamma33 - 1)/gamma12]],Max[0,(b - gamma12 + gamma33 - 1)/gamma13],1,1,1,Min[1,-b/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma12 + gamma32 + gamma33 - 1)/gamma32]],0},
	{1,Min[1,Max[0,(b + gamma13 - 1)/gamma12]],0,0,Min[1,Max[0,(b + gamma12 + gamma13 - 1)/gamma12]],Max[0,(b - gamma12 + gamma13 - 1)/gamma13],Min[1,(-b - gamma12 - gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{1,1,Min[1,Max[0,(b + gamma32 - 1)/gamma13]],0,Max[0,(b - gamma13 + gamma32 - 1)/gamma12],Min[1,Max[0,(b + gamma13 + gamma32 - 1)/gamma13]],Min[1,(-b - gamma13 + gamma33)/(gamma32 + gamma33 - 1)],0,1},
	{1,1,1,0,Min[1,Max[0,(b + gamma32 + gamma33 - 1)/gamma12]],0,Min[1,-b/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma12 + gamma32 + gamma33 - 1)/gamma32]],Max[0,(b - gamma12 + gamma33 - 1)/gamma33]},
	{1,1,Min[1,Max[0,(b - gamma12 + gamma13 - gamma33)/gamma13]],0,Min[1,(b + gamma13 - gamma33)/gamma12],Min[1,Max[0,(b - gamma12 - gamma33)/gamma13]],Max[0,(-b + gamma12 + gamma13 + gamma33)/(gamma32 + gamma33 - 1)],0,1},
	{1,1,1,0,Min[1,Max[0,(b - gamma13 - gamma32 - gamma33)/gamma12]],Min[1,Max[0,(b - gamma32 - gamma33)/gamma13]],Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma33)/gamma32]],Min[1,b/gamma33]},
	{0,0,Min[1,Max[0,(b + gamma12 - 1)/gamma13]],1,Max[0,(b + gamma12 - gamma13 - 1)/gamma12],Min[1,Max[0,(b + gamma12 + gamma13 - 1)/gamma13]],Min[1,(-b - gamma12 - gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{1,Min[1,Max[0,(b - gamma13 - gamma32 - gamma33)/gamma12]],Min[1,Max[0,(b + gamma13 - gamma32 - gamma33)/gamma13]],0,Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma12],Min[1,Max[0,(b - gamma32 - gamma33)/gamma13]],Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{0,Max[0,(b + gamma32 - 1)/gamma12],1,1,1,0,Min[1,-b/(gamma32 + gamma33 - 1)],0,Min[1,Max[0,(b + gamma32 + gamma33 - 1)/gamma33]]},
	{1,1,1,0,Min[1,Max[0,(b - gamma32)/gamma12]],Min[1,Max[0,(b - gamma12 - gamma32)/gamma13]],Max[0,(-b + gamma12 + gamma13 + gamma32)/(gamma32 + gamma33 - 1)],Min[1,b/gamma32],0},
	{0,1,0,1,0,Max[0,(b + gamma13 - 1)/gamma13],Min[1,(-b - gamma13 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b + gamma13 + gamma32 - 1)/gamma32]],1},
	{0,1,1,1,Min[1,Max[0,(b - gamma32 - gamma33)/gamma12]],Min[1,Max[0,(b - gamma12 - gamma32 - gamma33)/gamma13]],Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma33)/gamma32]],Min[1,b/gamma33]},
	{0,1,1,1,0,Min[1,Max[0,(b - gamma32)/gamma13]],Max[0,(-b + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,b/gamma32],Min[1,Max[0,(b - gamma13 - gamma32)/gamma33]]},
	{1,0,Min[1,Max[0,(b - gamma32 - gamma33)/gamma13]],0,Min[1,Max[0,(b + gamma12 - gamma32 - gamma33)/gamma12]],Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma13],Max[0,(-b + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{0,1,1,1,0,Min[1,b/gamma13],Max[0,(-b + gamma13 + gamma32)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma13)/gamma32]],0},
	{1,0,Min[1,Max[0,(b + gamma12 - 1)/gamma13]],0,Max[0,(b + gamma12 - gamma13 - 1)/gamma12],Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma13],Min[1,Max[0,(-b - gamma12 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)]],1,1},
	{0,Min[1,(b + gamma13 - gamma33)/gamma12],Max[0,(b - gamma12 + gamma13 + gamma32 - 1)/gamma13],1,1,0,Min[1,Max[0,(-b + gamma12 - gamma13 + gamma33)/(gamma32 + gamma33 - 1)]],0,1},
	{0,Max[0,(b - gamma13 + gamma32 + gamma33 - 1)/gamma12],1,1,1,Min[1,b/gamma13],Min[1,Max[0,(-b + gamma13)/(gamma32 + gamma33 - 1)]],0,0},
	{1,1,1,0,Min[1,Max[0,(b - gamma13 - gamma32)/gamma12]],Min[1,Max[0,(b - gamma32)/gamma13]],Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,b/gamma32],Min[1,Max[0,(b - gamma12 - gamma13 - gamma32)/gamma33]]},
	{0,Min[1,Max[0,(b + gamma33 - 1)/gamma12]],0,1,1,1,Min[1,Max[0,(-b + gamma32)/(gamma32 + gamma33 - 1)]],Min[1,b/gamma32],Max[0,(b - gamma12 + gamma33 - 1)/gamma33]},
	{0,0,0,1,1,Min[1,(b + gamma13 - gamma33)/gamma13],Min[1,Max[0,(-b + gamma33)/(gamma32 + gamma33 - 1)]],Max[0,(b + gamma32 - 1)/gamma32],1},
	{1,1,1,0,Max[0,(b - gamma13 + gamma32 + gamma33 - 1)/gamma12],Min[1,b/gamma13],Min[1,Max[0,(-b + gamma13)/(gamma32 + gamma33 - 1)]],0,0},
	{0,1,0,1,0,Min[1,(b + gamma13 - gamma33)/gamma13],Max[0,(-b + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma33)/gamma32]],1},
	{1,1,1,0,0,0,Min[1,Max[0,(-b + gamma33)/(gamma32 + gamma33 - 1)]],Max[0,(b + gamma32 - 1)/gamma32],Min[1,b/gamma33]},
	{0,0,Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma13],1,Min[1,Max[0,(b + gamma12 - gamma32 - gamma33)/gamma12]],Min[1,Max[0,(b - gamma32 - gamma33)/gamma13]],Max[0,(-b + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{1,1,1,0,0,0,Min[1,-b/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b + gamma32 + gamma33 - 1)/gamma32]],Max[0,(b + gamma33 - 1)/gamma33]},
	{0,0,Min[1,Max[0,(b + gamma12 + gamma13 - 1)/gamma13]],1,Max[0,(b + gamma12 - 1)/gamma12],0,Min[1,(-b - gamma12 - gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{0,Max[0,(b + gamma32 - 1)/gamma12],0,1,1,Min[1,Max[0,(b + gamma13 + gamma32 - 1)/gamma13]],Min[1,(-b - gamma13 + gamma33)/(gamma32 + gamma33 - 1)],0,1},
	{0,Min[1,b/gamma12],Min[1,Max[0,(b - gamma12)/gamma13]],1,1,1,Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma12 - gamma13 - gamma33)/gamma32]],Min[1,Max[0,(b - gamma12 - gamma13)/gamma33]]},
	{0,Min[1,Max[0,(b + gamma13 - gamma32 - gamma33)/gamma12]],Max[0,(b - gamma12 + gamma13 - 1)/gamma13],1,Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma12],0,Min[1,Max[0,(-b + gamma12 - gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)]],1,1},
	{0,1,Min[1,Max[0,(b - gamma12 - gamma32 - gamma33)/gamma13]],1,Min[1,(b + gamma13 - gamma33)/gamma12],Min[1,Max[0,(b - gamma12 + gamma13 - gamma33)/gamma13]],Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma12 - gamma33)/gamma32]],1},
	{0,Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma12],Min[1,Max[0,(b + gamma13 - gamma32 - gamma33)/gamma13]],1,Min[1,Max[0,(b - gamma13 - gamma32 - gamma33)/gamma12]],Min[1,Max[0,(b - gamma32 - gamma33)/gamma13]],Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{0,0,Min[1,Max[0,(b + gamma32 + gamma33 - 1)/gamma13]],1,1,1,Min[1,-b/(gamma32 + gamma33 - 1)],Max[0,(b - gamma13 + gamma32 + gamma33 - 1)/gamma32],0},
	{1,Min[1,Max[0,(b - gamma13 - gamma32 - gamma33)/gamma12]],Min[1,Max[0,(b + gamma12 - gamma32 - gamma33)/gamma13]],0,Min[1,Max[0,(b + gamma12 - gamma13 - gamma32 - gamma33)/gamma12]],Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma13],Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{1,0,Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma13],0,Min[1,Max[0,(b + gamma12 - gamma32 - gamma33)/gamma12]],0,Max[0,(-b + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{0,Min[1,Max[0,(b - gamma33)/gamma12]],0,1,1,1,Max[0,(-b + gamma12 + gamma33)/(gamma32 + gamma33 - 1)],0,Min[1,b/gamma33]},
	{0,Min[1,b/gamma12],1,1,1,0,Max[0,(-b + gamma12 + gamma33)/(gamma32 + gamma33 - 1)],0,Min[1,Max[0,(b - gamma12)/gamma33]]},
	{1,1,0,0,0,Min[1,Max[0,(b + gamma13 - gamma32 - gamma33)/gamma13]],Max[0,(-b + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,(b + gamma13 - gamma33)/gamma32],1},
	{0,Min[1,Max[0,(b + gamma13 + gamma32 - 1)/gamma12]],0,1,1,Max[0,(b - gamma12 + gamma13 - 1)/gamma13],Min[1,(-b - gamma13 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma12 + gamma13 + gamma32 - 1)/gamma32]],1},
	{0,0,Min[1,b/gamma13],1,1,1,Max[0,(-b + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma13)/gamma32]],Min[1,Max[0,(b - gamma13 - gamma32)/gamma33]]},
	{1,1,Min[1,Max[0,(b - gamma32 - gamma33)/gamma13]],0,0,Min[1,(b + gamma13 - gamma33)/gamma13],Max[0,(-b + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma33)/gamma32]],1},
	{0,1,1,1,0,Max[0,(b + gamma33 - 1)/gamma13],Min[1,-b/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b + gamma32 + gamma33 - 1)/gamma32]],0},
	{1,1,0,0,Min[1,(b + gamma13 - gamma33)/gamma12],Max[0,(b - gamma12 + gamma13 + gamma32 - 1)/gamma13],Min[1,Max[0,(-b + gamma12 - gamma13 + gamma33)/(gamma32 + gamma33 - 1)]],0,1},
	{1,Min[1,Max[0,(b + gamma12 - gamma32 - gamma33)/gamma12]],Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma13],0,Min[1,Max[0,(b - gamma32 - gamma33)/gamma12]],0,Max[0,(-b + gamma12 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{1,1,1,0,0,0,Max[0,(-b + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,b/gamma32],Min[1,Max[0,(b - gamma32)/gamma33]]},
	{1,1,1,0,Min[1,b/gamma12],Min[1,Max[0,(b - gamma12)/gamma13]],Max[0,(-b + gamma12 + gamma13)/(gamma32 + gamma33 - 1)],0,0},
	{0,0,1,1,1,Min[1,Max[0,(b + gamma32 + gamma33 - 1)/gamma13]],Min[1,-b/(gamma32 + gamma33 - 1)],Max[0,(b - gamma13 + gamma32 - 1)/gamma32],Min[1,Max[0,(b - gamma13 + gamma32 + gamma33 - 1)/gamma33]]},
	{0,0,0,1,Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma12],Min[1,Max[0,(b + gamma13 - gamma32 - gamma33)/gamma13]],Max[0,(-b + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{0,1,Min[1,Max[0,(b - gamma12 + gamma13 - gamma33)/gamma13]],1,Min[1,(b + gamma13 - gamma33)/gamma12],0,Max[0,(-b + gamma12 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma12 - gamma33)/gamma32]],1},
	{0,Min[1,Max[0,(b + gamma12 - gamma13 - gamma32 - gamma33)/gamma12]],Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma13],1,0,Min[1,Max[0,(b + gamma12 - gamma32 - gamma33)/gamma13]],Max[0,(-b + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{0,1,Min[1,Max[0,(b + gamma13 + gamma32 - 1)/gamma13]],1,Max[0,(b - gamma13 + gamma32 - 1)/gamma12],Min[1,Max[0,(b + gamma32 - 1)/gamma13]],Min[1,(-b - gamma13 + gamma33)/(gamma32 + gamma33 - 1)],0,1},
	{0,1,1,1,0,0,Min[1,-b/(gamma32 + gamma33 - 1)],Max[0,(b + gamma32 - 1)/gamma32],Min[1,Max[0,(b + gamma32 + gamma33 - 1)/gamma33]]},
	{0,Min[1,Max[0,(b - gamma13 - gamma32 - gamma33)/gamma12]],Min[1,Max[0,(b + gamma12 - gamma32 - gamma33)/gamma13]],1,Min[1,Max[0,(b + gamma12 - gamma13 - gamma32 - gamma33)/gamma12]],Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma13],Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{0,1,1,1,Min[1,b/gamma12],Min[1,Max[0,(b - gamma12)/gamma13]],Max[0,(-b + gamma12 + gamma13)/(gamma32 + gamma33 - 1)],0,0},
	{0,1,1,1,Min[1,Max[0,(b + gamma32 + gamma33 - 1)/gamma12]],Max[0,(b - gamma12 + gamma32 + gamma33 - 1)/gamma13],Min[1,-b/(gamma32 + gamma33 - 1)],0,0},
	{1,1,1,0,Min[1,b/gamma12],0,Max[0,(-b + gamma12 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma12)/gamma32]],Min[1,Max[0,(b - gamma12 - gamma32)/gamma33]]},
	{1,1,Max[0,(b - gamma12 + gamma13 - 1)/gamma13],0,Min[1,Max[0,(b + gamma13 + gamma32 - 1)/gamma12]],0,Min[1,(-b - gamma13 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma12 + gamma13 + gamma32 - 1)/gamma32]],1},
	{0,0,Max[0,(b + gamma33 - 1)/gamma13],1,1,1,Min[1,-b/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b + gamma32 + gamma33 - 1)/gamma32]],0},
	{0,1,1,1,Max[0,(b + gamma32 - 1)/gamma12],0,Min[1,Max[0,(-b + gamma33)/(gamma32 + gamma33 - 1)]],0,Min[1,b/gamma33]},
	{1,1,1,0,Min[1,Max[0,(b - gamma13 - gamma33)/gamma12]],Min[1,b/gamma13],Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma12 - gamma13 - gamma33)/gamma32]],Min[1,Max[0,(b - gamma13)/gamma33]]},
	{0,1,1,1,0,Min[1,b/gamma13],Min[1,Max[0,(-b + gamma13)/(gamma32 + gamma33 - 1)]],Max[0,(b - gamma13 + gamma32 + gamma33 - 1)/gamma32],0},
	{1,Max[0,(b + gamma12 - 1)/gamma12],0,0,0,Min[1,Max[0,(b + gamma12 + gamma13 - 1)/gamma13]],Min[1,(-b - gamma12 - gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{0,1,1,1,Min[1,Max[0,(b - gamma13 - gamma33)/gamma12]],Min[1,b/gamma13],Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma12 - gamma13 - gamma33)/gamma32]],Min[1,Max[0,(b - gamma13)/gamma33]]},
	{1,1,1,0,0,Min[1,b/gamma13],Max[0,(-b + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma13)/gamma32]],Min[1,Max[0,(b - gamma13 - gamma32)/gamma33]]},
	{0,Min[1,Max[0,(b - gamma32)/gamma12]],0,1,1,1,Max[0,(-b + gamma12 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,b/gamma32],Min[1,Max[0,(b - gamma12 - gamma32)/gamma33]]},
	{0,0,1,1,1,0,Min[1,Max[0,(-b + gamma33)/(gamma32 + gamma33 - 1)]],Max[0,(b + gamma32 - 1)/gamma32],Min[1,b/gamma33]},
	{0,1,0,1,0,Min[1,Max[0,(b + gamma13 + gamma32 - 1)/gamma13]],Min[1,(-b - gamma13 + gamma33)/(gamma32 + gamma33 - 1)],Max[0,(b + gamma32 - 1)/gamma32],1},
	{0,Min[1,Max[0,(b + gamma33 - 1)/gamma12]],1,1,1,Max[0,(b - gamma12 + gamma33 - 1)/gamma13],Min[1,Max[0,(-b + gamma32)/(gamma32 + gamma33 - 1)]],Min[1,b/gamma32],0},
	{0,Max[0,(b + gamma12 - 1)/gamma12],0,1,0,Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma13],Min[1,Max[0,(-b - gamma12 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)]],1,1},
	{0,Min[1,Max[0,(b - gamma13)/gamma12]],Min[1,b/gamma13],1,1,1,Max[0,(-b + gamma12 + gamma13 + gamma32)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma12 - gamma13)/gamma32]],0},
	{0,Min[1,b/gamma12],Min[1,Max[0,(b - gamma12 - gamma33)/gamma13]],1,1,1,Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma12 - gamma13 - gamma33)/gamma32]],Min[1,Max[0,(b - gamma12)/gamma33]]},
	{0,Min[1,Max[0,(b - gamma32)/gamma12]],1,1,1,0,Max[0,(-b + gamma12 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,b/gamma32],Min[1,Max[0,(b - gamma12 - gamma32)/gamma33]]},
	{0,0,1,1,1,0,Min[1,-b/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b + gamma32 + gamma33 - 1)/gamma32]],Max[0,(b + gamma33 - 1)/gamma33]},
	{0,1,0,1,Min[1,Max[0,(b + gamma13 + gamma32 - 1)/gamma12]],Max[0,(b - gamma12 + gamma13 + gamma32 - 1)/gamma13],Min[1,(-b - gamma13 + gamma33)/(gamma32 + gamma33 - 1)],0,1},
	{1,1,Min[1,Max[0,(b - gamma12 - gamma33)/gamma13]],0,Min[1,Max[0,(b - gamma33)/gamma12]],Min[1,(b + gamma13 - gamma33)/gamma13],Max[0,(-b + gamma12 + gamma13 + gamma33)/(gamma32 + gamma33 - 1)],0,1},
	{1,0,Min[1,Max[0,(b + gamma12 + gamma13 - 1)/gamma13]],0,Max[0,(b + gamma12 - 1)/gamma12],0,Min[1,(-b - gamma12 - gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{1,1,1,0,0,Min[1,Max[0,(b + gamma32 + gamma33 - 1)/gamma13]],Min[1,-b/(gamma32 + gamma33 - 1)],Max[0,(b - gamma13 + gamma32 + gamma33 - 1)/gamma32],0},
	{0,0,Min[1,Max[0,(b - gamma32)/gamma13]],1,1,1,Max[0,(-b + gamma13 + gamma32)/(gamma32 + gamma33 - 1)],Min[1,b/gamma32],0},
	{1,1,0,0,Min[1,(b + gamma13 - gamma33)/gamma12],Max[0,(b - gamma12 + gamma13 - 1)/gamma13],Min[1,Max[0,(-b + gamma12 - gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)]],Min[1,Max[0,(b - gamma12 + gamma13 - gamma33)/gamma32]],1},
	{0,1,1,1,Min[1,Max[0,(b - gamma32)/gamma12]],Min[1,Max[0,(b - gamma12 - gamma32)/gamma13]],Max[0,(-b + gamma12 + gamma13 + gamma32)/(gamma32 + gamma33 - 1)],Min[1,b/gamma32],0},
	{0,Min[1,Max[0,(b + gamma12 + gamma13 - 1)/gamma12]],Max[0,(b + gamma13 - 1)/gamma13],1,0,0,Min[1,(-b - gamma12 - gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{1,1,Min[1,Max[0,(b + gamma13 + gamma32 - 1)/gamma13]],0,Max[0,(b + gamma32 - 1)/gamma12],0,Min[1,(-b - gamma13 + gamma33)/(gamma32 + gamma33 - 1)],0,1},
	{0,1,1,1,0,0,Max[0,(-b + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,b/gamma32],Min[1,Max[0,(b - gamma32)/gamma33]]},
	{1,1,0,0,0,Min[1,(b + gamma13 - gamma33)/gamma13],Min[1,Max[0,(-b + gamma33)/(gamma32 + gamma33 - 1)]],Max[0,(b + gamma32 - 1)/gamma32],1},
	{1,1,1,0,0,Min[1,Max[0,(b + gamma32 - 1)/gamma13]],Min[1,-b/(gamma32 + gamma33 - 1)],Max[0,(b - gamma13 + gamma32 - 1)/gamma32],Min[1,Max[0,(b + gamma32 + gamma33 - 1)/gamma33]]},
	{1,1,Min[1,Max[0,(b - gamma12 - gamma32 - gamma33)/gamma13]],0,Min[1,(b + gamma13 - gamma33)/gamma12],Min[1,Max[0,(b - gamma12 + gamma13 - gamma33)/gamma13]],Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma12 - gamma33)/gamma32]],1},
	{0,0,0,1,Min[1,Max[0,(b + gamma12 + gamma13 - 1)/gamma12]],Max[0,(b + gamma13 - 1)/gamma13],Min[1,(-b - gamma12 - gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{1,0,Max[0,(b + gamma13 - 1)/gamma13],0,Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma12],0,Min[1,Max[0,(-b - gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)]],1,1},
	{1,0,Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma13],0,Max[0,(b + gamma12 - gamma13 - 1)/gamma12],Min[1,Max[0,(b + gamma12 - gamma32 - gamma33)/gamma13]],Min[1,Max[0,(-b - gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)]],1,1},
	{0,0,Max[0,(b + gamma13 - 1)/gamma13],1,1,0,Min[1,(-b - gamma13 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b + gamma13 + gamma32 - 1)/gamma32]],1},
	{1,1,0,0,0,Max[0,(b + gamma13 - 1)/gamma13],Min[1,(-b - gamma13 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b + gamma13 + gamma32 - 1)/gamma32]],1},
	{1,1,1,0,Min[1,Max[0,(b - gamma33)/gamma12]],0,Max[0,(-b + gamma12 + gamma33)/(gamma32 + gamma33 - 1)],0,Min[1,b/gamma33]},
	{0,Max[0,(b - gamma13 + gamma32 - 1)/gamma12],Min[1,Max[0,(b + gamma32 - 1)/gamma13]],1,1,1,Min[1,-b/(gamma32 + gamma33 - 1)],0,Min[1,Max[0,(b + gamma32 + gamma33 - 1)/gamma33]]},
	{1,1,1,0,Min[1,b/gamma12],0,Min[1,Max[0,(-b + gamma12)/(gamma32 + gamma33 - 1)]],0,Max[0,(b - gamma12 + gamma32 + gamma33 - 1)/gamma33]},
	{0,1,Min[1,Max[0,(b - gamma12 - gamma32 - gamma33)/gamma13]],1,Min[1,Max[0,(b + gamma13 - gamma32 - gamma33)/gamma12]],Min[1,Max[0,(b - gamma12 + gamma13 - gamma32 - gamma33)/gamma13]],Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,(b + gamma13 - gamma33)/gamma32],1},
	{0,1,1,1,Min[1,Max[0,(b + gamma33 - 1)/gamma12]],0,Min[1,Max[0,(-b + gamma32)/(gamma32 + gamma33 - 1)]],Min[1,b/gamma32],Max[0,(b - gamma12 + gamma33 - 1)/gamma33]},
	{1,Min[1,Max[0,(b + gamma13 - gamma32 - gamma33)/gamma12]],0,0,Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma12],Min[1,Max[0,(b - gamma12 + gamma13 - gamma32 - gamma33)/gamma13]],Max[0,(-b + gamma12 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{0,1,Min[1,Max[0,(b + gamma32 - 1)/gamma13]],1,Max[0,(b - gamma13 + gamma32 - 1)/gamma12],Min[1,(b + gamma13 - gamma33)/gamma13],Min[1,Max[0,(-b + gamma33)/(gamma32 + gamma33 - 1)]],0,1},
	{0,Min[1,Max[0,(b + gamma32 + gamma33 - 1)/gamma12]],1,1,1,0,Min[1,-b/(gamma32 + gamma33 - 1)],0,Max[0,(b - gamma12 + gamma32 + gamma33 - 1)/gamma33]},
	{0,Min[1,b/gamma12],Max[0,(b - gamma12 + gamma32 + gamma33 - 1)/gamma13],1,1,1,Min[1,Max[0,(-b + gamma12)/(gamma32 + gamma33 - 1)]],0,0},
	{0,0,1,1,1,0,Max[0,(-b + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma33)/gamma32]],Min[1,b/gamma33]},
	{1,Min[1,Max[0,(b + gamma12 + gamma13 - 1)/gamma12]],Max[0,(b + gamma13 - 1)/gamma13],0,0,0,Min[1,(-b - gamma12 - gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{0,Min[1,Max[0,(b + gamma32 + gamma33 - 1)/gamma12]],0,1,1,1,Min[1,-b/(gamma32 + gamma33 - 1)],0,Max[0,(b - gamma12 + gamma32 + gamma33 - 1)/gamma33]},
	{1,Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma12],Min[1,Max[0,(b + gamma13 - gamma32 - gamma33)/gamma13]],0,0,Min[1,Max[0,(b - gamma32 - gamma33)/gamma13]],Max[0,(-b + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{0,Max[0,(b + gamma12 - 1)/gamma12],Min[1,Max[0,(b + gamma12 + gamma13 - 1)/gamma13]],1,0,0,Min[1,(-b - gamma12 - gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{1,Min[1,Max[0,(b - gamma32 - gamma33)/gamma12]],Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma13],0,Min[1,Max[0,(b + gamma12 - gamma32 - gamma33)/gamma12]],Min[1,Max[0,(b - gamma12 - gamma32 - gamma33)/gamma13]],Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{1,1,1,0,Min[1,Max[0,(b - gamma32)/gamma12]],0,Min[1,Max[0,(-b + gamma12 + gamma32)/(gamma32 + gamma33 - 1)]],Min[1,b/gamma32],Max[0,(b - gamma12 + gamma33 - 1)/gamma33]},
	{0,1,1,1,Min[1,Max[0,(b - gamma13 - gamma32)/gamma12]],Min[1,Max[0,(b - gamma32)/gamma13]],Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,b/gamma32],Min[1,Max[0,(b - gamma12 - gamma13 - gamma32)/gamma33]]},
	{0,Min[1,Max[0,(b + gamma12 - gamma32 - gamma33)/gamma12]],Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma13],1,Min[1,Max[0,(b - gamma32 - gamma33)/gamma12]],0,Max[0,(-b + gamma12 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{1,Min[1,Max[0,(b + gamma12 - gamma13 - gamma32 - gamma33)/gamma12]],Min[1,Max[0,(b + gamma12 - gamma32 - gamma33)/gamma13]],0,0,Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma13],Max[0,(-b + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{0,1,1,1,Min[1,Max[0,(b - gamma33)/gamma12]],0,Max[0,(-b + gamma12 + gamma33)/(gamma32 + gamma33 - 1)],0,Min[1,b/gamma33]},
	{1,0,0,0,Max[0,(b + gamma12 - 1)/gamma12],Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma13],Min[1,Max[0,(-b - gamma12 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)]],1,1},
	{0,1,1,1,Max[0,(b - gamma13 + gamma32 + gamma33 - 1)/gamma12],Min[1,b/gamma13],Min[1,Max[0,(-b + gamma13)/(gamma32 + gamma33 - 1)]],0,0},
	{0,0,1,1,1,Min[1,Max[0,(b - gamma32 - gamma33)/gamma13]],Max[0,(-b + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,b/gamma32],Min[1,Max[0,(b - gamma32)/gamma33]]},
	{0,0,0,1,1,1,Min[1,Max[0,(-b + gamma32)/(gamma32 + gamma33 - 1)]],Min[1,b/gamma32],Max[0,(b + gamma33 - 1)/gamma33]},
	{0,1,Min[1,Max[0,(b - gamma12 - gamma33)/gamma13]],1,Min[1,Max[0,(b - gamma33)/gamma12]],Min[1,(b + gamma13 - gamma33)/gamma13],Max[0,(-b + gamma12 + gamma13 + gamma33)/(gamma32 + gamma33 - 1)],0,1},
	{1,0,0,0,Min[1,Max[0,(b + gamma12 - gamma32 - gamma33)/gamma12]],Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma13],Max[0,(-b + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{0,Min[1,Max[0,(b - gamma32 - gamma33)/gamma12]],0,1,Min[1,Max[0,(b + gamma12 - gamma32 - gamma33)/gamma12]],Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma13],Max[0,(-b + gamma12 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],1,1},
	{0,Min[1,Max[0,(b - gamma32)/gamma12]],Max[0,(b - gamma12 + gamma33 - 1)/gamma13],1,1,1,Min[1,Max[0,(-b + gamma12 + gamma32)/(gamma32 + gamma33 - 1)]],Min[1,b/gamma32],0},
	{1,1,Max[0,(b - gamma12 + gamma13 + gamma32 - 1)/gamma13],0,Min[1,Max[0,(b + gamma13 + gamma32 - 1)/gamma12]],0,Min[1,(-b - gamma13 + gamma33)/(gamma32 + gamma33 - 1)],0,1},
	{1,1,1,0,0,Min[1,Max[0,(b - gamma32)/gamma13]],Max[0,(-b + gamma13 + gamma32)/(gamma32 + gamma33 - 1)],Min[1,b/gamma32],0},
	{0,0,Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma13],1,Max[0,(b + gamma12 - gamma13 - 1)/gamma12],Min[1,Max[0,(b + gamma12 - gamma32 - gamma33)/gamma13]],Min[1,Max[0,(-b - gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)]],1,1},
	{1,1,1,0,Min[1,Max[0,(b - gamma13)/gamma12]],Min[1,b/gamma13],Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,Max[0,(b - gamma12 - gamma13)/gamma32]],Min[1,Max[0,(b - gamma12 - gamma13 - gamma32)/gamma33]]},
	{0,1,1,1,Min[1,Max[0,(b - gamma13)/gamma12]],Min[1,b/gamma13],Max[0,(-b + gamma12 + gamma13 + gamma33)/(gamma32 + gamma33 - 1)],0,Min[1,Max[0,(b - gamma12 - gamma13)/gamma33]]},
	{1,1,0,0,Min[1,(b + gamma13 - gamma33)/gamma12],Min[1,Max[0,(b - gamma12 + gamma13 - gamma33)/gamma13]],Max[0,(-b + gamma12 + gamma33)/(gamma32 + gamma33 - 1)],0,1},
	{1,1,1,0,0,Max[0,(b + gamma33 - 1)/gamma13],Min[1,Max[0,(-b + gamma32)/(gamma32 + gamma33 - 1)]],Min[1,b/gamma32],0},
	{1,1,0,0,Max[0,(b + gamma32 - 1)/gamma12],Min[1,Max[0,(b + gamma13 + gamma32 - 1)/gamma13]],Min[1,(-b - gamma13 + gamma33)/(gamma32 + gamma33 - 1)],0,1},
	{1,0,0,0,Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma12],Max[0,(b + gamma13 - 1)/gamma13],Min[1,Max[0,(-b - gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)]],1,1},
	{1,1,1,0,Max[0,(b - gamma13 + gamma32 - 1)/gamma12],Min[1,b/gamma13],Min[1,Max[0,(-b + gamma13)/(gamma32 + gamma33 - 1)]],0,Min[1,Max[0,(b - gamma13 + gamma32 + gamma33 - 1)/gamma33]]},
	{0,0,0,1,Max[0,(b + gamma12 - 1)/gamma12],Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma13],Min[1,Max[0,(-b - gamma12 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)]],1,1},
	{0,0,1,1,1,Max[0,(b + gamma33 - 1)/gamma13],Min[1,Max[0,(-b + gamma32)/(gamma32 + gamma33 - 1)]],Min[1,b/gamma32],0},
	{1,Max[0,(b + gamma12 - 1)/gamma12],Min[1,(b + gamma12 + gamma13 - gamma32 - gamma33)/gamma13],0,0,0,Min[1,Max[0,(-b - gamma12 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)]],1,1},
	{0,1,1,1,0,0,Min[1,Max[0,(-b + gamma32)/(gamma32 + gamma33 - 1)]],Min[1,b/gamma32],Max[0,(b + gamma33 - 1)/gamma33]},
	{1,1,1,0,Min[1,b/gamma12],Max[0,(b - gamma12 + gamma32 + gamma33 - 1)/gamma13],Min[1,Max[0,(-b + gamma12)/(gamma32 + gamma33 - 1)]],0,0},
	{0,1,0,1,Max[0,(b + gamma32 - 1)/gamma12],Min[1,Max[0,(b + gamma13 + gamma32 - 1)/gamma13]],Min[1,(-b - gamma13 + gamma33)/(gamma32 + gamma33 - 1)],0,1}
};
Length[rawMass]
massLiSven={1-b,1-b,1-b,b,b,b,b,b,b};


(* ::Subsubsection::Closed:: *)
(*Handcrafted Hybrid Algorithms*)


CheckMassRand[mass_]:={gamma11,gamma12,gamma13,gamma11,gamma12,gamma13,
		1-gamma32-gamma33,gamma32,gamma33}.(mass-{a,a,a,b,b,b,b,b,b}) /.
		{a->1-b}/.({gamma12->#1,gamma13->(1-#1)#2,gamma32->#1*#3,gamma33->(1-#1)#2*#4,b->#3}&@@RandomReal[{0,1},5])
CheckMassListRand[massList_]:=ParallelTable[Chop@Max@Abs@Table[CheckMassRand@m,{i,1,100}],{m,massList}] (* probabilistically check if the mass balances; it should equal zero *)
CheckMassListRand[rawMass]


hybridMass = {
	 (* 168: replace 9+42 (in crit region) *)
	{0,1,0,1,x3,x3,Min[1,(-b-gamma13+gamma33)/(-1+gamma32+gamma33)],Min[1,Max[0,(-1+b+gamma13+gamma32)/gamma32]],1}/.{x3->Max[0,(-1+b+gamma13)/(gamma12+gamma13)]}
	(* 169: ? replace 49+5+71*)
	,{0,0,1,1,1,Min[1,b/gamma13],x2,x2,x2}/.x2->Max[0,b-gamma13]
	(*170*),{1,1,1,0,0,0,b,b,b}
	(*171*),{1,1,1,0,x1,x1,x2,x2,x2}/.{x1->Min[1,b/(gamma12+gamma13)],x2->Max[0,b-gamma12-gamma13]}
    (*172*),{0,1,1,1,0,0,b,b,b}
	(*173*),{0,1,1,1,x1,x1,x2,x2,x2}/.{x1->Min[1,b/(gamma12+gamma13)],x2->Max[0,b-gamma12-gamma13]}
    (*174*),{0,0,0,1,1,1,b,b,b}
    (*175*),{0,0,0,1,x2,x2,x1,x1,x1}/.{x2->1-Min[(1-b)/(gamma12+gamma13),b/Max[b,1-gamma12-gamma13]],x1->b/Max[b,1-gamma12-gamma13]}
	(*176: somewhat-symmetrize 167 in noncritical region *)
	,{0,1,0,1,x2,x2,x1,x1,1}/.{x1->Min[1,(b+gamma13-gamma33)/(1-gamma33)],x2->Max[0,(b+gamma13-1)/(gamma12+gamma13)]}
    (* 177: counterbalance to 169 , uncertain how useful yet *)
	,{0,0,1,1,1,0,b,b,b}
	(* 178: WEAK early chain, due to non convex decomposition, but later chain is the important part *)
	,{0,1,1-x1,1,x2,x2,x1,x1,x1}/.{x1->b/Max[b,1-gamma13],x2->Max[0,(b+gamma13-1)/(gamma12+gamma13)]}
	(* 179: WEAK early chain "" *)
	,{0,1,1-x1,1,x3,x3,x2,x1,x1}/.{x1->b/Max[b,gamma32+gamma33-gamma13],x2->Max[0,Min[1,1-(1-b-gamma13)/(1-gamma32-gamma33)]],x3->Max[0,(b+gamma13-1)/(gamma12+gamma13)]}
	(* 180: less sym version of 172, to counter-balance 179 *)
	,{0,1,1,1,0,0,x1,x2,x2}/.{x1->Min[1,b/(1-gamma32-gamma33)],x2->Max[0,Min[1,1-(1-b)/(gamma32+gamma33)]]}
	(* 181: sym version of 72 *)
	,{0,0,1,1,1,x1,x3,x2,x2}/.{x1->Min[1,b/gamma13],x2->Max[0,Min[1,(b-gamma13)/(gamma32+gamma33)]],x3->Max[0,(b-gamma13-gamma32-gamma33)/(1-gamma32-gamma33)]}
	(* 182: 2-sym variant of 174 *)
    ,{0,0,0,1,1,1,x1,x2,x2}/.{x1->Min[1,b/(1-gamma32-gamma33)],x2->Max[0,1-(1-b)/(gamma32+gamma33)]}
};
unusedMass={
    {0,1,0,1,0,1,b,b,b}  (*not actually valid*)
    ,{0,0,0,1,1,x2,x1,x1,1}/.{x1->Min[1,(b+gamma13-gamma33)/(1-gamma33)],x2->Max[0,(gamma13-1+b)/gamma13]}
    ,{0,0,0,1,1,x1,x2,x2,1}/.{x1->Min[1,(b+gamma13-gamma33)/gamma13],x2->Max[0,(b-gamma33)/(1-gamma33)]}
};
CheckMassListRand[hybridMass] (* probabilistically check if the mass balances; it should equal zero *)


(* test out new algos *)
(*hybridMass[[-1]]
Manipulate[Module[{msolDual,msolOptBaseline,mCombo,params},
	params = {b->pb,gamma12->pgamma12,gamma13->pgamma13,gamma32->pgamma32,gamma33->pgamma33,g1->pg1,g2->pg2};
    Column@{hybridMass[[-1]]/.params,
	{gamma11,gamma12,gamma13,gamma11,gamma12,gamma13,
		1-gamma32-gamma33,gamma32,gamma33}.(mass[[175]]-{a,a,a,b,b,b,b,b,b}) /.
		{a->1-b}/.params}
   ],{{pb,b0},0,1,.001},{{pg1,g10},.01,1,.001},{{pg2,g20},.01,1,.001},{{pgamma12,gamma120},.01,1.5,.001}
   ,{{pgamma13,gamma130},.01,1,.001},{{pgamma32,gamma320},.01,1,.001},{{pgamma33,gamma330},.01,1,.001}]*)


(* ::Subsubsection:: *)
(*Variables and Constraints:*)


rawMass2=Join[rawMass(*,hybridMass*)];
algs=Prepend[cost@@#&/@rawMass2,costLiSven];
mass=Prepend[rawMass2,massLiSven];
Length@algs
algsWithMass=Table[{algCost->algs[[i]],algMass->mass[[i]],algIndex->i},{i,1,Length@mass}];
constrAlg = Z<=#&/@algs;

gammaVar1 = {gamma12,gamma13};
gammaVar3 = {gamma32,gamma33};
varNonLin = Union[gammaVar1,gammaVar3,{b,g1,g2}];
vars=Union[varD1,varD2,{Z},varNonLin];
(*constrD1D2=MapThread[#1<=#2&,{varD2,varD1}];*)
constrBasic = Join[{Z>=0,0<=b<=1},#>=0&/@Union[varD1,varD2,gammaVar1,gammaVar3]
	,MapThread[#1<=#2&,{gammaVar3,gammaVar1}],{Total[gammaVar3]<=1, Total[varD1]*(1-b)+Total[varD2]*b==1}];
(* TODO: Define gamma3s in terms of gamma1s to reduce number of non-linear variables, might reduce execution time(?) *)


(* ::Subsubsection:: *)
(*Define NLP*)


(* type checking: needed for multiple optional arguments and generally helpful for debugging *)
IndexQ[i_]:=(i==All || i==(1;;All) || And@@IntegerQ/@i) (* allow passing ;; or All for index subset *)
EquationQ[eq_]:=Not@FreeQ[eq,(Equal|LessEqual|Less|Greater|GreaterEqual)]||eq (* contains one of =,<,<=,>,>=, or trivially true *)

defaultHints={.6 <= b <= .8, .01 <= gamma12 <= 2, .01 <= gamma13 <= 2, Z>=1,
		.01<=gamma32+gamma33<=.99, .01<=gamma32, .01<=gamma33};
SolveNLP[g1hat_,g2hat_,iter_,algI_,hints_:defaultHints]:=
	NMaximize[{Z, constrAlg[[algI]], constrBasic, g1==g1hat, g2==g2hat, hints
		}, vars~Union~{g1,g2}, MaxIterations->iter][[2]]
SolveNLP[g1hat_,iter_,algI_:;;]:=SolveNLP[g1hat,iter,algI,defaultHints]

(* If we fix non-linear variables, remaining system is linear and very fast/accurate *)
SolveLP[nonLinParams_,algI:_?IndexQ:All,constrExtra:{___?EquationQ}:{}]:=
	Maximize[{Z, constrAlg[[algI]], constrBasic, constrExtra}/.nonLinParams,
		Union[varD1,varD2,{Z}]][[2]]~Join~nonLinParams;
SolveLPatSol[fullSol_,algI:_?IndexQ:All,constrExtra:{___?EquationQ}:{}]:=SolveLP[ExtractNonLin[fullSol], algI,constrExtra]
ExtractNonLin[sol_]:=Select[sol,MemberQ[varNonLin,#[[1]]]&]


(* ::Subsection::Closed:: *)
(*Utility Methods*)


StyleMass[mass_,digits_:2]:=Style[mass,PrintPrecision->digits]
EvaluateAlgs[params_,algIset_:;;]:=(
		{algCost, algMass//StyleMass, algIndex}/.#&/@algsWithMass[[algIset]]
	)/.params
EvaluateAlgsByCost[params_,algIset_:;;]:=Grid[SortBy[EvaluateAlgs[params,algIset],First]~Prepend~{"Alg Cost ", "Alg Mass","Alg Index"},Alignment->Left]
EvaluateAlgsByMass[params_,algIset_:;;]:=Grid[SortBy[EvaluateAlgs[params,algIset],#[[2]]&]~Prepend~{"Alg Cost ", "Alg Mass","Alg Index"},Alignment->Left]
EvaluateAlgsByIndex[params_,algIset_:;;]:=Grid[SortBy[EvaluateAlgs[params,algIset],#[[3]]&]~Prepend~{"Alg Cost ", "Alg Mass","Alg Index"},Alignment->Left]


(* assumes gamma3s don't matter *)
(*todo adjust more subetly and only if needed *)
FixGamma3s[params_]:=Join[Select[params,Not@MemberQ[{gamma32,gamma33},#[[1]]]&],
			            {gamma32->(gamma12/2/.params),gamma33->(gamma13/2/.params)}]
ExtractNonLinX[sol_]:=Select[sol,Not@MemberQ[varD1~Union~varD2,#[[1]]]&]
ShowClients[sol_]:=Grid@{{d211,d221,d231,"  ",d212,d222,d232,"  ",d213,d223,d233},
				    {d111,d121,d131,"  ",d112,d122,d132,"  ",d113,d123,d133},{" "},
					{d1131,d1231,d1331,"  ",d1132,d1232,d1332,"  ",d1133,d1233,d1333},
				    {d311,d321,d331,"  ",d312,d322,d332,"  ",d313,d323,d333}}/.sol
ConstrainNearby[nonLinParams_,eps_:.05]:=(#[[2]]*(1-eps)<=#[[1]]<=#[[2]]*(1+eps))&/@ExtractNonLin@nonLinParams


(* ::Subsection:: *)
(*Best Result (1.3057?)*)


sol3={b->0.6704691512786565`,d111->0.030151466178908695`,d112->0.0007505799918395816`,d113->0.02284397332476624`,d1131->0.004957127399036917`,d1132->0.0033849340836345013`,d1133->0.08893768328142544`,d121->0.03015146131575757`,d122->0.22719693190360066`,d123->1.221804609887599`*^-6,d1231->0.08892675042298144`,d1232->0.14107815618612843`,d1233->0.034074010823198254`,d131->0.06128352499219638`,d132->5.198408426107392`*^-7,d133->0.26394448363400386`,d1331->0.23334147745814485`,d1332->0.17867295874835623`,d1333->0.22672767964484045`,d211->0.`,d212->0.0032450042891221604`,d213->0.09077159826478834`,d221->0.`,d222->0.061098544895136664`,d223->3.865592171638287`*^-9,d231->0.`,d232->7.624178186742625`*^-7,d233->0.02829975647735198`,d311->0.003317338828125693`,d312->0.0028268796924769512`,d313->0.08749623273642182`,d321->0.07601561746042138`,d322->0.023431862072954383`,d323->0.0025072550528780096`,d331->0.08235632855809785`,d332->0.13329626230239866`,d333->0.09253822239402419`,g1->0.642`,g2->0.833`,gamma12->0.32963704056869886`,gamma13->0.33792751290013473`,gamma32->0.3295912277823226`,gamma33->0.3368783094462972`,Z->1.3036610750819297`};


algsI29={1,6,14,21,25,28,36,42,45,50,51,53,56,72,77,80,86,91,109,119,124,125,128,141,147,153,156,162,168};
algsI30={1,6,10,14,21,25,28,36,42,43,45,50,51,53,56,72,77,80,86,91,109,119,124,125,128,141,147,153,156,162}; (* basic *)
algsI9={1,169,170,171,172,173,174,175,176}; (* handles critical point, but does worse at localMax1 *)
algsI13={1,170,171,172,173,174,175,147,10,72,125,86,169}; (* handles localMax1 *)
algsI14={1,170,171,172,173,174,175,176,147,10,72,125,86,169}; (* handles localMax1+2 *)
algsI9sym={1,169,170,171,172,173,174,175,178}; (*symmetric in F31/F32/F33 and F22/F23, but does poorly at save6 *)
algsI10sym2={1,169,170,171,172,173,174,175,179,180}; (*symmetric in F32/F33 and F22/F23, fails at save7*)
algsI12sym2={1,169,170,171,172,173,174,175,179,180,181,182};
algsI=algsI30
Length@algsI
solBest={b->0.6715331873666895`,d111->0.046860368382269514`,d112->0.02456331335018877`,d113->0.044074854304643814`,d1131->0.07144707077351625`,d1132->0.02986653206436148`,d1133->0.061099227368884346`,d121->0.04695211510711601`,d122->0.0752748957991086`,d123->0.13931896491196272`,d1231->0.05883468012890778`,d1232->0.024422132431967978`,d1233->0.050364903626525424`,d131->0.07457214633931589`,d132->0.061522492525401866`,d133->0.11153079587680949`,d1331->0.3156463103941929`,d1332->0.12667137180358412`,d1333->0.26456720159876934`,d211->1.3055804129059156`*^-10,d212->0.013885414272666036`,d213->0.02619922345614402`,d221->1.3055806300140836`*^-10,d222->0.024068020757453987`,d223->0.042253564881508485`,d231->1.3055745614447794`*^-10,d232->0.021952084030530877`,d233->0.0410386302990541`,d311->0.05434950802505862`,d312->0.021182405258084562`,d313->0.044979431676897816`,d321->0.04555546206374887`,d322->0.017939953371794066`,d323->0.037662673383040815`,d331->0.13291684395399628`,d332->0.055358001630245506`,d333->0.11368619189433839`,g1->0.642`,g2->0.833`,gamma12->0.21167853121269323`,gamma13->0.38689227778230223`,gamma32->0.18043327359652983`,gamma33->0.3749367318689848`,Z->1.3057309344455876`,g1->0.642`,g2->0.833`};
{g1hat,g2hat}={g1,g2}/.solBest
{g1hat,g2hat}={.62,.85}
(* should reproduce solBest, may need 2000 iterations *)


{time,sol2}=Timing@SolveNLP[g1hat,g2hat,1200,algsI30,defaultHints] (*more iters needed for accuracy*)


1.3036610750819297`


localMax2={b->.6715,g1->.642,g2->.833,gamma12->.001,gamma13->.979,gamma32->.001,gamma33->.001};
SolveLPatSol[sol2,solTightAll~Union~{7}];
SolveLPatSol[sol2,All]
Z/.%;
EvaluateAlgsByCost[%%,Range@Length[rawMass+1]]


sol1={b->0.6722857121027332`,g1->0.642`,g2->0.833`,gamma12->0.3354641102280557`,gamma13->0.32473589766882294`,gamma32->0.3354099707632686`,gamma33->0.32466836968844615`};


(* ::Text:: *)
(*B y setting g1=.642 and g2=.833, we get approximation factor???*)
(**)
(*I think this NLP could be simplified by padding such that |F2C|=min{|F2B|,|Y|}, to eliminate need for gammaC variable. However, in my attempts to do so, it didn't actually seem to speed up the NLP, if anything it made it less likely to converge to the correct solution.*)
(**)
(*Fortunately, adversary appears unable to take advantage of the variables gamma32, gamma33, as their value doesn't seem to affect the optima.*)


(* ::Subsubsection::Closed:: *)
(*Output*)


outputFile=FileNameJoin[{NotebookDirectory[],"data","g2_algs.m"}]
outputObj={massSubsets->{algs12sym2->algsI12sym2,algs14->algsI14,algsBasic30->algsI30, algs29->algsI29},massAll->mass};
Put[outputObj,outputFile]


outputFile=FileNameJoin[{NotebookDirectory[],"data","g2_algs.json"}];
outputObj={"massSubsets"->{"algs12sym2"->algsI12sym2,"algs14"->algsI14,"algs29"->algsI29,"algsBasic30"->algsI30},"massAll"->Map[ToString@InputForm@#&,mass,{2}]};
Export[outputFile,outputObj,"JSON"]


(* ::Subsection:: *)
(*Find Minimal Subset*)


loopAlgsI = solTightAll;
tsol=sol1;
maxIndices=40;  (* set this up higher to enable *)
maxIterations=1000;
While[Length[loopAlgsI]<maxIndices,
	(*{time, loopSol} = Timing@SolveNLP[g1hat,g2hat,maxIterations,loopAlgsI]; *)
	loopSol = FixGamma3s@tsol;
	loopSolMoreAccurate = SolveLPatSol[loopSol,loopAlgsI]; 
	cheapestAlg = SortBy[algsWithMass[[;;Length[rawMass]+1]]/.loopSolMoreAccurate, algCost/.#&][[1]];

Print[cheapestAlg];
	(*Print[{NumberForm[X/.loopSol,{8,7}], NumberForm[algCost,{8,7}], algIndex, Chop[algMass,.0001], Round@time, NumberForm[ExtractNonLin[loopSol],{3,2}]}/.cheapestAlg];*)
	If[(algCost/.cheapestAlg) <= (Z/.loopSolMoreAccurate) - .00001,
		AppendTo[loopAlgsI, algIndex/.cheapestAlg],
		(* if there's no good algo to add, cycle an old one instead *)
		Print["No improvement. Removing "<>ToString[loopAlgsI[[1]]]]<>": "<>ToString@loopAlgsI; loopAlgsI = loopAlgsI(*[[2;;]]*);Break[]
	]
	(* TODO make inner loop to re-run LP until no improvement == much faster *)
]


tsol2=SolveLPatSol[loopSol,loopAlgsI]
Union@(Last/@Select[#,#[[1]]-.001<(Z/.tsol2)&])&@EvaluateAlgsByCost[tsol2,loopAlgsI][[1]][[2;;]]


{{1,6,14,21,28,36,42,45,50,51,53,56,72,77,80,100,109,119,124,147,153,156,162}, 
{6,14,21,28,36,42,45,50,51,53,56,72,77,79,80,100,109,119,124,147,153,156,162}, 
{1,4,6,14,17,21,28,36,42,45,47,50,51,53,56,72,77,79,80,86,93,100,109,124,147,153,156,162},
{1,4,6,14,21,28,36,42,45,47,50,51,53,56,72,77,79,80,86,93,100,109,119,124,147,153,156,162}, 
{1,6,14,28,36,39,42,45,47,50,51,53,56,72,77,79,80,86,93,100,109,119,124,147,153,156,162},
{1,4,6,14,21,28,36,42,45,47,50,51,53,56,72,77,79,80,86,93,100,109,119,124,147,153,156,162},
{1,4,5,6,14,21,28,36,42,45,47,50,51,53,56,72,77,79,80,86,93,100,109,119,124,147,153,156,162}, 
{1,4,5,6,14,17,21,28,36,42,45,47,50,51,53,56,67,72,77,79,80,86,93,100,109,119,124,147,153,156,162},
{(*28, 56,*)52,78,136, 7}
};
solTightAll=Union@@%
solTightAll=Complement[solTightAll,{28, 56}]
Length@%


tsolDual=SolveDualLP[sol1,solTightAll]
algIcrit=Union@loopAlgsI[[ Select[Range@Length@loopAlgsI,(u[#]/.tsolDual)>0&] ]]


(* ::Subsubsection::Closed:: *)
(*Scratch*)


(*
loopAlgsI={143,122,18,37,34,35,31,44,11,1,13,40,126,105,14,108,109,161,51,118,52,41,124,5,10,42,79,27,49,140,146,85,71,24,9,76,155,20,64,50,71};
loopAlgsI={31,44,11,1,13,40,126,105,14,108,109,161,51,118,52,41,124,5,10,42,79,27,49,140,146,85,71,24,9,76,155,20,64,50,71};
loopAlgsI={13,40,126,105,14,108,109,161,51,118,52,41,124,5,10,42,79,27,49,140,146,85,71,24,9,76,155,20,64,50,71,55,122,127};
loopAlgsI={105,14,108,109,161,51,118,52,41,124,5,10,42,79,27,49,140,146,85,71,24,9,76,155,20,64,50,71,55,122,127};
loopAlgsI={105,14,108,109,161,51,118,52,41,124,5,10,42,79,27,49,140,146,85,71,24,9,76,155,20,64,50,71,55,122,127,13};

{1.74, 0., 143, {1, 0, 0, 0, 0.42631879, 1, 1, 1, 1}, 12.921875}
{1.74, 0., 122, {1, 1, 0, 0, 0, 0.59218477, 1, 1, 1}, 34.187500}
{1.7399999, 0., 18, {1, 0, 1, 0, 0, 0.20426351, 1, 1, 1}, 37.781250}
{1.7302475, 0.030001763, 37, {1, 1, 1, 0, 0, 0, 0, 0.87397596, 1}, 33.265625}
{1.6790983, 0.22243083, 34, {1, 1, 0, 0, 0, 0.96435675, 1, 0, 1}, 21.781250}
{1.6790978, 0.22243083, 35, {1, 1, 1, 0, 0, 0, 0.74566652, 0, 0}, 27.859375}
{1.4756418, 0.6121517, 31, {0, 0, 0.70428937, 1, 1, 1, 0, 0, 1}, 24.765625}
{1.4340801, 0.36860007, 44, {0, 1, 1, 1, 0, 0.27320744, 0, 1, 0}, 36.406250}
{1.4340802, 0.24857339, 11, {0, 1, 0, 1, 1, 1, 0, 0.16463744, 0}, 53.968750}
{1.4299918, 0., 1, {0, 0, 1, 1, 1, 0.62626263, 0, 1, 0}, 59.687500}
{"1.4048352", "0.6886392", 40, {0,0,1,1,1,0,1,0,0.00016036112084526365`}, 78}
{"1.3970533", "0.8746786", 126, {0,1,0,1,0.7480802249791965`,0,0,1,1}, 70}
{"1.3885863", "0.7376873", 105, {0,1,0,1,0.5224902543064074`,0,1,0,1}, 164, {b->"0.66",g1->"0.60",g2->"0.85",gamma12->"0.31",gamma13->"0.32",gamma32->"0.18",gamma33->"0.16"}}
{"1.3866437","0.6231023",14,{1,1,1,0,1,0,3.3387684453097045`*^-7,1,1},90,{b->"0.65",g1->"0.60",g2->"0.85",gamma12->"0.50",gamma13->"0.51",gamma32->"0.01",gamma33->"0.15"}}
{"1.4095288", "0.7600438", 108, {1,1,1,0,0,1,1,0.5668202252740848`,0}, 106, {b->"0.64",g1->"0.60",g2->"0.85",gamma12->"0.84",gamma13->"0.15",gamma32->"0.84",gamma33->"0.15"}}
{"1.3917338", "0.7313604", 109, {0,0,0.016327330146324218`,1,1,1,0,1,0}, 104, {b->"0.63",g1->"0.60",g2->"0.85",gamma12->"0.62",gamma13->"0.61",gamma32->"0.62",gamma33->"0.37"}}
{"1.3785822", "0.8248534", 161, {0,0,0,1,0.6064729216053097`,1,1,1,1}, 88, {b->"0.64",g1->"0.60",g2->"0.85",gamma12->"0.91",gamma13->"0.62",gamma32->"0.64",gamma33->"0.35"}}
{"1.3622378", "0.8315724", 51, {0,0,0,1,1,1,0.9626687276423019`,1,0}, 103, {b->"0.66",g1->"0.60",g2->"0.85",gamma12->"0.35",gamma13->"0.66",gamma32->"0.01",gamma33->"0.31"}}
{"1.3531882", "0.9498931", 118, {0,0,0,1,1,0.6553734161132394`,1,1,1}, 92, {b->"0.66",g1->"0.60",g2->"0.85",gamma12->"0.52",gamma13->"0.99",gamma32->"0.28",gamma33->"0.66"}}
{"1.3432391", "0.8505813", 52, {0,0,0,1,1,1,0.8956340136622007`,0,1}, 82, {b->"0.68",g1->"0.60",g2->"0.85",gamma12->"0.31",gamma13->"0.38",gamma32->"0.24",gamma33->"0.01"}}
{"1.3306160", "0.9904201", 41, {1,1,1,0,0.9784030970381273`,0,0,1,0}, 81, {b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.53",gamma13->"0.48",gamma32->"0.15",gamma33->"0.14"}}
{"1.3356466", "0.9641105", 124, {0,0,0,1,1,1,1,0,0.657706605825563`}, 126, {b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.57",gamma13->"0.91",gamma32->"0.02",gamma33->"0.91"}}
{"1.3328756", "1.0031160", 5, {0,0,1,1,1,1,0.740538073500749`,0,1}, 96, {b->"0.69",g1->"0.60",g2->"0.85",gamma12->"0.27",gamma13->"0.15",gamma32->"0.27",gamma33->"0.01"}}
{"1.3281167", "0.9038275", 10, {0,0,0,1,1,1,0,1,0.9999616981027899`}, 97, {b->"0.69",g1->"0.60",g2->"0.85",gamma12->"0.31",gamma13->"0.38",gamma32->"0.31",gamma33->"0.38"}}
{"1.3262170", "0.9630202", 42, {0,1,0,1,0,0.39335101751871904`,1,1,1}, 113, {b->"0.69",g1->"0.60",g2->"0.85",gamma12->"0.31",gamma13->"0.51",gamma32->"0.01",gamma33->"0.01"}}
{"1.3211593", "1.0478021", 79, {0,0,0,1,1,1,0.47202675781817666`,1,1}, 101, {b->"0.68",g1->"0.60",g2->"0.85",gamma12->"0.41",gamma13->"0.28",gamma32->"0.12",gamma33->"0.28"}}
{"1.3113138", "1.0877549", 27, {0,1,1,1,1,0.8186726154945156`,0,0,1}, 103, {b->"0.66",g1->"0.60",g2->"0.85",gamma12->"0.29",gamma13->"0.28",gamma32->"0.29",gamma33->"0.15"}}
{"1.3098851", "1.0152986", 49, {0,0,1,1,1,1,0.8953314362551189`,0,0}, 122, {b->"0.66",g1->"0.60",g2->"0.85",gamma12->"0.48",gamma13->"0.29",gamma32->"0.29",gamma33->"0.29"}}
{"1.3077114", "1.2281063", 140, {0,1,1,1,1,0,0.1670962683116804`,1,1}, 118, {b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.39",gamma13->"0.21",gamma32->"0.12",gamma33->"0.01"}}
{"1.3267301", "1.0365595", 146, {0,0,0,1,1,1,1,1,0.5043382572954628`}, 112, {b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.32",gamma13->"0.67",gamma32->"0.32",gamma33->"0.67"}}
{"1.3090361", "1.1926134", 85, {0,1,1,1,1,0.5752115726260862`,0,0,0}, 126, {b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.52",gamma13->"0.25",gamma32->"0.52",gamma33->"0.25"}}
{"1.3078205", "1.1610874", 71, {0,0,1,1,1,1,0,0.559346213232929`,0}, 153, {b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.47",gamma13->"0.43",gamma32->"0.43",gamma33->"0.24"}}
{"1.3076570", "1.1608870", 24, {0,0,1,1,1,1,0,0,0.5641901419722595`}, 155, {b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.48",gamma13->"0.43",gamma32->"0.24",gamma33->"0.43"}}
{"1.3073621", "1.0066454", 9, {0,1,0,1,0.934208283610358`,0,1,1,1}, 151, {b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.29",gamma13->"0.60",gamma32->"0.27",gamma33->"0.35"}}
{"1.3076627", "1.2553831", 76, {1,1,1,0,0,0,0.4168178849494415`,1,1}, 142, {b->"0.66",g1->"0.60",g2->"0.85",gamma12->"0.66",gamma13->"0.22",gamma32->"0.20",gamma33->"0.22"}}
{"1.3077255", "1.2258897", 155, {0,1,1,1,0.7240884340642132`,1,0,0,0}, 139, {b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.58",gamma13->"0.25",gamma32->"0.58",gamma33->"0.24"}}
{"1.3068603", "1.2865897", 20, {0,1,1,1,0,0,0.9016145028254624`,0,0}, 148, {b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.63",gamma13->"0.25",gamma32->"0.01",gamma33->"0.25"}}
{"1.3069863", "1.2374327", 64, {0,0,1,1,1,1,1,0.40115822638258286`,0}, 131, {b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.59",gamma13->"0.37",gamma32->"0.57",gamma33->"0.35"}}
{"1.3068338", "1.3068344", 50, {1,1,1,0,0,0.7068745339506713`,0,1,0}, 155, {b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.54",gamma13->"0.43",gamma32->"0.37",gamma33->"0.34"}}
{"1.3068345", "1.3068350", 71, {0,0,1,1,1,1,0,0.887831814312429`,0}, 147, {b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.54",gamma13->"0.43",gamma32->"0.28",gamma33->"0.39"}}
{"1.3068345", "1.3068350", 71, {0,0,1,1,1,1,0,0.887831814312429`,0}, 140, {b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.54",gamma13->"0.43",gamma32->"0.28",gamma33->"0.39"}}
{"1.3068345", "1.3068350", 71, {0,0,1,1,1,1,0,0.887831814312429`,0}, 141, {b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.54",gamma13->"0.43",gamma32->"0.28",gamma33->"0.39"}}
{"1.3068345", "1.3068350", 71, {0,0,1,1,1,1,0,0.887831814312429`,0}, 144, {b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.54",gamma13->"0.43",gamma32->"0.28",gamma33->"0.39"}}
{143, 122, 18, 37, 34, 35, 31, 44, 11, 1, 13, 40, 126, 105, 14, 108, 109, 161, 51, 118, 52, 41, 124, 5, 10, 42, 79, 27, 49, 140, 146, 85, 71, 24, 9, 76, 155, 20, 64, 50, 71, 71, 71, 71}
{"1.3068266", "1.3060772", 55, {1,1,1,0,0,0,0.6362031345810665`,0,1}, 120, {b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.52",gamma13->"0.44",gamma32->"0.02",gamma33->"0.12"}}
{"1.3068368", "1.3044207", 122, {1,1,0,0,0,0.21611310328482156`,1,1,1}, 179, {b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.55",gamma13->"0.42",gamma32->"0.20",gamma33->"0.42"}}
{"1.3068302", "1.3068032", 127, {0,1,1,1,0,0,0.6744939261264813`,1,0}, 230, {b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.53",gamma13->"0.43",gamma32->"0.01",gamma33->"0.01"}}
{"1.3068293", "1.3068309", 142, {0,1,1,1,1,0,0.03258791863959559`,0,1}, 180, {b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.53",gamma13->"0.43",gamma32->"0.01",gamma33->"0.11"}}
{"1.3068237", "1.3068260", 42, {0,1,0,1,0,0.2427271671609529`,1,1,1}, 163, {b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.52",gamma13->"0.43",gamma32->"0.01",gamma33->"0.01"}}
{31, 44, 11, 1, 13, 40, 126, 105, 14, 108, 109, 161, 51, 118, 52, 41, 124, 5, 10, 42, 79, 27, 49, 140, 146, 85, 71, 24, 9, 76, 155, 20, 64, 50, 71, 55, 122, 127, 142, 42}
{"1.3068367", "1.3068367", 42, {0,1,0,1,0,0.2165646627254926`,1,1,1}, 344, {b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.55",gamma13->"0.42",gamma32->"0.23",gamma33->"0.42"}}
loopAlgsI = {13, 40, 126, 105, 14, 108, 109, 161, 51, 118, 52, 41, 124, 5, 10, 42, 79, 27, 49, 140, 146, 85, 71, 24, 9, 76, 155, 20, 64, 50, 71, 55, 122, 127}
{"1.3163244", "1.1116152", 13, {1,1,1,0,0.38085859050769205`,1,0,0,0}, 454, {b->"0.65",g1->"0.60",g2->"0.85",gamma12->"0.32",gamma13->"0.53",gamma32->"0.32",gamma33->"0.01"}}
{"1.3068367", "1.3068367", 122, {1,1,0,0,0,0.21780591001051613`,1,1,1}, 452, {b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.55",gamma13->"0.42",gamma32->"0.19",gamma33->"0.41"}}
{105,14,108,109,161,51,118,52,41,124,5,10,42,79,27,49,140,146,85,71,24,9,76,155,20,64,50,71,55,122,127,13}
{"1.3068346","1.3055521",90,{0,1,1,1,0,0,0.8252222114889173`,0,1},603,{b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.54",gamma13->"0.42",gamma32->"0.27",gamma33->"0.40"}}
{"1.3068353","1.3068359",146,{0,0,0,1,1,1,1,1,0.18446060490444766`},636,{b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.55",gamma13->"0.42",gamma32->"0.27",gamma33->"0.40"}}
"No improvement. Removing 108"
StringJoin::string: "String expected at position \!\(1\) in \!\(Null <> \": {108, 109, 161, 51, 118, 52, 41, 124, 5, 10, 42, 79, 27, 49, 140, 146, 85, 71, 24, 9, 76, 155, 20, 64, 50, 71, 55, 122, 127, 13, 123, 90}\"\). \!\(\*ButtonBox[\">>\", ButtonStyle->\"Link\", ButtonFrame->None, ButtonData:>\"paclet:ref/StringJoin\", ButtonNote -> \"StringJoin::string\"]\)"
StringJoin::string: "String expected at position \!\(1\) in \!\(Null <> \": {108, 109, 161, 51, 118, 52, 41, 124, 5, 10, 42, 79, 27, 49, 140, 146, 85, 71, 24, 9, 76, 155, 20, 64, 50, 71, 55, 122, 127, 13, 123, 90}\"\). \!\(\*ButtonBox[\">>\", ButtonStyle->\"Link\", ButtonFrame->None, ButtonData:>\"paclet:ref/StringJoin\", ButtonNote -> \"StringJoin::string\"]\)"
{"1.3318275","0.9575359",35,{1,1,1,0,0,0,0.7406107379739791`,0,0},626,{b->"0.63",g1->"0.60",g2->"0.85",gamma12->"0.33",gamma13->"0.29",gamma32->"0.01",gamma33->"0.14"}}
{"1.3139492","0.9897104",152,{1,1,1,0,0,1,0.2911477916041027`,1,0},643,{b->"0.66",g1->"0.60",g2->"0.85",gamma12->"0.15",gamma13->"0.41",gamma32->"0.10",gamma33->"0.38"}}
{"1.3068367","1.3068367",59,{0,0,0,1,1,0.7370810587038342`,1,0,1},723,{b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.55",gamma13->"0.42",gamma32->"0.22",gamma33->"0.41"}}
"No improvement. Removing 109"
{161,51,118,52,41,124,5,10,42,79,27,49,140,146,85,71,24,9,76,155,20,64,50,71,55,122,127,13,123,90,35,152}
StringJoin::string: "String expected at position \!\(1\) in \!\(Null <> \": {109, 161, 51, 118, 52, 41, 124, 5, 10, 42, 79, 27, 49, 140, 146, 85, 71, 24, 9, 76, 155, 20, 64, 50, 71, 55, 122, 127, 13, 123, 90, 35, 152}\"\). \!\(\*ButtonBox[\">>\", ButtonStyle->\"Link\", ButtonFrame->None, ButtonData:>\"paclet:ref/StringJoin\", ButtonNote -> \"StringJoin::string\"]\)"
General::stop: "Further output of \!\(\*StyleBox[\(StringJoin :: string\), \"MessageName\"]\) will be suppressed during this calculation. \!\(\*ButtonBox[\">>\", ButtonStyle->\"Link\", ButtonFrame->None, ButtonData:>\"paclet:ref/message/General/stop\", ButtonNote -> \"General::stop\"]\)"
{"1.3068338","1.3068348",16,{0,0,0,1,1,0,0.9279536558853285`,1,1},779,{b->"0.67",g1->"0.60",g2->"0.85",gamma12->"0.66",gamma13->"0.26",gamma32->"0.01",gamma33->"0.02"}}
"No improvement. Removing 161"
*)


(* ::Subsection::Closed:: *)
(*Explore Tight Solution*)


sol=solBest;
algsIm=algsI29~Select~(Not@MemberQ[{(*9,42*)},#]&);
Manipulate[EvaluateAlgsByMass[#,algsIm]&@SolveLPatSol[
{g1->(g1/.sol),g2->(g2/.sol),b->mb,gamma12->mgamma12,gamma13->mgamma13,gamma32->mgamma32,gamma33->mgamma33},algsIm]
	,{{mb,b/.sol},0,1,.0001},{{mgamma12,gamma12/.sol},0,1,.001},{{mgamma13,gamma13/.sol},0,1,.001},{{mgamma32,gamma32/.sol},0,1},{{mgamma33,gamma33/.sol},0,1}];


(* ::Subsubsection::Closed:: *)
(*Other*)


(* ::Text:: *)
(*Here we can explore if adding the full set of constraints does not improve over the minimal set of 32.*)


solFullI=SolveLPatSol[solBest];Z/.solFullI
solI30=SolveLPatSol[solBest,algsI30];Z/.solI30


(* ::Text:: *)
(*We can use the full set of algorithms or our minimal set. We can tweak things and see that it looks maximal. Also we see that gamma32 and gamma33 don't affect the maximum.*)


sol=solBest;
Manipulate[{X/.#,solTemp=#;#}&@SolveLPatSol[{g1->(g1/.sol),g2->(g2/.sol),b->mb,gamma12->mgamma12,gamma13->mgamma13,gamma32->mgamma32,gamma33->mgamma33},algsI29]
	,{{mb,b/.sol},0,1,.0001},{{mgamma12,gamma12/.sol},0,1,.001},{{mgamma13,gamma13/.sol},0,1,.001},{{mgamma32,gamma32/.sol},0,1},{{mgamma33,gamma33/.sol},0,1}]


(* need 5 or 31 for smaller gamma33 *)
algsIm=algsI14
tsol=localMax2
Manipulate[EvaluateAlgsByMass[#,algsIm]&@SolveLPatSol[
{g1->(g1/.tsol),g2->(g2/.tsol),b->mb,gamma12->mgamma12,gamma13->mgamma13,gamma32->mgamma32,gamma33->mgamma33},algsIm]
	,{{mb,b/.tsol},0,1,.0001},{{mgamma12,gamma12/.tsol},0,1,.001},{{mgamma13,gamma13/.tsol},0,1,.001},{{mgamma32,gamma32/.tsol},0,1},{{mgamma33,gamma33/.tsol},0,1}]


(* ::Subsubsection::Closed:: *)
(*Check looseness*)


algsI=algsI12sym2
(* heuristic visual proof of algorithm set tightness; b held constant for simplicity (a little slow)*)
fullPlot=Plot3D[(Z/.SolveLPatSol[{g1->(g1/.sol),g2->(g2/.sol),b->(b/.sol),gamma12->mgamma12,gamma13->mgamma13,gamma32->.999*Min[.499,mgamma12],gamma33->.999*Min[.499,mgamma13]},algsI])
	          - (Z/.SolveLPatSol[{g1->(g1/.sol),g2->(g2/.sol),b->(b/.sol),gamma12->mgamma12,gamma13->mgamma13,gamma32->.001,gamma33->.001},algsI30]),
	{mgamma12,0.002,1.1},{mgamma13,0.002,1.1}(*,RegionFunction->Function[{mgamma12,mgamma13,delta},mgamma12+mgamma13<=1.3]*)]


fullPlot=Plot3D[{Z/.SolveLPatSol[{g1->(g1/.sol),g2->(g2/.sol),b->(b/.sol),gamma12->mgamma12,gamma13->mgamma13,gamma32->.999*Min[.499,mgamma12],gamma33->.999*Min[.499,mgamma13]},algsI]
	            ,Z/.SolveLPatSol[{g1->(g1/.sol),g2->(g2/.sol),b->(b/.sol),gamma12->mgamma12,gamma13->mgamma13,gamma32->.001,gamma33->.001},algsI30]},
	{mgamma12,0.002,1.1},{mgamma13,0.002,1.1},PlotStyle->{Red,Blue},PlotRange->{1.303,1.305731}]


fullPlot=Plot3D[{Z/.SolveLPatSol[{g1->(g1/.sol),g2->(g2/.sol),b->(b/.sol),gamma12->mgamma12,gamma13->mgamma13,gamma32->.999*Min[.499,mgamma12],gamma33->.999*Min[.499,mgamma13]},algsI]
	            ,Z/.SolveLPatSol[{g1->(g1/.sol),g2->(g2/.sol),b->(b/.sol),gamma12->mgamma12,gamma13->mgamma13,gamma32->.001,gamma33->.001},algsI30]},
	{mgamma12,.1,.8},{mgamma13,0.6,.9},PlotStyle->{Red,Blue},PlotRange->{1.300,1.305731}]


(Z/.SolveLPatSol[{g1->(g1/.sol),g2->(g2/.sol),b->(b/.sol),gamma12->.3,gamma13->.27,gamma32->.001,gamma33->.001},#])&/@{algsI9sym,algsI10sym2,algsI30,All}


(* ::Subsection:: *)
(*Dual*)


(* ::Subsubsection::Closed:: *)
(*Definition*)


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
	Table[{u[i], algMass//StyleMass, VisualMass[algMass,3,ImageSize->{60,20}],
			 algIndex, i}/.algsWithMass[[algIset[[i]]]],{i,1,Length[algIset]}]
]/.params


algsI=algsI13
sol=solBest;
solDual=SolveDualLP[sol,algsI];alpha/.solDual
Grid@SortBy[EvaluateDual[solDual,algsI],#[[2]]&]


(* ::Subsubsection:: *)
(*Manipulate*)


BigFractionStyle = Style[#, DefaultOptions -> {FractionBoxOptions -> {AllowScriptLevelChange -> False}}] &;
algsI=algsI30
algsI=solTightAll
(*algsI=Range[Length[rawMass]+1];*)
Length[algsI]
{b0,g10,g20,gamma120,gamma130,gamma320,gamma330}={b,g1,g2,gamma12,gamma13,gamma32,gamma33}/.sol2;
Manipulate[Module[{msolDual,msolOptBaseline,marginals,jointProbs,conditionalProbs},
	mparams1 = {b->pb,gamma12->pgamma12,gamma13->pgamma13,gamma32->pgamma32,gamma33->pgamma33,g1->pg1,g2->pg2};
    msolDual = SolveDualLP[mparams1,algsI,Join[u[#]==0&/@removeI,(u[#]>=eps1&)/@forceI]];
	msolOptBaseline = alpha/.SolveDualLP[mparams1,Range[Length[rawMass]+1]];
	marginals=Total[u[#]*mass[[algsI[[#]]]]&/@comboI]/Max[.0001,Total[u[#]&/@comboI]];
    jointProbs=Total[u[#]*(Transpose[#].#&@{mass[[algsI[[#]]]]})&/@comboI]/Max[.0001,Total[u[#]&/@comboI]];
	conditionalProbs=Table[jointProbs[[i,j]]/marginals[[j]],{i,1,Length@jointProbs},{j,1,Length@jointProbs}];
	BigFractionStyle@Column@{Row@{msolOptBaseline,"(Baseline)",1.305731},alpha, algsI[[comboI]],marginals~StyleMass~4,
		Row[{(*Grid[jointProbs],*)Grid[conditionalProbs]},Spacer@12]~StyleMass~4,VisualMass[marginals,3,ImageSize->{120,80}]
		,Grid@Select[SortBy[EvaluateDual[msolDual,algsI],-#[[1]]&],Chop[#[[1]]]>=0&]}/.msolDual
   ],{{pb,b0},0,1,.001},{{pg1,g10},.01,1,.001},{{pg2,g20},.01,1,.001},{{pgamma12,gamma120},.01,1.5,.001}
   ,{{pgamma13,gamma130},.01,1,.001},{{pgamma32,gamma320},.01,1,.001},{{pgamma33,gamma330},.01,1,.001}
   ,{{eps1,.001},0,1,.001},{{removeI,{}}},{{comboI,Complement[Range@Length@algsI,{1}]}},{{forceI,{}}}]


save=mparams1;
{b->#[[1]],g1->#[[2]],g2->#[[3]],gamma12->#[[4]],gamma13->#[[5]],gamma32->#[[6]],gamma33->#[[7]]}&[{b,g1,g2,gamma12,gamma13,gamma32,gamma33}/.save]


{b,g1,g2,gamma12,gamma13,gamma32,gamma33}/.sol


(* keep a record of potentially difficult points as regression tests for new algorithm sets *)
{save1,save2,save3,save4,save5,save6,save7}={b->#[[1]],g1->#[[2]],g2->#[[3]],gamma12->#[[4]],gamma13->#[[5]],gamma32->#[[6]],gamma33->#[[7]]}&/@{
{0.6715331873666895`,0.642`,0.833`,0.526`,0.323`,0.21167853121269323`,0.38689227778230223`},
{0.601`,0.642`,0.833`,0.21167853121269323`,0.38689227778230223`,0.21167853121269323`,0.38689227778230223`},
{0.670401615890807`,0.642`,0.833`,0.13850059367175058`,0.3275635475924704`,0.010000210741811375`,0.24844458802882918`},
{0.668327090916148`,0.642`,0.833`,0.2793271784224084`,0.2391828008877306`,0.14020302569038923`,0.23918280088767704`},
{0.668327090916148`,0.642`,0.833`,0.01`,1.`,0.01`,0.01`},
{0.6700417833928548`,0.642`,0.833`,0.257570731473704`,0.2826650145676018`,0.24635318616467414`,0.24185408887858426`},
{0.6695385103727721`,0.642`,0.833`,0.3`,0.28`,0.3`,0.28`}};


(* ::Subsubsection::Closed:: *)
(*Scratch*)


tsol=save;
algsI12sym2
VisualMass[mass[[#]]/.tsol,3,ImageSize->{100,100}]&/@%
(* note: algs10 changes value with change in gamma33. algs30 doesnt *)
(* TODO try adding F1A complements of existing algos? *)
(* TODO try adding counter shift to 168*)


{{{147,125},{0,0.`,0.`,0.9999999999999999`,0.9999999999999999`,0.9999999999999999`,0.9752151951321986`,0.16630752722041464`,0.16630752722040393`}}
,{{147,125,72},{0,0.`,0.46791978156020125`,1.`,1.`,1.`,0.556408726971795`,0.5564087269718222`,0.5564087269718165`}}
,{{147,125,10},{0,0.8444262346451141`,0.`,1.`,0.1555737653548859`,0.1555737653548859`,0.8702993228616422`,0.8702993228616541`,0.8702993228616526`}}
,{{10,86},{0,1.`,0.38170595276382563`,1.`,0.38170595276382563`,0.38170595276382563`,0.6182940472361815`,0.6182940472361743`,0.6182940472361743`}}
,{{72,86},{0,0.792114941592999`,1.`,1.`,1.`,1.`,0.20788505840702212`,0.2078850584070011`,0.2078850584070011`}}};
Grid[{First/@%, VisualMass[#[[2]]/.tsol,3,ImageSize->{100,100}]&/@%}]


(* ::Subsubsection::Closed:: *)
(*Vary Sets*)


(* identify algorithms which are definitely not needed at this point*)
talgsI=algsI
target=Z/.SolveLPatSol[save7,talgsI]
forceUseEachI=Sort[Table[{alpha/.SolveDualLP[save7,talgsI,{u[i]>=.0001}],talgsI[[i]]},{i,1,Length@talgsI}]~Select~(#[[1]]>target+.000001&)]


(* identify algorithms which can't be removed at this point *)
talgsI=algsI;tsol=save7;
target=Z/.SolveLPatSol[tsol,talgsI]
nonRemovableI=Last/@(Table[{alpha/.SolveDualLP[tsol,talgsI~Complement~{algI}],algI},{algI,talgsI}]~Select~(#[[1]]>target+.000001&))
removableI=talgsI~Complement~nonRemovableI


(* identify single new algorithms which can help at this point - though it's possible multiple algorithms may be needed in conjunction for benefit *)
talgsI=algsI
beatThis = Z/.SolveLPatSol[save4,talgsI]
tryAddRes=Sort[Table[{alpha/.SolveDualLP[save4,talgsI~Append~algI],algI},{algI,Complement[algsI30,talgsI]}]~Select~(#[[1]]<beatThis-.000001&)]
tryAddI=Last/@tryAddRes


SolveNLP[g1/.solBest,g2/.solBest,100,algsI]


(* ::Subsubsection::Closed:: *)
(*Algo Minimization*)


(* remove redundant algos for that point - this didn't seem to affect outcome - there weren't that many duplicates *)
(* first normalize gamma3's to equal gamma1's - probably doesnt matter *)
tsol=solBest~Select~(Not@MemberQ[{gamma32,gamma33},#[[1]]]&)//Join[#,{gamma32->gamma12,gamma33->gamma13}/.#]&;
fixedMasses = mass/.tsol;
uniqueI= Position[fixedMasses, #][[1,1]]&/@Union[fixedMasses] //Sort;
uniqueI=Complement[uniqueI,{9,42}];

(* Identify critical algos: those which are strictly required in any minimal set. *)
nonzeroVars=SolveDualLP[tsol,uniqueI]~Select~(#[[2]]>10^-5&);
uvars = Select[First/@nonzeroVars,Not@MemberQ[Append[vars,alpha],#]&];
uSubscript[u[x_]]:=x
usefulAlgI = uniqueI[[uSubscript/@uvars]];
costWithAlgIRemoved=Table[{i,alpha/.SolveDualLP[tsol,Complement[uniqueI,{i}]]},{i,usefulAlgI}]~SortBy~(-Last@#&);
optDual=alpha/.SolveDualLP[tsol,uniqueI];
criticalI=#[[1]]&/@Select[costWithAlgIRemoved,#[[2]]>optDual+.00000001&]


tsol=SolveDualLP[tsol,uniqueI];
alpha/.solDual
Grid@SortBy[EvaluateDual[tsol,uniqueI],#[[2]]&];


(* ::Subsection:: *)
(*Optimize g*)


{g1hat,g2hat}


(* used this to run batch jobs, to check grids of g values *)
sampleG12=Flatten[Table[{g1,g2(*+(g1-.641)*)},{g1,.60,.62,.01},{g2,.85,.87,.01}],1]
sampleG12=Table[{g1,g1},{g1,.2,1,.1}]
(*sampleG12={}*)
Length@sampleG12
t1=AbsoluteTime[];
assumptions={};(*{gamma32==gamma33==.01};*)
solGrid=ParallelTable[Module[{sol},
		sol=SolveNLP[g12[[1]],g12[[2]],800,solTightAll];
		Print@{g12[[1]],g12[[2]],Z/.sol};
		sol
	],{g12,sampleG12}];
solGrid12=solGrid
t2=AbsoluteTime[]; (t2-t1)/60//N


SortBy[{g1,g2,Z}/.#&/@Join[solGrid10,solGrid11],Last]
{g1hat,g2hat}


ListPlot3D[{g1,g2,Z}/.#&/@Join[solGrid10,solGrid11]]
ListPlot3D[{g1,g2,gamma12}/.#&/@Join[solGrid10,solGrid11]]


(* ::Subsubsection:: *)
(*Candidate*)


solBest={b->0.6715127810784994`,d111->0.055963882020552566`,d112->0.024566028588756693`,d113->0.044382312521878575`,d1131->0.07833174040696779`,d1132->0.03191242717384443`,d1133->0.06436808200122764`,d121->0.0615109239206875`,d122->0.08535007687653587`,d123->0.15086489170859027`,d1231->0.05510170532066508`,d1232->0.02638660130823359`,d1233->0.05326320777040984`,d131->0.04390224038831524`,d132->0.060288309420837516`,d133->0.09966363978920066`,d1331->0.2888475478539012`,d1332->0.14158362803831262`,d1333->0.26128016585357877`,d211->4.3086477656006447`*^-11,d212->0.013889664296362434`,d213->0.02224933564507619`,d221->4.308663792450089`*^-11,d222->0.023443809927846664`,d223->0.03764077449001071`,d231->4.293118574700673`*^-11,d232->0.025316459747375866`,d233->0.04866256720166031`,d311->0.034554050125961785`,d312->0.0215209795207525`,d313->0.036923994494867156`,d321->0.047891537407521584`,d322->0.02236426042449164`,d323->0.03915231832043774`,d331->0.13766700693306533`,d332->0.06030294467428174`,d333->0.12143005117084818`,g1->0.6403333333333333`,g2->0.8336666666666666`,gamma12->0.22441408459808865`,gamma13->0.3888391913009372`,gamma32->0.19966799214841638`,gamma33->0.37850452334289636`,X->1.3057328485283552`,g1->0.6403333333333333`,g2->0.8336666666666666`};
SolveNLP[g1/.solBest,g2/.solBest,10,algsI29]



