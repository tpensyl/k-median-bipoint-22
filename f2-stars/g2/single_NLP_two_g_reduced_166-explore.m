(* ::Package:: *)

(* ::Title:: *)
(*F2-Stars*)


SetOptions[EvaluationNotebook[],CellContext->Notebook, PrintPrecision->9]


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


Cf1[d1_,d2_,p1_,p2_,g_]:=p2*d2+(1-p2)*d1+(1-p2)*(1-p1)*g*(d1+d2)
(* If \[Sigma]_X(i1)!=i2, then we may try connecting to both before falling back on \[Sigma]_Y(i1) *)
Cf1b[d1_,d2_,p1_,p2_,p3_,g1_,g2_]:=p2*d2+(1-p2)*d1+(1-p2)*(1-p1)*(p3*g1+(1-p3)(g2))*(d1+d2)

(*## # Copy and paste from python script ## #*)
(* Let me know if I should consider some other notation, this is a little messy, especially the 'd' variables  *)
cost[p11_,p12_,p13_,p21_,p22_,p23_,p31_,p32_,p33_] := Total@{
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


(* ::Subsubsection::Closed:: *)
(*Probability Mass*)


(* ::Text:: *)
(*Let A(p11,p12,p13,p21,p22,p23,p31,p32,p33) give proportions.*)


mass = {{0,Min[1,Max[0,(b - gamma13 - gamma32)/gamma12]],1,1,1,Min[1,Max[0,(b - gamma32)/gamma13]],Max[0,(-b + gamma12 + gamma13 + gamma32 + gamma33)/(gamma32 + gamma33 - 1)],Min[1,b/gamma32],Min[1,Max[0,(b - gamma12 - gamma13 - gamma32)/gamma33]]},
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


(* ::Subsubsection::Closed:: *)
(*Variables and Constraints:*)


Length@mass
(*mass=mass/.{gamma32->Min[gamma12,0.9999999-gamma33]};
mass=mass/.{gamma33->Min[0.9999998,gamma13]};*)
algs=cost@@#&/@mass;
algsWithMass=Table[{algCost->cost@@mass[[i]],algMass->Style[mass[[i]],PrintPrecision->2],algIndex->i},{i,1,Length[mass]}];
constrAlg = X<=#&/@algs;


(*## # Copy and paste from python script ## #*)
varD1 = {d111,d112,d113,d121,d122,d123,d131,d132,d133,d1131,d1132,d1133,d1231,d1232,d1233,d1331,d1332,d1333};
varD2 = {d211,d212,d213,d221,d222,d223,d231,d232,d233,d311,d312,d313,d321,d322,d323,d331,d332,d333};
gammaVar1 = {gamma12,gamma13};
gammaVar3 = {gamma32,gamma33};
varNonLin = Union[gammaVar1,gammaVar3,{b,g1,g2}];
(*## ## ##*)
vars=Union[varD1,varD2,{X,b},gammaVar1,gammaVar3];
(*constrD1D2=MapThread[#1<=#2&,{varD2,varD1}];*)
constrBasic = Join[{X>=0,0<=b<=1},#>=0&/@Union[varD1,varD2,gammaVar1,gammaVar3],MapThread[#1<=#2&,{gammaVar3,gammaVar1}],{Total[gammaVar3]<=1},{Total[varD1]*(1-b)+Total[varD2]*b==1}];
constrAlgLiSven = X<=b*(3-2b)Total[varD2]+(1-b)*Total[varD1];
(* TODO: Define gamma3s in terms of gamma1s to reduce number of non-linear variables, might probably reduce execution time(?) *)


(* ::Text:: *)
(*We will fix the value of g1,g2, and let the adversary set the mass variable gamma*)


(* ::Subsubsection:: *)
(*Define NLP*)


(* TODO allow specify starting point? *)
Clear@SolveNLP
SolveNLP[g1hat_,g2hat_,iter_,algI_:;;]:=
	NMaximize[{X, constrAlg[[algI]], constrBasic, constrAlgLiSven, g1==g1hat, g2==g2hat,
		.63 <= b <= .74, .01 <= gamma12 <= .99, .01 <= gamma13 <= .99, X>=.5, (* manual hints *)
		.01<=gamma32+gamma33<=.99, .01<=gamma32, .01<=gamma33 (* hints *)
	}, vars~Union~{g1,g2}, MaxIterations->iter][[2]]
(*SolveNLP[g1hat,g2hat,100]*)


foo[g1hat_,g2hat_,iter_:30,x_:;;]:=6
foo[1,2,3,4]


(* If we fix non-linear variables, remaining system is linear and very fast/accurate *)
SolveLP[nonLinParams_,algI_:;;]:=Maximize[{X, constrAlg[[algI]], constrBasic, constrAlgLiSven}/.nonLinParams,Union[varD1,varD2,{X}]][[2]]~Join~nonLinParams;
SolveLPatSol[fullSol_,algI_:;;]:=SolveLP[ExtractNonLin[fullSol], algI]
ExtractNonLin[sol_]:=Select[sol,MemberQ[varNonLin,#[[1]]]&]


(* ::Subsection::Closed:: *)
(*Utility Methods*)


EvaluateAlgs[params_,algIset_:;;]:=(
		{algCost, Style[algMass,PrintPrecision->2], algIndex}/.#&/@algsWithMass[[algIset]]
	)/.params
EvaluateAlgsNice[params_,algIset_:;;]:=Grid[SortBy[EvaluateAlgs[params,algIset],First]~Prepend~{"Alg Cost ", "Alg Mass","Alg Index"},Alignment->Left]


(* ::Subsection:: *)
(*Find Minimal Subset*)


g1hat= 0.6;
g2hat= 0.85;
algsI={161,51,118,52,41,124,5,10,42,79,27,49,140,146,85,71,24,9,76,155,20,64,50,71,55,122,127,13,123,90,35,152};
Length@algsI


loopAlgsI = {};
maxIndices=0;  (* set this up higher to enable *)
maxIterations=1000;
While[Length[loopAlgsI]<maxIndices,
    {time, loopSol} = Timing@SolveNLP[g1hat,g2hat,maxIterations,loopAlgsI]; 
	loopSolMoreAccurate = SolveLPatSol[loopSol,loopAlgsI]; 
	cheapestAlg = SortBy[algsWithMass/.loopSolMoreAccurate, algCost/.#&][[1]];
	Print[{NumberForm[X/.loopSol,{8,7}], NumberForm[algCost,{8,7}], algIndex, Chop[algMass,.0001], Round@time, NumberForm[ExtractNonLin[loopSol],{3,2}]}/.cheapestAlg];
	If[(algCost/.cheapestAlg) <= (X/.loopSolMoreAccurate) - .00001,
		AppendTo[loopAlgsI, algIndex/.cheapestAlg],
		(* if there's no good algo to add, cycle an old one instead *)
		Print["No improvement. Removing "<>ToString@loopAlgsI[[1]]]<>": "<>ToString@loopAlgsI; loopAlgsI = loopAlgsI[[2;;]]
	]
]


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


(* ::Subsection:: *)
(*Explore Tight Solution*)


(* ::Text:: *)
(*Here we can explore if adding the full set of constraints does not improve over the minimal set of 32.*)


nonLinSol = {g1->0.6`,g2->0.85`,b->0.6693903931991064`,gamma12->0.624013`,gamma13->0.26546`,gamma32->0.010000140936428275`,gamma33->0.016320121313746373`};
algsI = {161,51,118,52,41,124,5,10,42,79,27,49,140,146,85,71,24,9,76,155,20,64,50,71,55,122,127,13,123,90,35,152};
{optFullI, solFullI} = {X/.#,#}&@SolveLPatSol[nonLinSol]
{optMinimalI, solMinimalI} = {X/.#,#}&@SolveLPatSol[nonLinSol,algsI]


(* ::Text:: *)
(*This uses the full set of algorithms, we can tweak things and see that it looks maximal. Also we see that gamma32 and gamma33 don't affect the maximum.*)


sol=solFullI;
Manipulate[{X/.#,#}&@SolveLPatSol[{g1->g1hat,g2->g2hat,b->mb,gamma12->mgamma12,gamma13->mgamma13,gamma32->mgamma32,gamma33->mgamma33}]
	,{{mb,b/.sol},0,1,.001},{{mgamma12,gamma12/.sol},0,1,.001},{{mgamma13,gamma13/.sol},0,1,.001},{{mgamma32,gamma32/.sol},0,1},{{mgamma33,gamma33/.sol},0,1}]


(* ::Subsection:: *)
(*Optimize g*)


(* TODO *)


(* ::Subsection:: *)
(*Result*)


algsI
Length@algsI
{g1hat,g2hat}
sol=SolveNLP[g1hat,g2hat,1000,algsI]
SolveLPatSol[sol,algsI]


(* ::Text:: *)
(*By setting g1=.6 and g2=.85, we get approximation factor 1.30684204*)
(**)
(*I think this NLP could be simplified by padding such that |F2C|=min{|F2B|,|Y|}, to eliminate need for gammaC variable. However, in my attempts to do so, it didn't actually seem to speed up the NLP, if anything it made it less likely to converge to the correct solution.*)
(**)
(*Fortunately, adversary appears unable to take advantage of the variables gamma32, gamma33, as their value doesn't seem to affect the optima.*)
