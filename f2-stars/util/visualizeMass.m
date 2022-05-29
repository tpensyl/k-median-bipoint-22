(* ::Package:: *)

(* A widget for visualizing mass sets. *)
Clear[VisualMass,VisualMassSquare]
Options[VisualMass] = {ImageSize -> {40,20}};
(* n is the number of partitions of F1 *)
VisualMassSquare[i_,j_,mass_]:=Rectangle[{i,j},{i+1,j+mass}]
VisualMass[p_List,n_,OptionsPattern[]]:=Module[{massGrid,visualGrid},
    massGrid=Table[p[[i+n(j-1)]],{j,1,3},{i,1,n}][[{3,1,2}]];
	visualGrid=Table[VisualMassSquare[i-1,j-1,massGrid[[j,i]]],{j,1,3},{i,1,n}];
	Graphics[
		Join[
			{Gray, Rectangle[{0,0},{n,3}]},
			{Black}, visualGrid[[1]],
			{Black}, visualGrid[[2]],
			{Black}, visualGrid[[3]]
	],PlotRange->{{0,n},{0,3}},ImageSize->OptionValue[ImageSize],AspectRatio->Full]
]

(*
VisualMass[Table[RandomReal[],{i,1,9}],3]
VisualMass[Table[RandomReal[],{i,1,6}],2,ImageSize->100]
*)
