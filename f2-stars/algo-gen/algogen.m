(* ::Package:: *)

(* ::Title:: *)
(*Algorithms Generation*)


SetOptions[EvaluationNotebook[],CellContext->Notebook, PrintPrecision->9]


(* ::Section:: *)
(*Generating Algorithms*)


(* ::Subsection:: *)
(*Create Variables and Mass Equation*)


createVar[symb_,num_]:=ToExpression[symb<>ToString[num]];

initialize[t_]:=(
	n = t+1;
	gammaAs = Table[createVar["gammaA",i],{i,1,n}];
	gammaCs = Table[createVar["gammaC",i],{i,1,n}];
	gammaCs = gammaCs/.{gammaC1->1-Total[gammaCs[[2;;]]]};
	pAs = Table[createVar["pA",i],{i,1,n}];
	pBs = Table[createVar["pB",i],{i,1,n}];
	pCs = Table[createVar["pC",i],{i,1,n}];
	varp = Union[pAs,pBs,pCs];
	cond = Union[{0<b<1},0<#<1&/@gammaCs,0<=#<=1&/@varp,MapThread[#1<=#2&,{gammaCs[[2;;]],gammaAs[[2;;]]}]];
	massExpr= Total[MapThread[(#1+#2)#3&,{pAs,pBs,gammaAs}]]+Total[MapThread[#1*#2&,{pCs,gammaCs}]]-Total[gammaAs]-b == 0;
);


(* ::Subsection:: *)
(*Generate Valid Base Algorithms*)


isValid[num_]:=Module[{bitString,flag,i,prev,next},
	bitString = Reverse[IntegerDigits[num,2,3*n]];
	flag=True;
	For[i=1,i<=n,i++,
		prev = bitString[[n+1;;n+i]];next = bitString[[2*n+i;;3*n]];
		If[(bitString[[i]]==0 )&&(MemberQ[prev,0])&&MemberQ[next,0],flag=False;Break[];];
		If[(i==1)&&(bitString[[i]]==1)&&(bitString[[n+i]]==1),flag=False;Break[];];
		If[(i==1)&&(bitString[[i]]==0)&&(bitString[[n+i]]==0),flag=False;Break[];];
	];
	Return[flag];
];


getValidAlgos:=Module[{ds,curr,w,i,curMass,res,val,numer,denom,w1,w2},
	ds = ConstantArray[{},{2^(3*n),3*n}];
	For[curr=0,curr<2^(3*n),curr++,
		If[isValid[curr],
			w = Reverse[IntegerDigits[curr,2,3*n]];
			For[i=2,i<=3*n,i++,
				If[(i==n+1)||(w[[i]]==1),Continue[]];
				curMass = massExpr/.MapThread[If[#1===varp[[i]],##&[],#1->#2]&,{varp,w}];
				res = Solve[curMass,varp[[i]]];
				If[Length[res]==0,Continue[]];
				val = Normal@(varp[[i]]/.res[[1]]);
				numer = Numerator[val];denom = Denominator[val];
				w1 = Reduce[FullSimplify[numer>=0],b];
				w2 = Reduce[FullSimplify[numer-denom<=0],b];
				If[w1===False||w2===False,Continue[]];
				If[w1===True,,ds[[curr,i]]={Last[w1]}];
				If[w2===True,,ds[[curr,i]]=Union[ds[[curr,i]],{Last[w2]}]];
				If[ds[[curr,i]]==={},,ds[[curr,i]] = Union[{val},{ds[[curr,i]]}]];
			];
		];
	];
	Return[ds];
];


(* ::Subsection:: *)
(*Generating All Chains*)


getConstraints[ds_]:=Module[{indices,combs,output,i,rem,perms,i0,j,out1,w,algo,ind,curr,flag,intw,ind1,expr,conds},
	indices = Drop[Drop[Range[3*n],{n+1}],{1}];
	combs = Subsets[indices,{n-1}];
	output = {};
	For[i=1,i<=Length[combs],i++,
		rem = Complement[indices,combs[[i]]];
		perms = Permutations[rem];
		For[i0=0,i0<=1,i0++,
			For[j=1,j<=Length[perms],j++,
				out1 = {};
				w = ConstantArray[0,3*n];algo = ConstantArray[0,3*n];
				w[[1]] = i0;w[[n+1]] = Mod[i0+1,2];algo[[1]] = i0;algo[[n+1]]=Mod[i0+1,2];
				For[ind=1,ind<=Length[combs[[i]]],ind++,w[[combs[[i]][[ind]]]]=1;algo[[combs[[i]][[ind]]]]=1];
				flag=0;curr=0;
				For[ind=1,ind<=Length[perms[[j]]],ind++,
					intw = FromDigits[Reverse[w],2];ind1 = perms[[j]][[ind]];
					If[ds[[intw,ind1]]==={},flag=1;Break[],
						{expr,conds} = ds[[intw,ind1]];
						out1=Append[out1,{intw,ind1}];
						If[(curr==0)&&(Length[conds]>1||!(Head[conds[[1]]]===LessEqual)),flag=1;Break[]];
						If[Length[conds]==1,
							If[curr==0,algo[[ind1]]=Min[1,expr],algo[[ind1]]=Max[0,expr];flag=2;Break[]];,
							algo[[ind1]] = Min[1,Max[0,expr]];
						];
						w[[ind1]] = 1;curr++;
					];
				];
				If[flag==2,output=Append[output,{algo,out1}]];
			];
		];
	];
	output=DeleteDuplicates[output];
	Return[output];
];


(* ::Subsection:: *)
(*Generate Minimal Set of Chains*)


reduceConstraints[constraints_,mass_]:=Module[{chosen,algos,cons,consNum,algoNum,i,j,rem,maxCons,maxVal,temp,temp1},
	chosen = {};
	algos = DeleteDuplicates[Flatten[#[[2]]&/@constraints,1]];
	algos = MapThread[#1->#2&,{algos,Range[Length[algos]]}];
	cons = (#[[2]]&/@constraints)/.algos;
	consNum = Length[#]&/@cons;
	algoNum = ConstantArray[{},Length[algos]];
	For[i=1,i<=Length[constraints],i++,
		For[j=1,j<=Length[cons[[i]]],j++,algoNum[[ cons[[i]][[j]]]]=Union[algoNum[[cons[[i]][[j]]]],{i}] ];
	];
	rem = Length[algos];
	While[rem>0,
		maxCons = -1;maxVal = 0;
		For[i=1,i<=Length[consNum],i++,
			If[maxVal<consNum[[i]],maxVal=consNum[[i]];maxCons = i];
		];
		For[i=1,i<=Length[cons[[maxCons]]],i++,
			temp = cons[[maxCons]];
			If[algoNum[[temp[[i]]]]==={},Continue[]];
			rem--;
			For[j=1,j<=Length[algoNum[[temp[[i]]]]],j++,
				temp1 = algoNum[[temp[[i]]]];
				consNum[[temp1[[j]]]]--;
			];
			algoNum[[temp[[i]]]] = {};
		];
		chosen = Append[chosen,mass[[maxCons]]];
	];
	Return[chosen];
];


(* ::Section:: *)
(*Generate and Save Algorithms*)


(* ::Subsection:: *)
(*One g-threshold (t=1)*)


t = 1;
initialize[t];


$Assumptions = And@@cond;
ds = getValidAlgos;
$Assumptions = True;


constraints = getConstraints[ds]; Print[Length[constraints]];
mass = #[[1]]&/@constraints;


reducedMass = reduceConstraints[constraints,mass];
Print[Length[reducedMass]];


(* ::Subsubsection:: *)
(*Saving mass and reducedMass*)


massFile = FileNameJoin[{NotebookDirectory[], "One-g-mass-"<>ToString[Length[mass]]<>".wl"}]
reducedMassFile = FileNameJoin[{NotebookDirectory[], "One-g-reduced-mass-"<>ToString[Length[reducedMass]]<>".wl"}]
DeleteFile[massFile];DeleteFile[reducedMassFile];
Save[massFile,{mass}];
Save[reducedMassFile,{reducedMass}];


(* ::Subsection:: *)
(*Two g-thresholds (t=2)*)


t = 2;
initialize[t];


$Assumptions = And@@cond;
ds = getValidAlgos;
$Assumptions = True;


constraints = getConstraints[ds]; Print[Length[constraints]];
mass = #[[1]]&/@constraints;


reducedMass = reduceConstraints[constraints,mass];
Print[Length[reducedMass]];


(* ::Subsubsection:: *)
(*Saving mass and reducedMass*)


massFile = FileNameJoin[{NotebookDirectory[], "Two-g-mass-"<>ToString[Length[mass]]<>".wl"}]
reducedMassFile = FileNameJoin[{NotebookDirectory[], "Two-g-reduced-mass-"<>ToString[Length[reducedMass]]<>".wl"}]
DeleteFile[massFile];DeleteFile[reducedMassFile];
Save[massFile,mass];
Save[reducedMassFile,reducedMass];


(* ::Subsection::Closed:: *)
(*Three g-thresholds (t=3)*)


t = 3;
initialize[t];


$Assumptions = And@@cond;\[AliasDelimiter]
ds = getValidAlgos;
$Assumptions = True;


constraints = getConstraints[ds]; Print[Length[constraints]];
mass = #[[1]]&/@constraints;


reducedMass = reduceConstraints[constraints,mass];
Print[Length[reducedMass]];






(* ::Subsubsection:: *)
(*Saving mass and reducedMass*)


massFile = FileNameJoin[{NotebookDirectory[], "Three-g-mass-"<>ToString[Length[mass]]<>".wl"}]
reducedMassFile = FileNameJoin[{NotebookDirectory[], "Three-g-reduced-mass-"<>ToString[Length[reducedMass]]<>".wl"}]
(*DeleteFile[massFile];*)DeleteFile[reducedMassFile];
(*Save[massFile,mass];*)
Save[reducedMassFile,reducedMass];
