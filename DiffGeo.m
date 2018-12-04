(* ::Package:: *)

(*ToDo*)
(*add ? style documentation*)


RankError::oob="The length of `1` and `2` must be the same as the up and down rank of the tensor.";
RankError::depth="The sum of `1` and `2` must be the same as the depth of the data matrix,`3` .";
indexError::mismatch="The two tensors must have the same indices to be added together";
indexError::declerationmismatch="the provided index lists must be the same length as the up and down ranks of the listed tensors";
typeError::wrongtype="Multiplication between a tensor and objects of type `1` is not defined";
dimmError::depth="dimensionality of metric and coordinates must be equal";


MakeManifold[g_,coordinates_]:= Module[{},
If[(Length[coordinates]==  Length[g[[1]]] && SquareMatrixQ[g]),
manifold[<|metric-> g,coords-> coordinates,NDim-> Length[coordinates],invmetric -> Simplify[Inverse[g]]|>],
Message[dimmError::depth]]
]


MakeTensor[matrix_, DownRank_,UpRank_,m_] := Module[{tmp,function,metric},
tmp = Null;
If[If[Head @ matrix === List, ArrayDepth[matrix],0]==DownRank+UpRank,
		tmp = <|data->matrix, downrank-> DownRank, uprank-> UpRank,manifold -> m|>;,
		Message[RankError::depth,DownRank,UpRank,matrix]];
		Tensor[tmp]
]


(* Contract TDownth index with TUpth index*)
Contract[T_,TDown_,TUp_] :=Module[{downlist,uplist,ii, result},
downlist = ConstantArray[;;,T[downrank]];
downlist[[TDown]] = ii;
uplist = ConstantArray[;;,T[uprank]];
uplist[[TUp]] = ii;
result = FullSimplify[Sum[T[[downlist,uplist]],{ii,1,T[manifold][NDim]}]];
MakeTensor[result,T[downrank]-1,T[uprank]-1,T[manifold]]
]


TProduct[T1_,T2_]:=Module[{result,numIndices,dummyvars,dummyvarsReordered},
Quiet[
If[Not[Head @ T2[data]=== List] || Not[Head @ T1[data]=== List],
	result = T1[data] T2[data];,
	
	result = Outer[Times,T1[data],T2[data]];
	numIndices = T1[downrank]+T1[uprank]+T2[downrank]+T2[uprank];
	dummyvars = Table[Symbol["var"<>ToString[i]],{i,numIndices}];
	dummyvarsReordered = Join[Table[dummyvars[[i]],{i,1,T1[downrank]}],Table[dummyvars[[i]],{i,T1[downrank]+T1[uprank]+1,T1[downrank]+T1[uprank]+T2[downrank]}],Table[dummyvars[[i]],{i,T1[downrank]+1,T1[downrank]+T1[uprank]}],Table[dummyvars[[i]],{i,T1[downrank]+T1[uprank]+T2[downrank]+1,T1[downrank]+T1[uprank]+T2[downrank]+T2[uprank]}]];
	result = Table@@Flatten[{{Part@@Flatten[{{result},dummyvars},1]},Table[{v,1,T1[manifold][NDim]},{v,dummyvarsReordered}]},1];
];
MakeTensor[result,T1[downrank]+T2[downrank],T1[uprank]+T2[uprank],T1[manifold]]
,Part::pkspec1]]


(* arguments will have form {T,{i,j,k},{l,m,n}}. Down indices must ALWAYS come first. *)
Einstein[{T_,argD_,argU_}] := Module[{varU,varD,contract,contractVars, tmp,out},
tmp = T;
varD = argD;
varU = argU;
contractVars = Table[If[MemberQ[varD,elem],Flatten[{Position[varD,elem],Position[varU,elem]}],## &[]],{elem,varU}];
If[Length[contractVars]!=0, tmp = Contract[T,contractVars[[1,1]],contractVars[[1,2]]];
varD = Delete[varD,contractVars[[1,1]]];
varU = Delete[varU,contractVars[[1,2]]];
contractVars = Delete[contractVars,1];];
out = {tmp,varD,varU};
If[Length[contractVars]!=0, Einstein[out],out]
]
(* define for two arguments *)
Einstein[{T1_,argD1_,argU1_},{T2_,argD2_,argU2_}] := Einstein[{TProduct[T1,T2],Join[argD1,argD2],Join[argU1,argU2]}]
(* define for three or more arguments *)
Einstein[{T1_,argD1_,argU1_},{T2_,argD2_,argU2_},{T3___,argD3___,argU3___}] := Einstein[Einstein[{T1,argD1,argU1},{T2,argD2,argU2}],{T3,argD3,argU3}]


StripIndices[IndexedTensor_]:=IndexedTensor[[1,1]]


(*Ensures compatability with tensor wrapper*)
Tensor[T_][downrank]^:=T[downrank];
Tensor[T_][manifold]^:=T[manifold];
Tensor[T_][uprank]^:=T[uprank];
Tensor[T_][data]^:=T[data];
manifold[M_][coords]^:=M[coords];
manifold[M_][metric]^:=M[metric];
manifold[M_][invmetric]^:=M[invmetric];
manifold[M_][NDim]^:=M[NDim];

Simplify[Tensor[T_]]^:= MakeTensor[Simplify[T[data]],T[downrank],T[uprank],T[manifold]];
Simplify[Superscript[Subscript[Tensor[T_], down_],up_]]^:= Superscript[Subscript[MakeTensor[Simplify[T[data]],T[downrank],T[uprank],T[manifold]], down],up];


(*define addition between two tensors*)
Superscript[Subscript[Tensor[T1_], down1_],up1_]+Superscript[Subscript[Tensor[T2_], down2_],up2_]^:= Module[{varsums,indices,tensorData},
(*verify that the indeces are the same on both tensors*)
If[Sort[down1]===Sort[down2] && Sort[up1]===Sort[up2],

	indices = Flatten[{down1,up1}];
	varsums = Table[{v,1,T1[manifold][NDim]},{v,indices}];
	tensorData = Table[Tensor[T1][[down1,up1]]+Tensor[T2][[down2,up2]],##]&@@ varsums;
	Superscript[Subscript[MakeTensor[tensorData,T1[downrank],T2[uprank],T1[manifold]], down1],up1],
	
	Message[indexError::mismatch]]
];


(*define scalar multiplication of a tensor*)
a_ Superscript[Subscript[Tensor[T_], down_],up_]^:= If[NumericQ[a] || Not[ValueQ[a]],Superscript[Subscript[MakeTensor[a Tensor[T][data],T[downrank],T[uprank],T[manifold]], down],up],Message[typeError::wrongtype,Head @ a]]


(*add compatability with derivatives of arbitrary order*)
f[a_,b_]:= a[b]
Subscript[D, i_][ Superscript[Subscript[Tensor[T_], downIndices_],upIndices_]]^:=Module[{newdata},
If[MemberQ[T[manifold][coords],i],
Superscript[Subscript[MakeTensor[D[T[data],i],T[downrank],T[uprank],T[manifold]], downIndices],upIndices],
newdata = Outer[f,  Table[Function[F,D[F,II]]/.II-> ii,{ii,T[manifold][coords]}],T[data]];
Superscript[Subscript[MakeTensor[newdata,T[downrank]+1,T[uprank],T[manifold]], Join[{i},downIndices]],upIndices]]
]


(*Covariant derivative*)
(*requires that \[CapitalGamma] is defined*)
\!\(
\*SubscriptBox[\(\[Del]\), \(aa_\)]\ \*
TemplateBox[{SubscriptBox[RowBox[{"Tensor", "[", "T_", "]"}], "down_"],"up_"},
"Superscript"]\) ^:= Module[{sumvar,result,i},
result = Subscript[D, aa][Superscript[Subscript[Tensor[T], down],up]];
result += Sum[ Superscript[\!\(\*SubscriptBox[\(\[CapitalGamma]\), \({sumvar, aa}\)]\),{up[[i]]}] Superscript[Subscript[Tensor[T], down],ReplacePart[up,i-> sumvar]],{i,Length[up]}];
result += Sum[ -Superscript[\!\(\*SubscriptBox[\(\[CapitalGamma]\), \({down[\([i]\)], aa}\)]\),{sumvar}] Superscript[Subscript[Tensor[T], ReplacePart[down,i-> sumvar]],up],{i,Length[down]}]
]


(*Alternate method for inputing Covariant Derivatives*)
Subscript[CoD, aa_ ]Superscript[Subscript[Tensor[T_], down_],up_] ^:= \!\(
\*SubscriptBox[\(\[Del]\), \(aa\)]\ \*
TemplateBox[{SubscriptBox[RowBox[{"Tensor", "[", "T", "]"}], "down"],"up"},
"Superscript"]\)


(*Acces tensor data with T[[upList,downList]] where upList and downList are lists of integers of the same length as uprank and downrank*)
(*to do*)
(*make accesible with subscript and superscript numbers:
if this is done make sure that Subscript[R, {a,b,c}]^{b} is distinguishable from Subscript[R, {1,2,1}]^{3}*)
Tensor[T_][[downList_,upList_]]^:=
If[T[downrank]==Length[downList]&& T[uprank]==Length[upList],
Part@@Flatten[{{T[data]},Flatten[{downList,upList}]},1],
Message[RankError::oob,downList,upList]]


(*IMPORTANT*)
(*To use this properly you must use T with a subscript and a superscript NOT a power, please copy the template below to do so for now*)

(*Tensor with indices template, if you run it first it will prettify it*)
Superscript[\!\(\*SubscriptBox[\(T\), \({}\)]\),{}] ;

(*To Do*)
(*set it up to check if the sub or suprscript list is mising so we dont need an empty list for absent indices*)
(* add a check to make sure that indices are repeated only once and are properly up and down*)
Superscript[Subscript[Tensor[T1_], a1_],b1_] Superscript[Subscript[Tensor[T2_], a2_],b2_] ^:=Module[{result,downIndices,upIndices,resTensor},
If[Length[a1]==T1[downrank]&& Length[b1]==T1[uprank]&&Length[a2]==T2[downrank]&& Length[b2]==T2[uprank],
result = Einstein[{T1,a1,b1},{T2,a2,b2}];
resTensor = result[[1]];
Superscript[Subscript[resTensor, result[[2]]],result[[3]]],
Message[indexError::declerationmismatch]
]]
