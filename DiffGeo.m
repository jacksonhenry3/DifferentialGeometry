(* ::Package:: *)

RankError::oob="The length of `1` and `2` must be the same as the up and down rank of the tensor.";
RankError::depth="The sum of `1` and `2` must be the same as the depth of the data matrix,`3` .";
indexError::mismatch="The two tensors must have the same indices to be added together";


(*Ensures compatability with tensor wrap;per*)
Tensor[T1_][downrank]^:=T1[downrank];
Tensor[T1_][uprank]^:=T1[uprank];
Tensor[T1_][data]^:=T1[data];


Superscript[Subscript[Tensor[T1_], down1_],up1_]+Superscript[Subscript[Tensor[T2_], down2_],up2_]^:= Module[{varsums,indices,tensorData},

If[Sort[down1]===Sort[down2] && Sort[up1]===Sort[up2],

indices = Flatten[{down1,up1}];
varsums = Table[{v,1,NDim},{v,indices}];

tensorData = Table[Tensor[T1][[down1,up1]]+Tensor[T2][[down2,up2]],##]&@@ varsums;

Superscript[Subscript[MakeTensor[tensorData,T1[downrank],T2[uprank]], down1],up1],

Message[indexError::mismatch]]

];

a_ Superscript[Subscript[Tensor[T_], down_],up_]^:= Superscript[Subscript[MakeTensor[a Tensor[T][data],T[downrank],T[uprank]], down],up]



(*add compatability with derivatives of arbitrary order*)
f[a_,b_]:= a[b]
Subscript[D, i_][ Superscript[Subscript[Tensor[T_], downIndices_],upIndices_]]^:=Module[{newdata},
If[MemberQ[coordinates,i],
Superscript[Subscript[MakeTensor[D[T[data],i],T[downrank],T[uprank]], downIndices],upIndices],
newdata = Outer[f,  Table[Function[F,D[F,II]]/.II-> ii,{ii,coordinates}],T[data]];
Superscript[Subscript[MakeTensor[newdata,T[downrank]+1,T[uprank]], Join[{i},downIndices]],upIndices]
]
]

(*Acces tensor data with T[[upList,downList]] where upList and downList are lists of integers of the same length as uprank and downrank*)

(*to do*)
(*make accesible with subscript and superscript numbers:
if this is done make sure that Subscript[R, {a,b,c}]^{b} is distinguishable from Subscript[R, {1,2,1}]^{3}*)
Tensor[T_][[downList_,upList_]]^:=
If[T[downrank]==Length[downList]&& T[uprank]==Length[upList],
Part@@Flatten[{{T[data]},Flatten[{downList,upList}]},1],
Message[RankError::oob,downList,upList]]

(*i just made my function compatible with your stringy notation, im sure they can talk more directly, but idk how to modifiy Einstein properly*)

(* I think einstein should also work on a single tensor, I.E. if we want to contract the riemann tensor to the ricci tensor id like to type     Subscript[R, {a,b,c}]^{b}*) 

(*IMPORTANT*)
(*To use this properly you must use T with a subscript and a superscript NOT a power, please copy the template below to do so for now*)

(*Tensor with indices template*)
Superscript[\!\(\*SubscriptBox[\(T\), \({}\)]\),{}] ;

(*Scroll to bottom for examples*)

(*To Do*)
(*set it up to check if the sub or suprscript list is mising so we dont need an empty list for absent indices*)
(*add a check to make sure that a1 b1 a2 b2 have the same length as up and down rank of T2 and T2*)
(* add a check to make sure that indices are repeated only once and are properly up and down*)
Superscript[Subscript[Tensor[T1_], a1_],b1_] Superscript[Subscript[Tensor[T2_], a2_],b2_] ^:=Module[{result,downIndices,upIndices,resTensor},

result = Einstein[{T1,LToS[a1],LToS[b1]},{T2,LToS[a2],LToS[b2]}];


resTensor = result[[1]];
downIndices = ToExpression[StringSplit[result[[2]],""]];
upIndices = ToExpression[StringSplit[result[[3]],""]];
Superscript[Subscript[resTensor, downIndices],upIndices]
]

LToS[l_]:=StringDelete[StringRiffle[l]," "]



MakeTensor[matrix_, DownRank_,UpRank_] := Module[{tmp,function},
tmp = Null;
If[If[Head @ matrix === List, ArrayDepth[matrix],0]==DownRank+UpRank,
		tmp = <|data->matrix, downrank-> DownRank, uprank-> UpRank|>;,
		Message[RankError::depth,DownRank,UpRank,matrix]];
		Tensor[tmp]
]


(* Contract TDownth index with TUpth index*)
Contract[T_,TDown_,TUp_] :=Module[{downlist,uplist,i, result},
downlist = ConstantArray[;;,T[downrank]];
downlist[[TDown]] = i;
uplist = ConstantArray[;;,T[uprank]];
uplist[[TUp]] = i;
result = FullSimplify[Sum[T[[downlist,uplist]],{i,1,NDim}]];
MakeTensor[result,T[downrank]-1,T[uprank]-1]
]


TProduct[T1_,T2_]:=Module[{result,numIndices,dummyvars,dummyvarsReordered},
Quiet[
If[Not[Head @ T2[data]=== List] || Not[Head @ T1[data]=== List],
	result = T1[data] T2[data];,
	
	result = Outer[Times,T1[data],T2[data]];
	numIndices = T1[downrank]+T1[uprank]+T2[downrank]+T2[uprank];
	dummyvars = Table[Symbol["var"<>ToString[i]],{i,numIndices}];
	dummyvarsReordered = Join[Table[dummyvars[[i]],{i,1,T1[downrank]}],Table[dummyvars[[i]],{i,T1[downrank]+T1[uprank]+1,T1[downrank]+T1[uprank]+T2[downrank]}],Table[dummyvars[[i]],{i,T1[downrank]+1,T1[downrank]+T1[uprank]}],Table[dummyvars[[i]],{i,T1[downrank]+T1[uprank]+T2[downrank]+1,T1[downrank]+T1[uprank]+T2[downrank]+T2[uprank]}]];
	result = Table@@Flatten[{{Part@@Flatten[{{result},dummyvars},1]},Table[{v,1,NDim},{v,dummyvarsReordered}]},1];
];
MakeTensor[result,T1[downrank]+T2[downrank],T1[uprank]+T2[uprank]]
	
,Part::pkspec1]]


(* arguments will have form {T,"ijk,"lmn"}. Down indices must ALWAYS come first. *)
Einstein[{T_,argD_,argU_}] := Module[{varU,varD,contract,contractVars, tmp,out},
tmp = T;
varD = ToExpression[StringSplit[argD,""]];
varU = ToExpression[StringSplit[argU,""]];
contractVars = Table[If[MemberQ[varD,elem],Flatten[{Position[varD,elem],Position[varU,elem]}],## &[]],{elem,varU}];
If[Length[contractVars]!=0, tmp = Contract[T,contractVars[[1,1]],contractVars[[1,2]]];
varD = Delete[varD,contractVars[[1,1]]];
varU = Delete[varU,contractVars[[1,2]]];
contractVars = Delete[contractVars,1];];
out = {tmp,StringRiffle[varD,""],StringRiffle[varU,""]};
If[Length[contractVars]!=0, Einstein[out],out]
]
(* define for two arguments *)
Einstein[{T1_,argD1_,argU1_},{T2_,argD2_,argU2_}] := Einstein[{TProduct[T1,T2],argD1<>argD2,argU1<>argU2}]
(* define for three or more arguments *)
Einstein[{T1_,argD1_,argU1_},{T2_,argD2_,argU2_},{T3___,argD3___,argU3___}] := Einstein[Einstein[{T1,argD1,argU1},{T2,argD2,argU2}],{T3,argD3,argU3}]


StripIndices[IndexedTensor_]:=IndexedTensor[[1,1]]
