(* ::Package:: *)

RankError::oob="The length of `1` and `2` must be the same as the up and down rank of the tensor.";
RankError::depth="The sum of `1` and `2` must be the same as the depth of the data matrix,`3` .";


(*Ensures compatability with tensor wrapper*)
Tensor[T1_][downrank]^:=T1[downrank]
Tensor[T1_][uprank]^:=T1[uprank]
Tensor[T1_][data]^:=T1[data]

(*add a check to validate that T1 and T2 have the same uprank and downrank*)
Tensor[T1_]+Tensor[T2_]^:= MakeTensor[T1[data]+T2[data],T1[downrank],T2[uprank]]

Quiet[Tensor[T1_]-Tensor[T2_]^:= MakeTensor[T1[data]-T2[data],T1[downrank],T2[uprank]]]

(*add compatability with derivatives of arbitrary order*)
(*make it so derivatives can increase tensor order I.E. Subscript[\[ScriptCapitalD], i] instead of Subscript[\[ScriptCapitalD], x] specifically*)
D[Tensor[T_],x_]^:=MakeTensor[D[T[data],x],T[downrank],T[uprank]]

(*Acces tensor data with T[[upList,downList]] where upList and downList are lists of integers of the same length as uprank and downrank*)

(*to do*)
(*make accesible with subscript and superscript numbers:
if this is done make sure that Subscript[R, {a,b,c}]^{b} is distinguishable from Subscript[R, {1,2,1}]^{3}*)
Tensor[T_][[downList_,upList_]]^:=
If[T[downrank]==Length[downList]&& T[uprank]==Length[upList],
Part@@Flatten[{{T[data]},Flatten[{downList,upList}]},1],
Message[RankError::oob,downList,upList]]

(*i just made my function compatible with your stringy notation, im sure they can talk more directly, but idk how to modifiy Einstein properly*)

(*I believe eisntien returns a list where the first object is a tensor and the last two are the names of the up and down indices of the result, I think it would make more sense for it to just return the tensor, additionally, this may be breaking the product when more than two tensors are involved*)
(*my work is breaking product becouse its not returning tensor WITH INDICES, at the end of the calcuation we want a tensor without indices, so idk how to deal with that, maybe a function strips tensor indices?*)
(*Finally, I think einstein should also work on a single tensor, I.E. if we want to contract the riemann tensor to the ricci tensor id like to type     Subscript[R, {a,b,c}]^{b}*) 

(*IMPORTANT*)
(*To use this properly you must use T with a subscript and a superscript NOT a power, please copy the template below to do so for now*)

(*Tensor with indices template*)
Superscript[\!\(\*SubscriptBox[\(T\), \({}\)]\),{}] ;

(*Scroll to bottom for examples*)

(*To Do*)
(*set it up to check if the sub or suprscript list is mising so we dont need an empty list for absent indices*)
(*add a check to make sure that a1 b1 a2 b2 have the same length as up and down rank of T2 and T2*)
(* add a check to make sure that indices are repeated only once and are properly up and down*)
Superscript[Subscript[Tensor[T1_], a1_],b1_] Superscript[Subscript[Tensor[T2_], a2_],b2_] ^:=Einstein[{T1,LToS[a1],LToS[b1]},{T2,LToS[a2],LToS[b2]}][[1]]

LToS[l_]:=StringDelete[StringRiffle[l]," "]



MakeTensor[matrix_, DownRank_,UpRank_] := Module[{tmp,function},

tmp = Null;
(*If[Head @ matrix\[Equal]List,
	If[ArrayDepth[matrix]==DownRank+UpRank,
		tmp = <|data->matrix, downrank-> DownRank, uprank-> UpRank|>;
		Tensor[tmp],
		Message[RankError::depth,DownRank,UpRank,matrix]];,
	tmp = <|data->matrix, downrank-> DownRank, uprank-> UpRank|>;
	Tensor[tmp]]
	Tensor[tmp]*)
	
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
	result = Table@@Flatten[{{Part@@Flatten[{{result},dummyvarsReordered},1]},Table[{v,1,NDim},{v,dummyvars}]},1];
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
