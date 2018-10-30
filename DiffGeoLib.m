(* ::Package:: *)

(* ::Text:: *)
(*Todo*)
(*1. change all sum and table variables to be more obscure (triple)*)
(*2. Change everything so all down is ALWAYS returned.*)
(*3. add raise and lower functions*)


(* ::Input::Initialization:: *)
(* \[CapitalGamma][c_,a_,b_,met_,coord_] gives Subsuperscript[\[CapitalGamma], ab, c]  for a given metric (nxn matrix) and coordinate system *)
\[CapitalGamma][c_, a_, b_, met_, coord_] := Module[{imet, n}, n = Length[coord]; imet = Inverse[met];
Return[(1/2) Sum[imet[[c, d]] (D[met[[a, d]], coord[[b]]] + D[met[[b, d]], coord[[a]]] - D[met[[a, b]], coord[[d]]]), {d, 1, n}]]]
\[CapitalGamma][met_,coord_]:=Table[\[CapitalGamma][c,a,b,met,coord],{c,1,Length[coord]},{a,1,Length[coord]},{b,1,Length[coord]}]


(* ::Input::Initialization:: *)
(*This function will take a covariant derivative of an arbitrary tensor field
The result is of the form \!\(
\*SubscriptBox[\(\[Del]\), \(var\)]
\*SuperscriptBox[
SubscriptBox[\(T\), \(down\)], \(up\)]\) where down and up are lists of particular index values
met is the metric and coord is a list of your symbolic coordinates.*)
CovariantD[T_,up_,down_,var_,met_,coord_]:=
Module[{n,indexList,S},
n = Length[coord];
indexList = Join[Table[i,{i,up}],Table[j,{j,down}]];
S = D[Extract[T,indexList],coord[[var]]];
S=S+
Sum[
-Sum[
\[CapitalGamma][d,down[[b]],var,met,coord]Extract[T,ReplacePart[indexList , d, Length[up]+b]],
{d,1,n}],
{b,Length[down]}
]+
Sum[
Sum[
\[CapitalGamma][up[[b]],d,var,met,coord]Extract[T,ReplacePart[indexList , d, b]],
{d,1,n}],
{b,Length[up]}
];
If[up=={} && down =={},S = D[T[[1]],coord[[var]]],S]
]
CovariantD[T_,up_,down_,met_,coord_]:=Table[CovariantD[T,up,down,var,met,coord],{var,1,Length[coord]}]


(* ::Input::Initialization:: *)
(* R[\[Mu]_,\[Nu]_,\[Rho]_,\[Sigma]_,met_,coord_] gives Subsuperscript[R, abc,    d] for the given metric *)
R[\[Mu]_,\[Nu]_,\[Rho]_,\[Sigma]_,met_,coord_]:=D[\[CapitalGamma][\[Sigma],\[Mu],\[Rho],met,coord],coord[[\[Nu]]]]-D[\[CapitalGamma][\[Sigma],\[Nu],\[Rho],met,coord],coord[[\[Mu]]]]+Sum[\[CapitalGamma][\[Alpha],\[Mu],\[Rho],met,coord] \[CapitalGamma][\[Sigma],\[Alpha],\[Nu],met,coord]-\[CapitalGamma][\[Alpha],\[Nu],\[Rho],met,coord] \[CapitalGamma][\[Sigma],\[Alpha],\[Mu],met,coord],{\[Alpha],1,Length[coord]}]
RiemannTensor[met_,coord_]:=Table[R[\[Mu],\[Nu],\[Rho],\[Sigma],met,coord],{\[Mu],1,Length[coord]},{\[Nu],1,Length[coord]},{\[Rho],1,Length[coord]},{\[Sigma],1,Length[coord]}]


(* ::Input::Initialization:: *)
(* R[\[Mu]_,\[Nu]_,met_,coord_] gives the Ricci Subsuperscript[tensorR, ab,   ] for the given metric *)
R[\[Mu]_,\[Rho]_,met_,coord_]:=Sum[R[\[Mu],\[Nu],\[Rho],\[Nu],met,coord],{\[Nu],1,Length[coord]}]
RicciTensor[met_,coord_]:=Table[R[\[Mu],\[Rho],met,coord],{\[Mu],1,Length[coord]},{\[Rho],1,Length[coord]}]


(* ::Input::Initialization:: *)
(* R[met_,coord_] gives the Ricci Scalar R*)
R[met_,coord_]:=Module[{imet,n},n=Length[coord];imet=Inverse[met];
Return[Sum[imet[[aa,bb]] R[aa,bb,met,coord],{aa,1,n},{bb,1,n}]]]


(*This calculates the extrinsic curvature assuming that the surface is defined as being a surface of constant first dimension. In this case, constant r.*)
k[a_,b_,n_,met_,coord_] := If[a ==1 || b ==1,0,CovariantD[n,{},{b},a,met,coord]]


(*converts down index object coordinate system*)
ConvertVector[OldVector_,OldCoords_,NewCoords_]:=Table[Sum[D[OldCoords[[i]],a]OldVector[[i]],{i,Length[OldCoords]}],{a,NewCoords}];
ConvertVector1[OldVector_,OldCoords_,NewCoords_]:=Table[Sum[D[OldCoords[[i]],a]OldVector[[i]],{i,Length[OldCoords]}],{a,NewCoords}];
ConvertVector2[OldVector_,OldCoords_,NewCoords_]:=Table[Sum[D[NewCoords[[i]],a]OldVector[[i]],{i,Length[NewCoords]}],{a,OldCoords}];
GenerateJacobian[OldCoords_,NewCoords_]:=Table[D[OldCoords[[i]],a],{i,Length[OldCoords]},{a,NewCoords}];
GenerateJacobian[OldCoords_,NewCoords_]:=Table[D[NewCoords[[i]],a],{i,Length[NewCoords]},{a,OldCoords}];
Convert2Tensor[OldMetric_,OldCoords_,NewCoords_]:=Table[Sum[D[OldCoords[[i]],a]D[OldCoords[[j]],b]OldMetric[[i,j]],{i,Length[OldCoords]},{j,Length[OldCoords]}],{a,NewCoords},{b,NewCoords}];
