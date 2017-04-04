(* Wolfram Language Package *)

BeginPackage["MatrixD`Utilities`", {"MatrixD`"}]

WithExcludedFunctions::usage = "WithExcludedFunctions[expr, funs] prevents D from firing on funs"
SimplifyPureFunction::usage = "SimplifyPureFunction[Function[.]] applies Simplify to the pure function argument"
ExpandedTranspose::usage = "ExpandedTranspose[expr] transposes expr and expands out all Transpose objects"
TrReduce::usage = "TrReduce[Tr[expr]] expand sums and products by scalars, and converts the arguments of the resulting Tr objects to a single MatrixFunction if possible"
ScalarQ::usage = "ScalarQ[expr] returns True if exp is not an Array object"
FactorTimesList::usage = "FactorTimesList[Times[.]] produces a list of a product of scalars and nonscalars"
UsageBasedSymbols::usage = "UsageBasedSymbols[expr] determines what kinds of tensors a symbol must be"
SimplifyMatrixFunction::usage = "SimpifyMatrixFunction[func, arg] returns a simplified MatrixFunction[func, arg]"

Begin["`Private`"] 

(* helper function that tempoararily excludes matrix functions from normal differentatiation rules *)
SetAttributes[WithExcludedFunctions, HoldFirst];
WithExcludedFunctions[body_, funs_] := Module[{old},
	Internal`WithLocalSettings[
		(* allow D to pass through matrix functions *)
		old = "ExcludedFunctions" /.
			("DifferentiationOptions"/. SystemOptions["DifferentiationOptions"]);
		SetSystemOptions["DifferentiationOptions" -> "ExcludedFunctions"->
			Union @ Join[
				old,
				funs
			]
		],

		body,

		SetSystemOptions["DifferentiationOptions"->"ExcludedFunctions"->old]
	]
]

SimplifyPureFunction[Function[expr_]] := Function[Evaluate@Simplify[expr, #>0]]
SimplifyPureFunction[e_] := e

Options[FactorTimesList] = {"Predicate" -> ScalarQ}

FactorTimesList[a_Times, OptionsPattern[]] := With[{bool = OptionValue["Predicate"] /@ List @@ a},
	{Pick[a, bool], Pick[a, bool, False]}
]
FactorTimesList[a_, OptionsPattern[]] := If[OptionValue["Predicate"][a], {a, 1}, {1, a}]

(* expand sums/products and eliminate Transpose at top level *)
TrReduce[Tr[Transpose[a_]]] := TrReduce @ Tr[a]
TrReduce[Tr[a_Plus]] := TrReduce @* Tr /@ a
TrReduce[Tr[a_Times]] := Replace[
	FactorTimesList[a, "Predicate"->ScalarQ],
	{
	{s_, 1} -> s Tr[$IdentityMatrix],
	{s_, t_Times} -> s Tr[t],
	{s_, t_} :> s TrReduce[Tr[t]]
	}
]
TrReduce[Tr[a_?ScalarQ]] := a Tr[$IdentityMatrix]
TrReduce[Tr[a_Symbol]] := Tr[a]

(* canonicalize matrix functions *)
TrReduce[Tr[a:(_Inverse|_MatrixFunction|_MatrixLog|_MatrixExp|_MatrixPower)]] := Replace[
	fromMatrixFunction @ MFReduce[a],
	{
		t_Times :> TrReduce[Tr[t]],
		t_ :> Tr[t]
	}
]

(* main function *)
TrReduce[Tr[a_Dot]] := Replace[
	fromMatrixFunction @ MFJoin @ MFGrow @ MFAlign @ MFTranspose @ Map[MFReduce] @ a,
	{
		t_Times :> TrReduce[Tr[t]],
		t_ :> Tr[t]
	}
]

(* MFTranpose expands out all Transpose objects *)
MFTranspose[a_] := a /. Transpose -> ExpandedTranspose

ExpandedTranspose[a_Dot] := ExpandedTranspose /@ Reverse @ a
ExpandedTranspose[Transpose[a_]] := a
ExpandedTranspose[Verbatim[MatrixFunction][f_, a_]] := MatrixFunction[f, ExpandedTranspose[a]]
ExpandedTranspose[(h:MatrixLog|MatrixExp|Inverse)[a_]] := h[ExpandedTranspose[a]]
ExpandedTranspose[MatrixPower[a_, k_]] := MatrixPower[ExpandedTranspose[a], k]
ExpandedTranspose[a_] := Transpose[a]

(* MFAlign cycles the Dot product so that a MatrixFunction comes first (an allowed operation inside of Tr) *)
MFAlign[a_Dot] := Replace[Position[a, _MatrixFunction, 1, 1],
	{
	{{k_Integer}} :> RotateLeft[a, k-1],
	_ -> a
	}
]

(* MFGrow subsumes neighboring objects *)
MFGrow[a_Dot] := a //. Verbatim[MatrixFunction][f_, b_].b_ :> MatrixFunction[SimplifyPureFunction[# f[#] &], b]

(* MFJoin converts dot products of MatrixFunction objects into a single MatrixFunction if possible *)
MFJoin[a_Dot] := a //. Verbatim[MatrixFunction][f_, b_].Verbatim[MatrixFunction][g_, b_] :> MatrixFunction[SimplifyPureFunction[f[#] g[#] &], b]
MFJoin[a_] := a

(* MFReduce converts matrix functions to a MatrixFunction object, and then unnests nested MatrixFunction objects if possible *)
MFReduce[a_] := contractMatrixFunction @ toMatrixFunction @ a

(* convert to MatrixFunction *)
toMatrixFunction[a_] := a /. m:(Inverse | MatrixExp | MatrixLog | MatrixPower) :> toMF @* m

toMF[Inverse[a_]] := MatrixFunction[1/#&,a]
toMF[MatrixExp[a_]] := MatrixFunction[Exp, a]
toMF[MatrixLog[a_]] := MatrixFunction[Log, a]
toMF[MatrixPower[a_, k_]] := MatrixFunction[Power[#, k]&, a]

(* unnest MatrixFunctions *)
contractMatrixFunction[a_] := a /. MatrixFunction -> contractMF

contractMF[f_, Verbatim[MatrixFunction][g_, r_]] := MatrixFunction[SimplifyPureFunction[f[g[#]]&], r]
contractMF[f_, a_Times] := Replace[FactorTimesList[a],
	{s_, t_} :> Switch[t,
		1, Message[MatrixFunction::matsq, s, 2]; Throw[$Failed, "Unsupported"], 
		_Times, Message[MatrixFunction::ttimes, t]; Throw[$Failed, "Unsupported"],
		_, contractMF[SimplifyPureFunction[f[s #]&], t]
	]
] 
contractMF[a__] := MatrixFunction[a]

(* convert from MatrixFunction *)
fromMatrixFunction[a_] := a /. MatrixFunction -> SimplifyMatrixFunction

SimplifyMatrixFunction[#&, a_] := a
SimplifyMatrixFunction[Power[#, -1]&, a_] := Inverse[a]
SimplifyMatrixFunction[Times[1, Power[#, -1]]&, a_] := Inverse[a]
SimplifyMatrixFunction[Power[#, k_]&, a_] := If[k===1, a, MatrixPower[a, k]]
SimplifyMatrixFunction[Power[E, #]& | Exp, a_] := MatrixExp[a]
SimplifyMatrixFunction[Log[#]& | Log, a_] := MatrixLog[a]
SimplifyMatrixFunction[Function[z_], a_] := Which[
	FreeQ[z, #], 
	z
	,
	MatchQ[z, _Times],
	Replace[
		FactorTimesList[z, "Predicate" -> Function[y, FreeQ[y, #]]],
		{
		{1, h_} :> MatrixFunction[h&, a],
		{s_, h_} :> s SimplifyMatrixFunction[h&, a]
		}
	]
	,
	True,
	MatrixFunction[Function[z], a]
]
SimplifyMatrixFunction[a__] := MatrixFunction[a]

(* ScalarQ *)
ScalarQ[a_MatrixFunction] = False
ScalarQ[a_MatrixLog] = False
ScalarQ[a_MatrixExp] = False
ScalarQ[a_MatrixPower] = False
ScalarQ[a_Dot] = False
ScalarQ[a_Transpose] = False
ScalarQ[a_Inverse] = False
ScalarQ[a_Plus] := AllTrue[a, ScalarQ]
ScalarQ[a_Times] := AllTrue[a, ScalarQ]
ScalarQ[a_Symbol] := TensorRank[a] === 0
ScalarQ[a_] = True

(* determine nature of symbols based on usage *)
UsageBasedSymbols[f_] := Last@Reap[
	Cases[f,
		Verbatim[MatrixFunction][_, r_] | MatrixPower[r_, _] | (Inverse|MatrixExp|MatrixLog|Transpose|Tr|Det)[r_] :> iGet[r],
		{0, Infinity}
	],
	_,
	Rule[#1, DeleteDuplicates[#2]] &
]

iGet[s_Symbol] := Sow[s, "Matrices"]
iGet[a_Plus] := iGet /@ a
iGet[a_Dot] := iGet /@ a
iGet[Inverse[a_]] := iGet[a]
iGet[HoldPattern@MatrixFunction[_, a_]] := iGet[a]
iGet[MatrixPower[a_, k_]] := {iGet[a], iScalar[k]}
iGet[Transpose[a_]] := iGet[a]
iGet[Tr[a_]] := iGet[a]
iGet[Det[a_]] := iGet[a]

iScalar[a_] := Sow[a, "Scalars"]



End[] (* End Private Context *)

EndPackage[]
