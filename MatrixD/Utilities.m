(* Wolfram Language Package *)

BeginPackage["MatrixD`Utilities`", {"MatrixD`"}]

WithExcludedFunctions::usage = "WithExcludedFunctions[expr, funs] prevents D from firing on funs"
SimplifyPureFunction::usage = "SimplifyPureFunction[Function[.]] applies Simplify to the pure function argument"
TrReduce::usage = "TrReduce[Tr[expr]] expand sums and products by scalars, and converts the arguments of the resulting Tr objects to a single MatrixFunction if possible"
ScalarQ::usage = "ScalarQ[expr] returns True if exp is not an Array object"

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

(* expand sums/products and eliminate Transpose at top level *)
TrReduce[Tr[a_Transpose]] := TrReduce @ Tr[a]
TrReduce[Tr[a_Plus]] := TrReduce @* Tr /@ a
TrReduce[Tr[a_Times]] := With[{bool = ScalarQ /@ List @@ a},
	Pick[a, bool] Replace[Pick[a, bool, False],
		{
		1 -> Tr[$IdentityMatrix],
		b_Times -> Tr[b],
		b_ :> TrReduce[b]
		}
	]
]
TrReduce[Tr[a_?ScalarQ]] := a Tr[$IdentityMatrix]
TrReduce[Tr[a_Symbol]] := Tr[a]

(* canonicalize matrix functions *)
TrReduce[Tr[a:(_Inverse|_MatrixFunction|_MatrixLog|_MatrixExp|_MatrixPower)]] := Tr[fromMatrixFunction @ MFReduce[a]]

(* main function *)
TrReduce[Tr[a_Dot]] := Tr @ fromMatrixFunction @ MFJoin @ MFGrow @ MFAlign @ MFTranspose @ Map[MFReduce] @ a

(* MFTranpose expands out all Transpose objects *)
MFTranspose[a_] := a /. Transpose -> expandTranspose

expandTranspose[a_Dot] := expandTranspose /@ Reverse @ a
expandTranspose[Transpose[a_]] := a
expandTranspose[Verbatim[MatrixFunction][f_, a_]] := MatrixFunction[f, expandTranspose[a]]
expandTranspose[a_] := Transpose[a]

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
contractMF[a__] := MatrixFunction[a]

(* convert from MatrixFunction *)
fromMatrixFunction[a_] := a /. MatrixFunction -> fromMF

fromMF[#&, a_] := a
fromMF[Power[#, -1]&, a_] := Inverse[a]
fromMF[Times[1, Power[#, -1]]&, a_] := Inverse[a]
fromMF[Power[#, k_]&, a_] := MatrixPower[a, k]
fromMF[Power[E, #]& | Exp, a_] := MatrixExp[a]
fromMF[Log[#]& | Log, a_] := MatrixLog[a]
fromMF[a__] := MatrixFunction[a]

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

End[] (* End Private Context *)

EndPackage[]
