(* Wolfram Language Package *)

BeginPackage["MatrixD`Utilities`", {"MatrixD`"}]

WithExcludedFunctions::usage = "WithExcludedFunctions[expr, funs] prevents D from firing on funs"
SimplifyPureFunction::usage = "SimplifyPureFunction[Function[.]] applies Simplify to the pure function argument"

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

End[] (* End Private Context *)

EndPackage[]
