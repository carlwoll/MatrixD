BeginPackage["MatrixD`TestFunctions`", { "MatrixD`", "MatrixD`Utilities`"}]

TestMatrixD::usage = "TestMatrixD[expr, X] evaluates the derivative using MatrixD and explicit random matrices"
MatrixEquivalence::usage = "MatrixEquivalence[expr1, expr2] evaluates the matrix function expr1 and expr2 using explicit random matrices"

Begin["`Private`"] (* Begin Private Context *) 

Options[TestMatrixD] = {Constants -> Automatic, "RandomSeed"->1};
	
TestMatrixD[a_, X_, OptionsPattern[]] := Module[{constants, constantRules},
	SeedRandom[OptionValue["RandomSeed"]];
	constants = Replace[OptionValue[Constants],
		Except[_List] :> "Matrices" /. UsageBasedSymbols[a]
	];
	constants = # -> Array[Unique[], {2,2}]& /@ constants;

	constantRules = MapThread[Rule, {#, RandomReal[1, Length[#]]}]&[
		Flatten[constants[[All,2]]]
	];

	WithExcludedFunctions[
		Column@{
			D[a /. IJRules /. constants, {X /. constants}] /. constantRules,
			Hold[Evaluate@MatrixD[a,X]] /. IJRules /. constants /. constantRules
		},
		$MatrixFunctions
	] //ReleaseHold
]

IJRules = {
	$IdentityMatrix -> IdentityMatrix[2],
	$SingleEntryMatrix -> Transpose[
		TensorProduct[IdentityMatrix[2], IdentityMatrix[2]],
		{1, 3, 2, 4}
	]
};

Options[MatrixEquivalence] = {Constants -> Automatic, "RandomSeed"->1};

MatrixEquivalence[m1_, m2_, OptionsPattern[]] := Module[{constants, constantRules},
	SeedRandom[OptionValue["RandomSeed"]];
	constants = Replace[OptionValue[Constants],
		Except[_List] :> "Matrices" /. UsageBasedSymbols[{m1,m2}]
	];
	constants = # -> Array[Unique[], {2,2}]& /@ constants;

	constantRules = MapThread[Rule, {#, RandomReal[1, Length[#]]}]&[
		Flatten[constants[[All,2]]]
	];

	{m1, m2} /. constants /. constantRules
]

End[] (* End Private Context *)

EndPackage[]