BeginPackage["MatrixD`"]

MatrixD::usage = "MatrixD[f, m] gives the matrix derivative of f with respect to the matrix m";
MatrixReduce::usage = "MatrixReduce[expr] attempts to return a canonical form for the given symbolic matrix expression";

$SingleEntryMatrix::usage = "$SingleEntryMatrix is the matrix derivative of X with respect to itself"
$IdentityMatrix
$MatrixDimension

MatrixD::unsup = "`1` is not supported outside of Tr";
MatrixD::scalar = "Matrix derivative of scalar function `1` encountered";

Get["MatrixD`Utilities`"]
Get["MatrixD`TestFunctions`"]

Begin["`Private`"]

$IdentityMatrix /: MakeBoxes[$IdentityMatrix, fmt_] := InterpretationBox[StyleBox["\[DoubleStruckCapitalI]", Bold, Larger], $IdentityMatrix]
$SingleEntryMatrix /: MakeBoxes[$SingleEntryMatrix, fmt_] := InterpretationBox[StyleBox["\[DoubleStruckCapitalJ]", Bold, Larger], $SingleEntryMatrix]
$MatrixDimension = \[FormalD]

$MatrixFunctions = {Tr, Transpose, Det, Inverse, MatrixPower, MatrixFunction, MatrixExp, MatrixLog}

Options[MatrixD] = {Assumptions:>Automatic, "Invertible"->True, "MatrixDimensions"->{$MatrixDimension, $MatrixDimension}};

MatrixD[f_, matrix_, OptionsPattern[]] := WithExcludedFunctions[
	Catch[
		Block[
			{
			$Assumptions = toAssumptions[f, Assumptions->OptionValue[Assumptions]],
			$MatrixDimension = Replace[OptionValue["MatrixDimensions"], {{d_, d_} -> d, Except[_Integer] -> \[FormalD]}],
			$Invertible = TrueQ@OptionValue["Invertible"]
			},

			MatrixReduce[
				D[f, MatrixD, NonConstants->{matrix}],
				"Invertible"->OptionValue["Invertible"],
				Assumptions->True
			]
		],
		"Unsupported"
	],
	$MatrixFunctions
]

MatrixD /: D[X_, MatrixD, NonConstants->{X_}] := $SingleEntryMatrix

MatrixD /: D[Transpose[f_], MatrixD, NonConstants->{X_}] := Transpose[D[f, MatrixD, NonConstants->{X}]]
MatrixD /: D[Inverse[f_], MatrixD, NonConstants->{X_}] := -Inverse[f].D[f, MatrixD, NonConstants->{X}].Inverse[f]

(* MatrixPower and MatrixFunction have simple derivatives at the top level inside a Tr *)
(* TODO: X.MatrixFunction[Log,X] can be rewritten MatrixFunction[# Log[#]&, X]. This rewrite
 * should be performed automatically so that MatrixFunction is at top level.
 *
 * TODO: Need a predicate indicating a function is "univariate". That's when you can differentiate 
 * MatrixFunction. Tr[MatrixExp[A. MatrixExp[X]] is not differentiable
 *)

MatrixD /: D[Tr[a_], MatrixD, NonConstants->{X_}] := With[{reduce = TrReduce[Tr[a]]},
	Replace[reduce,
		{
		Tr[arg_] :> Block[{trQ=True}, Tr[D[arg, MatrixD, NonConstants->{X}]] /. Tr[0] -> 0],
		arg_ :> D[arg, MatrixD, NonConstants->{X}]
		}
	]
]

MatrixD /: D[Det[a_Dot], MatrixD, NonConstants->{X_}] /; $Invertible := Det[a] (D[Tr[MatrixLog[#]], MatrixD, NonConstants->{X}]& /@ Plus@@a)

MatrixD /: D[Det[Transpose[f_]], MatrixD, NonConstants->{X_}] := D[Det[f], MatrixD, NonConstants->{X}]
MatrixD /: D[Det[Inverse[f_]], MatrixD, NonConstants->{X_}] := -Det[Inverse[f]] D[Det[f], MatrixD, NonConstants->{X}]/Det[f]
MatrixD /: D[Det[MatrixPower[f_, n_]], MatrixD, NonConstants->{X_}] := n Det[MatrixPower[f, n]] D[Det[f], MatrixD, NonConstants->{X}]/Det[f]
MatrixD /: D[Det[f_], MatrixD, NonConstants->{X_}] := Det[f] D[Tr[MatrixLog[f]], MatrixD, NonConstants->{X}]

(* TODO: Times in a Det/Tr should be simplified *)

(* If inside of a Tr, then we can use simple derivatives of Matrix* functions. Otherwise fail *)
MatrixD /: D[HoldPattern@MatrixFunction[f_, U_], MatrixD, NonConstants->{X_}] := If[TrueQ@trQ,
	Plus[
	 	Replace[D[U, MatrixD, NonConstants->{X}], d:Except[0] -> d . SimplifyMatrixFunction[f', U]],
	 	MixedFunction[D[f[#], MatrixD, NonConstants->{X}], U]
	],

	Message[MatrixD::unsup,MatrixFunction];
	Throw[$Failed,"Unsupported"] 
]

MatrixD /: D[MatrixLog[f_Dot], MatrixD, NonConstants->{X_}] /; trQ && $Invertible := 
	D[MatrixLog[#], MatrixD, NonConstants->{X}]& /@ Plus @@ f

MatrixD /: D[MatrixLog[f_], MatrixD, NonConstants->{X_}] := If[TrueQ@trQ,
	Replace[D[f, MatrixD, NonConstants->{X}], d:Except[0] -> d . Inverse[f]],

	Message[MatrixD::unsup,MatrixLog];
	Throw[$Failed, "Unsupported"]
]

MatrixD /: D[MatrixExp[f_], MatrixD, NonConstants->{X_}] := If[TrueQ@trQ,
	Replace[D[f, MatrixD, NonConstants->{X}], d:Except[0] -> d . MatrixExp[f]],

	Message[MatrixD::unsup,MatrixExp];
	Throw[$Failed, "Unsupported"]
]

(* If trQ is True, then use simple derivative. Otherwise, use more complicated summation form of derivative *)
MatrixD /: D[MatrixPower[f_,n_], MatrixD, NonConstants-> {X_}] := Which[
	TrueQ@trQ,
	n D[f, MatrixD, NonConstants->{X}] . MatrixPower[f,n-1],

	MatchQ[n,_Integer?Positive],
	D[Dot @@ ConstantArray[f,n], MatrixD, NonConstants->{X}],

	MatchQ[n,_Integer?Negative],
	D[Dot @@ ConstantArray[Inverse[f], -n], MatrixD, NonConstants->{X}],

	!TrueQ[Refine[Element[n, Integers]]],
	Message[MatrixD::unsup, MatrixPower[f, n]];
	Throw[$Failed, "Unsupported"],

	TrueQ@Refine[n < 0],
	-Sum[
		Dot[
			MatrixPower[Inverse@f, \[FormalK]+1],
			D[f, MatrixD, NonConstants->{X}],
			MatrixPower[Inverse@f,-n-\[FormalK]]
		],
		{\[FormalK],0,-n-1}
	],
	
	True,
	Sum[
		Dot[
			MatrixPower[f,\[FormalK]],
			D[f, MatrixD, NonConstants->{X}],
			MatrixPower[f,n-\[FormalK]-1]
		],
		{\[FormalK],0,n-1}
	]
]

(* implement MatrixD rules for Dot, Times and Plus. This way the automatic differentiation rules for
 * D can be avoided, allowing the matrix version of D to operate when chaining. I need to be able to check
 * these intermediate derivatives for unsupported differentiation of scalar functions.*)
 
MatrixD /: D[a_Dot|a_Times, MatrixD, NonConstants->{X_}] := Block[{trQ=False},
	Sum[MapAt[D[#, MatrixD, NonConstants->{X}]&, a, i], {i,Length[a]}]
]

MatrixD /: D[a_Plus, MatrixD, NonConstants->{X_}] :=
	D[#, MatrixD, NonConstants->{X}]& /@ a

(* At this point, all matrix functions (e.g., Inverse, Det, etc) should have been taken care of. If there
 * are any matrix variables (i.e., X variables outside of Det/Tr) still present in the expression, then MatrixD gives up *)		
MatrixD /: D[a_, MatrixD, NonConstants->{X_}] := Throw[
	Message[MatrixD::scalar, a];
	$Failed,

	"Unsupported"
] /; !FreeQ[a /. _Det|_Tr -> n, X]

Options[MatrixReduce] = {Assumptions:>Automatic, "Invertible"->True};

MatrixReduce[f_, OptionsPattern[]] := Internal`InheritedBlock[
	{Dot, Inverse, Tr, Transpose, $Assumptions=toAssumptions[f, Assumptions->OptionValue[Assumptions], Method->None]},

	Unprotect[Dot, Inverse, Tr, Transpose];

	(* If "Invertible" expand out Inverse to enable cancellation *)
	If[TrueQ@OptionValue["Invertible"],
		Inverse @ a_Dot := Inverse /@ Reverse[Dot[a]];
	];

	(* support linearity so that Tr/Dot don't contain Plus/Times at top level *)	
	Tr[a_Plus] := Distribute[Unevaluated[Tr[a]]];
	Tr[Sum[a_, i__]] := Sum[Tr[a], i];
	Tr[a_?ScalarQ b_] := a Tr[b];

	Dot[a___, Sum[b_, i__], c___] := Sum[Dot[a,b,c], i];
	a_Dot /; MemberQ[Unevaluated[a], _Plus] := Distribute[Unevaluated @ a];

	(* special cases *)	
	Tr[$SingleEntryMatrix] := $IdentityMatrix;
	Transpose[0] = 0;
	Dot[___, 0, ___] = 0;

	(* reduction of SingleEntryMatrix *)
	Tr[Dot[a___, $SingleEntryMatrix, b___]] := ExpandedTranspose @ Dot[b, a];
	Tr[Dot[a___, Transpose[$SingleEntryMatrix], b___]] := Dot[b, a];

	(* reduction of MatrixFunction with matrix dependent pure functions *)
	Tr[MixedFunction[foo_, U_]] := distributeScalarList[foo, U];

	f /. 
		{
		Verbatim[MatrixFunction][Power[E, #]& | Exp, x_] :> MatrixExp[x], 
		Verbatim[MatrixFunction][Log[#]& | Log, x_] :> MatrixLog[x],
		Verbatim[MatrixFunction][Power[#, -1]&, x_] :> Inverse[x]
		} //. 
		{g_Function->g, h:(Dot|Transpose)->Composition[TensorReduce, TensorExpand, h]} //.
		{
			MatrixPower[x_,-1]->Inverse[x],
			MatrixPower[x_, 1]->x,
			(TensorTranspose|Transpose)[x_, {2,1}]->Transpose[x]
		}
]

(* collect on tensors instead *)
distributeScalarList[e_, a_] := Module[{tensors},
	tensors = DeleteDuplicates @ Flatten[
		Replace[FactorTimesList[#],
			{
			{_, t_Times} :> List @@ t,
			{_, t_} :> t
			}
		]& /@ Replace[Expand[e], {r_Plus :> List@@r, r_ :> {r}}]
	];
	Collect[
		e,
		tensors, 
		Function[x, 
			Replace[
				FactorTimesList[x, "Predicate" -> Function[y, FreeQ[y, #]]],
				{s_, t_} :> s MatrixFunction[t&, a]
			]
		]
	]
]

Options[toAssumptions] = {Assumptions->True, Method->"Usage"}

toAssumptions[f_, OptionsPattern[]] := If[OptionValue[Method] === "Usage",
	With[
		{symbols = UsageBasedSymbols[f]},
		{
		m = Replace[
			"Matrices" /. symbols,
			{
			{x__} :> Element[Alternatives[x, $SingleEntryMatrix], Matrices[{$MatrixDimension, $MatrixDimension}]],
			_ :> Element[$SingleEntryMatrix, Matrices[{$MatrixDimension, $MatrixDimension}]]
			}
		],
		a = Replace["Scalars" /. symbols /. "Scalars" -> {}, x_ :> Element[Alternatives @@ Join[x, {_Det, _Tr}], Complexes]]
		},
		m && a && OptionValue[Assumptions] && $Assumptions
	],
	OptionValue[Assumptions] && $Assumptions
]

End[]

EndPackage[]