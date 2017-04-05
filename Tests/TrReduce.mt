(* Wolfram Language Test file *)

Test[
	TrReduce[Tr[A.MatrixFunction[Sin, X]]]
	,
	Tr[MatrixFunction[Sin, X]. A]
	,
	TestID -> "TrReduce-1"
]

Test[
	TrReduce[Tr[A.MatrixLog[Transpose[Transpose[A].X]].Transpose[X]]]
	,
	Tr[MatrixFunction[Log[#] #&, Transpose[X].A]]
	,
	TestID -> "TrReduce-2"
]

Test[
	TrReduce[Tr[A.Transpose[MatrixLog[Transpose[A].X]].Transpose[X]]]
	,
	Tr[MatrixFunction[Log[#] #&, Transpose[X].A]]
	,
	TestID -> "TrReduce-3"
]

Test[
	TrReduce[Tr[A.MatrixLog[Transpose[X].A].Transpose[X].A.MatrixExp[Transpose[X].A].Transpose[X]]]
	,
	Tr[MatrixFunction[E^# Log[#] #^2&, Transpose[X].A]]
	,
	TestID -> "TrReduce-4"
]

Test[
	TrReduce[Tr[A.MatrixLog[MatrixFunction[Sin, X.A]].X]]
	,
	Tr[MatrixFunction[Log[Sin[#]] #&, X.A]]
	,
	TestID -> "TrReduce-5"
]

Test[
	TrReduce[Tr[2 X.X]]
	,
	2 Tr[X.X]
	,
	TestID -> "TrReduce-6"
]

(* MatrixFunction normalization *)

Test[
	Catch[TrReduce[Tr[MatrixFunction[Sin, 23 Det[X]]]], "Unsupported"]
	,
	$Failed
	,
	{MatrixFunction::matsq}
	,
	TestID -> "TrReduce-Normalization-1"
]

Test[
	Catch[TrReduce[Tr[MatrixFunction[Sin, A X]]], "Unsupported"]
	,
	$Failed
	,
	{MatrixFunction::ttimes}
	,
	TestID -> "TrReduce-Normalization-2"
]

Test[
	TrReduce[Tr[MatrixFunction[Sin, X Det[X]]]]
	,
	Tr[MatrixFunction[Sin[Det[X] #1] &, X]]
	,
	TestID -> "TrReduce-Normalization-3"
]

(* ScalarQ *)

Test[
	ScalarQ[A]
	,
	False
	,
	TestID -> "TrReduce-ScalarQ-1"
]

Test[
	ScalarQ[Tr[X]]
	,
	True
	,
	TestID -> "TrReduce-ScalarQ-2"
]

Test[
	ScalarQ[MatrixFunction[Sin, X]]
	,
	False
	,
	TestID -> "TrReduce-ScalarQ-3"
]

Test[
	Assuming[Element[k, Complexes], ScalarQ[k]]
	,
	True
	,
	TestID -> "TrReduce-ScalarQ-4"
]

Test[
	ScalarQ[Tr[X]+Det[X]]
	,
	True
	,
	TestID -> "TrReduce-ScalarQ-5"
]

Test[
	ScalarQ[Tr[X] X]
	,
	False
	,
	TestID -> "TrReduce-ScalarQ-6"
]
