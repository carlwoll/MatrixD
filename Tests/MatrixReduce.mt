(* Wolfram Language Test file *)

Test[
	MatrixReduce[Tr[A.$SingleEntryMatrix.B]]
	,
	Transpose[A].Transpose[B]
	,
	TestID -> "MatrixReduce-1"
]

Test[
	MatrixReduce[Tr[A.Transpose[X.$SingleEntryMatrix.Inverse[Transpose[A]]]]]
	,
	Transpose[X]
	,
	TestID -> "MatrixReduce-2"
]

Test[
	MatrixReduce[Tr[Det[X]X.$SingleEntryMatrix]]
	,
	Det[X] Transpose[X]
	,
	TestID -> "MatrixReduce-3"
]
	