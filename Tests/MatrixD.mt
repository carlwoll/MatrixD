(* Wolfram Language Test file *)

(* The Matrix Cookbook tests *)

Test[
	MatrixD[Det[X], X]
	,
	Det[X] Inverse[Transpose[X]]
	,
	TestID -> "MatrixCookbook-49"
]

Test[
	MatrixD[Det[A.X.B], X]
	,
	Det[A.X.B] Inverse[Transpose[X]]
	,
	TestID -> "MatrixCookbook-51"
]

Test[
	MatrixD[Det[X\[Transpose].A.X], X]
	,
	2 Det[Transpose[X].A.X] Inverse[Transpose[X]]
	,
	TestID -> "MatrixCookbook-52"
]

Test[
	MatrixD[Det[X\[Transpose].A.X], X, "Invertible"->False]
	,
	Det[Transpose[X].A.X] (A.X.Inverse[Transpose[X].A.X] + Transpose[A].X.Inverse[Transpose[X].Transpose[A].X])
	,
	TestID -> "MatrixCookbook-54"
]

Test[
	MatrixD[Log @ Det[X\[Transpose].X], X]
	,
	2 Inverse[Transpose[X]]
	,
	TestID -> "MatrixCookbook-55"
]

Test[
	MatrixD[Log @ Det[X], X]
	,
	Inverse[Transpose[X]]
	,
	TestID -> "MatrixCookbook-57"
]

Test[
	MatrixD[Det[MatrixPower[X, k]], X]
	,
	k Det[MatrixPower[X, k]] Inverse[Transpose[X]]
	,
	TestID -> "MatrixCookbook-58"
]

Test[
	MatrixD[Inverse[X], X]
	,
	-Inverse[X] . $SingleEntryMatrix . Inverse[X]
	,
	TestID -> "MatrixCookbook-60"
]

Test[
	MatrixD[Det[Inverse[X]], X]
	,
	-Det[Inverse[X]] Inverse[Transpose[X]]
	,
	TestID -> "MatrixCookbook-62"
]

Test[
	MatrixD[Tr[A.Inverse[X].B], X]
	,
	-Inverse[Transpose[X]].Transpose[A].Transpose[B].Inverse[Transpose[X]]
	,
	TestID -> "MatrixCookbook-63"
]

Test[
	MatrixD[Tr[Inverse[X+A]], X]
	,
	-MatrixPower[Transpose[A] + Transpose[X], -2]
	,
	TestID -> "MatrixCookbook-64"
]

Test[
	MatrixD[Tr[X], X]
	,
	$IdentityMatrix
	,
	TestID -> "MatrixCookbook-65"
]

Test[
	MatrixD[Det[X], X]
	,
	Det[X] Inverse[Transpose[X]]
	,
	TestID -> "MatrixCookbook-66"
]

Test[
	MatrixD[X, X]
	,
	$SingleEntryMatrix
	,
	TestID -> "MatrixCookbook-73"
]

Test[
	MatrixD[X.A, X]
	,
	$SingleEntryMatrix.A
	,
	TestID -> "MatrixCookbook-74"
]

Test[
	MatrixD[X\[Transpose].A, X]
	,
	Transpose[$SingleEntryMatrix].A
	,
	TestID -> "MatrixCookbook-75"
]

Test[
	MatrixD[X\[Transpose].B.X, X]
	,
	Transpose[X].B.$SingleEntryMatrix + Transpose[$SingleEntryMatrix].B.X
	,
	TestID -> "MatrixCookbook-80"
]

Test[
	MatrixD[MatrixPower[X, k], X]
	,
	Sum[MatrixPower[X, \[FormalK]] . $SingleEntryMatrix . MatrixPower[X, -1 - \[FormalK] + k], {\[FormalK], 0, -1 + k}]
	,
	TestID -> "MatrixCookbook-90"
]

Test[
	MatrixD[Tr[X], X]
	,
	$IdentityMatrix
	,
	TestID -> "MatrixCookbook-99"
]

Test[
	MatrixD[Tr[X.A], X]
	,
	Transpose[A]
	,
	TestID -> "MatrixCookbook-100"
]

Test[
	MatrixD[Tr[A.X.B], X]
	,
	Transpose[A].Transpose[B]
	,
	TestID -> "MatrixCookbook-101"
]

Test[
	MatrixD[Tr[A.X\[Transpose].B], X]
	,
	B.A
	,
	TestID -> "MatrixCookbook-102"
]

Test[
	MatrixD[Tr[X\[Transpose].A], X]
	,
	A
	,
	TestID -> "MatrixCookbook-103"
]

Test[
	MatrixD[Tr[A.X\[Transpose]], X]
	,
	A
	,
	TestID -> "MatrixCookbook-104"
]

Test[
	MatrixD[Tr[X.X], X]
	,
	2 Transpose[X]
	,
	TestID -> "MatrixCookbook-106"
]

Test[
	MatrixD[Tr[X.X.B], X]
	,
	Transpose[B].Transpose[X]+Transpose[X].Transpose[B]
	,
	TestID -> "MatrixCookbook-107"
]

Test[
	MatrixD[Tr[X\[Transpose].B.X], X]
	,
	B.X+Transpose[B].X
	,
	TestID -> "MatrixCookbook-108"
]

Test[
	MatrixD[Tr[B.X.X\[Transpose]], X]
	,
	B.X+Transpose[B].X
	,
	TestID -> "MatrixCookbook-109"
]

Test[
	MatrixD[Tr[X.X\[Transpose].B], X]
	,
	B.X+Transpose[B].X
	,
	TestID -> "MatrixCookbook-110"
]

Test[
	MatrixD[Tr[X.B.X\[Transpose]], X]
	,
	X.B+X.Transpose[B]
	,
	TestID -> "MatrixCookbook-111"
]

Test[
	MatrixD[Tr[B.X\[Transpose].X], X]
	,
	X.B+X.Transpose[B]
	,
	TestID -> "MatrixCookbook-112"
]

Test[
	MatrixD[Tr[X\[Transpose].X.B], X]
	,
	X.B+X.Transpose[B]
	,
	TestID -> "MatrixCookbook-113"
]

Test[
	MatrixD[Tr[A.X.B.X], X]
	,
	Transpose[A].Transpose[X].Transpose[B]+Transpose[B].Transpose[X].Transpose[A]
	,
	TestID -> "MatrixCookbook-114"
]

Test[
	MatrixD[Tr[X\[Transpose].X], X] == MatrixD[Tr[X.X\[Transpose]], X] == 2 X
	,
	True
	,
	TestID -> "MatrixCookbook-115"
]

Test[
	MatrixD[Tr[B\[Transpose].X\[Transpose].C.X.B], X]
	,
	C.X.B.Transpose[B]+Transpose[C].X.B.Transpose[B]
	,
	TestID -> "MatrixCookbook-116"
]

Test[
	MatrixD[Tr[X\[Transpose].B.X.C], X]
	,
	B.X.C+Transpose[B].X.Transpose[C]
	,
	TestID -> "MatrixCookbook-117"
]

Test[
	MatrixD[Tr[A.X.B.X\[Transpose].C], X]
	,
	C.A.X.B+Transpose[A].Transpose[C].X.Transpose[B]
	,
	TestID -> "MatrixCookbook-118"
]

Test[
	MatrixD[Tr[(A.X.B+C).(A.X.B+C)\[Transpose]], X]
	,
	2 Transpose[A].C.Transpose[B]+2 Transpose[A].A.X.B.Transpose[B]
	,
	TestID -> "MatrixCookbook-119"
]

Test[
	MatrixD[Tr[MatrixPower[X, k]], X]
	,
	k MatrixPower[Transpose[X],-1+k]
	,
	TestID -> "MatrixCookbook-121"
]

Test[
	MatrixD[Tr[A.MatrixPower[X, k]], X]
	,
	Sum[MatrixPower[Transpose[X], \[FormalK]] . Transpose[A] . MatrixPower[Transpose[X], -1 - \[FormalK] + k], {\[FormalK], 0, -1 + k}]
	,
	TestID -> "MatrixCookbook-122"
]

Test[
	MatrixD[Tr[B\[Transpose].X\[Transpose].C.X.X\[Transpose].C.X.B], X]
	,
	C.X.B.Transpose[B].Transpose[X].C.X + C.X.Transpose[X].C.X.B.Transpose[B] +
	Transpose[C].X.B.Transpose[B].Transpose[X].Transpose[C].X + Transpose[C].X.Transpose[X].Transpose[C].X.B.Transpose[B]
	,
	TestID -> "MatrixCookbook-123"
]

Test[
	MatrixD[Tr[A.Inverse[X].B], X]
	,
	-Inverse[Transpose[X]].Transpose[A].Transpose[B].Inverse[Transpose[X]]
	,
	TestID -> "MatrixCookbook-124"
]

Test[
	MatrixD[Tr[Inverse[X\[Transpose].C.X].A], X]
	,
	-Inverse[Transpose[X]].A.Inverse[X].Inverse[C].Inverse[Transpose[X]]-Inverse[Transpose[X]].Transpose[A].Inverse[X].Inverse[Transpose[C]].Inverse[Transpose[X]]
	,
	TestID -> "MatrixCookbook-125"
]

Test[
	MatrixD[Tr[MatrixFunction[Sin, X]], X]
	,
	Transpose[MatrixFunction[Cos[#1]&,X]]
	,
	TestID -> "MatrixCookbook-128"
]

(* Unsupported tests *)

Test[
	MatrixD[MatrixFunction[Log, X], X]
	,
	$Failed
	,
	{MatrixD::unsup}
	,
	TestID -> "Unsupported-1"
]

Test[
	MatrixD[Log[X], X]
	,
	$Failed
	,
	{MatrixD::scalar}
	,
	TestID -> "Unsupported-2"
]

Test[
	MatrixD[Tr[A.MatrixFunction[Sin, X]], X]
	,
	$Failed
	,
	{MatrixD::unsup}
	,
	TestID -> "Unsupported-3"
]

(* TensorReduce issues *)
Test[
	MatrixD[MatrixPower[Det[X] X, k], X]
	,
	k Det[X]^k Inverse[Transpose[X]] MatrixPower[X, k] + 
	Det[X]^k Sum[MatrixPower[X, \[FormalK]] . \[DoubleStruckCapitalJ] . MatrixPower[X, -1 - \[FormalK] + k], {\[FormalK], 0, -1 + k}]
	,
	TestID -> "TensorReduce-1"
]