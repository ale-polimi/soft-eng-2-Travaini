enum StudentStatus {Searching, Hired}

enum ApplicationStatus {AcceptedForContact, Declined, Ongoing}

sig Student {
	var studentStatus: one StudentStatus,
}

sig Company {

}

sig Internship {
	company: one Company,
	var openPositions: one Int,
} {
	openPositions > 0
}

sig Application {
	student: one Student,
	internship: one Internship,
	var applicationStatus: one ApplicationStatus
}

// If a student has an ongoing application, it means that he's hired.
fact {
	all s:Student, a:Application | a.applicationStatus = Ongoing and s = a.student implies s.studentStatus = Hired
}

// A hired student is in at most 1 ongoing internship at a time.
fact {
	all s:Student | all disj a1, a2:Application | (s in a1.student and s in a2.student and s.studentStatus = Hired) implies #(a1.applicationStatus & a2.applicationStatus) = 0
}

// The number of hired students in an internship must not exceed the number of open positions
fact NoOverhiring {
	no a:Application, i:Internship, s:Student | s = a.student and a.applicationStatus = Ongoing and s.studentStatus = Hired and #a > i.openPositions
}

pred show {
//	#Application = 2
}

run show
