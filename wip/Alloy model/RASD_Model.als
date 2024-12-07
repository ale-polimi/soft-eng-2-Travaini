open util/integer

enum StudentStatus {Searching, Hired}

enum ApplicationStatus {AcceptedForContact, Declined, Ongoing}

sig Student {
	var studentStatus: one StudentStatus,
}

sig Company {

}

sig Internship {
	company: one Company,
	var openPositions: one Int
} {
	openPositions >= 0
}

sig Application {
	student: one Student,
	internship: one Internship,
	var applicationStatus: one ApplicationStatus
}

// If an application is ongoing, the open positions for that internship must decrease
fact {
	always(all a:Application | a.applicationStatus = Ongoing implies a.internship.openPositions' = a.internship.openPositions - 1)
}

// Some applications become ongoing.
fact {
	eventually(some a:Application | a.applicationStatus = AcceptedForContact and a.applicationStatus' = Ongoing)
}

// Some applications become declined
fact {
	eventually(some a:Application | a.applicationStatus = AcceptedForContact and a.applicationStatus' = Declined)
}

// If an internship goes from AcceptedForContact to Ongoing, the student must go from Searching to Hired
fact {
	always(all a:Application | (a.applicationStatus = AcceptedForContact and a.applicationStatus' = Ongoing) iff (a.student.studentStatus = Searching and a.student.studentStatus' = Hired))
}

// No regression of application status
fact {
	always(no a:Application | a.applicationStatus = Ongoing and a.applicationStatus' = Declined) and
	always(no a:Application | a.applicationStatus = Ongoing and a.applicationStatus' = AcceptedForContact)
	always(no a:Application | a.applicationStatus = Declined and (a.applicationStatus' = AcceptedForContact or a.applicationStatus' = Ongoing))
}

// No regression of student status
fact {
	always(no s:Student | s.studentStatus = Hired and s.studentStatus' = Searching)
}

// The number of open positions must decrease if a student is hired
fact {
	always(all a:Application | (a.applicationStatus = AcceptedForContact and a.applicationStatus' = Ongoing) implies a.internship.openPositions' = minus[a.internship.openPositions, 1])
}

// The number of open positions must not change for internships that do not have interns
fact {
	always(all a:Application | (a.applicationStatus = AcceptedForContact and a.applicationStatus' != Ongoing) implies a.internship.openPositions' = a.internship.openPositions)
}

// If an internship is not in any application, its open positions must not change
fact {
	always(all i:Internship, a:Application | i not in a.internship implies i.openPositions' = i.openPositions)
}

// No student can be in more than 1 ongoing internship at a time
fact {
	always(all disj a1, a2:Application | (a1.applicationStatus = Ongoing and a2.applicationStatus = Ongoing) implies #(a1.student & a2.student) = 0)
}

// Initialization state
fact init {
	Student.studentStatus = Searching
	Internship.openPositions > 0
}

pred show {
	#Student <= 4
}

run show
