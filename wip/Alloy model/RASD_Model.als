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

// No student can be hired without an application
fact {
	always(no s:Student | all a:Application | s not in a.student and s.studentStatus = Hired)
}

// No searching student with an ongoing application
fact {
	always(all a:Application | a.applicationStatus = Ongoing iff a.student.studentStatus = Hired)
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
	always(all a:Application | (a.applicationStatus = AcceptedForContact and a.applicationStatus' = Ongoing) implies a.internship.openPositions' = minus[a.internship.openPositions, #(SubsetOfOngoingApplications[a])])
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
	always(all disj a1, a2:Application | (a1.applicationStatus = Ongoing and a2.applicationStatus = Ongoing) implies a1.student != a2.student)
}

// Initialization state
fact init {
	Student.studentStatus = Searching
	Internship.openPositions > 0
}

fun SubsetOfOngoingApplications[a:Application]: Application {
	{x:a | x.applicationStatus' = Ongoing and x.internship = a.internship}
}

pred show {
	#student = 3
}

run show
