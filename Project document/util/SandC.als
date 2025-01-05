  //&&&&&&&&&//
 //Signatures//       
//&&&&&&&&//
sig Student{
	uni : University
}

sig University {
}

sig Company {
	internships : set Internship
}


sig Internship {
	company: Company,
	status: InternshipStatus
}

abstract sig Request {
	student: Student,
	internship: Internship,
}

sig Recommendation extends Request{
	student_status: Status,
	company_status: Status
} 

sig Application extends Request{
	status: Status
}


sig Contact {
	company: Company,
	student: Student,
	internship: Internship,
	status: Status
}

sig Complaint{
	internship: one Internship
}

  //&&&&&&&&&&&//
 //Enumerations//
//&&&&&&&&&&&//

enum InternshipStatus {NA, ongoing}

enum Status {waiting, accepted, rejected}

  //&&&&&//
 //Facts//
//&&&&&//

//An internship belongs to a company
fact internshipBelongsToCompany{
 all i: Internship, c: Company | i.company = c implies i in c.internships
}

//An internship belongs to a single company
fact noIntershipBelongingToDifferentCompanies{
  all disj c1,c2: Company, i: Internship | 
    (i in c1.internships implies i not in c2.internships) or 
      (i in c2.internships implies i not in c1.internships)
}

//Some students belong to the same uni
fact studentsFromUni {
  some disj s1,s2: Student | s1.uni = s2.uni
}

//No duplicated application or recommendation between the same actors
fact noDuplicatedRequest {
  all disj a,r: Request | 
    !(a.student = r.student and a.internship = r.internship)
}

//A student must have at most one intership ongoing
fact oneOngoingInternshipPerStudent{
  all s:Student |
    (all disj r1,r2:Request | 
      (r1.student = s and r2.student = s and r1.internship.status = ongoing) 
        implies r2.internship.status = NA)
}

//In contact internship belongs to the company
fact contactSameInternshipAndCompany {
  all c: Contact | c.company = c.internship.company
}


//A contact is Made
fact contactCreatedIfAcceptedApplicationOrRecommendation {
    all c: Contact | 
		(c.status = waiting or c.status = accepted or c.status = rejected)
		 implies ((one a: Application |
			 (a.student = c.student and a.internship.company = c.company 
				and a.internship = c.internship and a.status = accepted)) or
        (one r: Recommendation | 
			(r.student = c.student and r.internship.company = c.company 
				and r.internship = c.internship and
			r.student_status = accepted and r.company_status = accepted)))
}

//One internship can have only one contact in status accepted
fact oneContactAcceptedPerInternship{
	all disj c1, c2 : Contact |
		((c1.company = c2.company 
			and c1.internship = c2.internship and c1.status = accepted) 
				implies c2.status = rejected) or 
		((c1.company = c2.company 
			and c1.internship = c2.internship and c2.status = accepted) 
				implies c1.status = rejected)
}


//One contact max between the same actors
fact oneContactMax {
    all disj c1, c2: Contact | 
		!(c1.student = c2.student and c1.company = c2.company)
}

//If the contact is accepted the internship is ongoing
fact acceptedContactInternship {
	all c: Contact | 
		c.status = accepted implies c.internship.status = ongoing 
}

//Each ongoing internship has a contact that is accepted
fact acceptedInternshipContact { 
	all i: Internship, c: Contact | 
		( i = c.internship and i.status = ongoing ) 
			implies c.status = accepted 
}

//An ongoing internship requires a contact that is accepted
fact InternshipRequiresAcceptedContactForOngoing {
    all i: Internship | 
        i.status = ongoing implies 
        one c: Contact |
			c.internship = i and c.company = i.company 
				and c.status = accepted
}

//Internship not available has all contact rejected
fact naInternshipHAsContactRejected{
	all i:Internship |
		i.status = NA implies
			(all c: Contact | 
				c.internship = i implies c.status = waiting 
										or  c.status = rejected) 
}

//An ongoing internshp has an accepted application or recommendation
fact acceptedInternshipRecommendationApplication{
	all i: Internship |
		i.status = ongoing implies 
			(( some a:Application |
				 a.internship = i implies a.status = accepted) or 
			( some r:Recommendation |
					 r.internship = i implies 
						(r.student_status = accepted and  
							r.company_status = accepted))) 
}

//Only the ongoing internships can have complaints
fact noComplaintForNA{
	all c:Complaint | c.internship.status = ongoing 
}


  //&&&&&&&&&&//
 //Predicates//
//&&&&&&&&&&//

pred Minimal {
	#University= 1
	#Company = 1
	#Student = 2
	#Internship = 1
	#Application = 1
	#Contact = 1
	#Complaint = 1
}

pred world{
	some i: Internship | i.status = ongoing
	some a : Application | a.status = accepted
	some r: Recommendation | r.student_status = accepted and
		 r.company_status = accepted
	#University= 1
	#Company = 2
	#Student = 2
	#Internship = 5
	#Recommendation = 2
	#Application = 2
	#Contact = 3
	#Complaint = 2
}

//run Minimal for 10

  //&&&&&&&&&&//
 //Assertions//
//&&&&&&&&&&//

assert OneAcceptedContactPerInternship {
    all disj c1, c2: Contact | 
        (c1.internship = c2.internship and c1.status = accepted) implies
			 c2.status != accepted
}

assert InternshipAcceptedHasAcceptedContact {
    all i: Internship | 
        i.status = ongoing implies 
       some c: Contact | c.internship = i and c.status = accepted
}

assert AcceptedContactImpliesOngoingInternship {
    all c: Contact | 
        c.status = accepted implies c.internship.status = ongoing
}

assert OneOngoingInternshipPerStudent {
    all s: Student | 
        lone i: Internship | 
			i.status = ongoing and some r: Request | 
				r.student = s and r.internship = i
}


assert NoDuplicatedRequests {
    all disj r1, r2: Request | 
        !(r1.student = r2.student and r1.internship = r2.internship)
}


assert InternshipBelongsToOneCompany {
    all i: Internship | 
        one c: Company | i in c.internships
}

assert NoDuplicateInternshipBetweenCompanies {
    all disj c1, c2: Company | 
        no i: Internship | i in c1.internships and i in c2.internships
}

assert StudentsFromSameUniversity {
    some disj s1, s2: Student | s1.uni = s2.uni
}

assert noComplaintForNAInternships{
	all i: Internship, c: Complaint |
		 i.status = NA implies c.internship != i
}

  //&&&&&&//
 //Checks//
//&&&&&&//

//check OneAcceptedContactPerInternship

//check InternshipAcceptedHasAcceptedContact

//check AcceptedContactImpliesOngoingInternship

//check OneOngoingInternshipPerStudent

//check NoDuplicatedRequests

//check InternshipBelongsToOneCompany

//check NoDuplicateInternshipBetweenCompanies

//check StudentsFromSameUniversity

//check noComplaintForNAInternships
