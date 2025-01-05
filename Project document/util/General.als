pred world{
	some i: Internship | i.status = ongoing
	some a : Application | a.status = accepted
	some r: Recommendation |
	 r.student_status = accepted and r.company_status = accepted
	#University= 1
	#Company = 2
	#Student = 2
	#Internship = 5
	#Recommendation = 2
	#Application = 2
	#Contact = 3
	#Complaint = 2
}
run world for 10
