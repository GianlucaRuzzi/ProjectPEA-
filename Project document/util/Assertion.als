assert InternshipAcceptedHasAcceptedContact {
	all i: Internship | 
		i.status = ongoing implies 
			some c: Contact | c.internship = i and c.status = accepted
}
check InternshipAcceptedHasAcceptedContact
