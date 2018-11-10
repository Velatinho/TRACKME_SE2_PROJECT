open util/boolean
open util/integer


sig AutomatedSOS{
	user: one IndividualUser,
	sendWarning: one Bool
}
{(user.data.healthData.vitalParameters <=4 implies sendWarning = True) and
(sendWarning = True implies user.data.healthData.vitalParameters <=4)}

-------------------------------------------------

sig Data{
	healthData: one HealthData,
	locationData: one LocationData,
}
sig HealthData{
	vitalParameters:  Int
}{vitalParameters >= 0 and vitalParameters <=7}
sig LocationData{}

-------------------------------------------------

//Requests Status
abstract sig Status{}
sig Accepted extends Status{}
sig Pending extends Status{}
sig Refused extends Status{}

-------------------------------------------------

abstract sig Request{
	sender: one CompanyUser,
	status: one Status,
	data: one Data
}
sig SingleRequest extends Request{
	recipient: one IndividualUser,
}
//The number of people in a GroupRequest must be grater than 1000 to be anonymous variable equal to True
sig GroupRequest extends Request{
	anonymous: one Bool,
	numberPeople: one Int
}
{(numberPeople>0) and (anonymous = False implies status = Refused) and (status = Refused implies anonymous=False) and
(anonymous = True implies status = Accepted) and (status = Accepted implies anonymous=True) and
(anonymous = True implies numberPeople >=4) and (numberPeople >=4 implies anonymous=True)}

-------------------------------------------------

abstract sig RegisteredUser{}
sig IndividualUser extends RegisteredUser{
	receivedRequests: set SingleRequest,
	data: one Data,
	automatedSOS: lone AutomatedSOS
}
sig CompanyUser extends RegisteredUser{
	sentRequests: set Request,
	availableData: set Data
}

-------------------------------------------------

//Every AutomatedSOS instance has its IndividualUser instance
fact AutomatedSOSIndividualUserConnection{
	all u: IndividualUser | all a: AutomatedSOS | (a in u.automatedSOS implies a.user=u) and (u in a.user implies u.automatedSOS=a)
}

//Every Request made by a CompanyUser implies that the CompanyUser is the sender of the Request
fact RequestCompanyUserConnection{
	all u:CompanyUser | (all r: Request | (r in u.sentRequests implies r.sender=u) and (u in r.sender implies u.sentRequests=r))
}

//Every CompanyUser can access to the AvailableData only if has already sent a request and the request has been accepted
fact AvailableData{
	all u: CompanyUser | all d: Data | (d in u.availableData implies (some r: Request | (r in u.sentRequests and r.status=Accepted and r.data=d)))
	and (all r: Request | (r in u.sentRequests and r.status=Accepted and r.data=d) implies d in u.availableData)
}

//Every data in a SingleRequest must be the same in the IndividualUser who is the recipient of the Request
fact DataIndividualUserDataRequestConnection{
	all r: SingleRequest | (all u: IndividualUser | (u in r.recipient implies r.data = u.data))
}

//Every Request recieved by an IndividualUser implies that the IndividualUser is the recipient of the Request
fact SigleRequestIndividualUserConnection{
	all u: IndividualUser | (all r: SingleRequest | (r in u.receivedRequests implies r.recipient = u) and (u in r.recipient implies u.receivedRequests = r))
}

//Every IndividualUser has his own Data
fact UniqueIndividualData{
	no disjoint u1,u2: IndividualUser | u1.data = u2.data
}

//The Data of a GroupRequest must be different from the Data of an IndividualUser
fact NoCommonDataGroupRequestIndividualUser{
	all u: IndividualUser | all r: GroupRequest | u.data !=r.data
}

//The Data must be unique
fact UniqueData{
	no disjoint d1,d2: Data | d1.healthData = d2.healthData or d1.locationData = d2.locationData
}

-------------------------------------------------


pred createSingleRequest(u: CompanyUser, u2: IndividualUser, r: SingleRequest, d: Data){
	r.sender = u
	r.recipient = u2
	r.data = d
}

pred createGroupRequest(u: CompanyUser, r: GroupRequest, d: Data){
	r.sender = u
	r.data = d
}

pred acceptedRequest(u: IndividualUser, r: SingleRequest){
	r.status= Accepted
	u.receivedRequests = r
}

pred refusedRequest(u: IndividualUser, r: SingleRequest){
	r.status= Refused
	u.receivedRequests = r
}

pred sendWarning(a: AutomatedSOS, u: IndividualUser){
	a.user = u
	u.data.healthData.vitalParameters <= 4
}

pred show{}

//A CompanyUser has any availableData if he has already sent a request and this has been already accepted
assert availableData{
	all u: CompanyUser | (all r: Request | all d: Data | ( r in u.sentRequests and d in r.data and r.status=Accepted) implies u.availableData=d)
}

//A group request must be refused if the number of people investigated is less than 4 (in the real world if the number is less than 1000)
assert anonymityGroupRequest{
	all r: GroupRequest | (r.numberPeople < 4 implies r.status=Refused) and (r.status=Refused implies r.numberPeople < 4)
}

run show for 10 but  exactly 2 Status, exactly 2 Data, 
	exactly 2 LocationData, exactly 2 HealthData, exactly 1 AutomatedSOS, exactly 1 IndividualUser, 
	exactly 1 SingleRequest, exactly 1 GroupRequest, exactly 2 CompanyUser
run sendWarning
run refusedRequest
run acceptedRequest
run createSingleRequest 
run createGroupRequest
check availableData
check anonymityGroupRequest

