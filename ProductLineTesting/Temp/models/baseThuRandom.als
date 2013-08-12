
module CrisisManagementSystemModel

one sig ProductConfigurations
{	
	configurations : set Configuration
}

sig Configuration
{
f1: one CrisisManagementSystem,
f2: one Communication,
f3: one CrisisType,
f4: one GSMTelephony,
f5: one GPSLocation,
f6: lone Fire,
f7: lone HealthEmergency,
f8: lone CarAccident,
f9: lone Theft,
f10: lone LocalOperator,
f11: lone FireStation,
f12: lone Ambulance,
f13: lone Police,
f14: lone InternationalOperator,
f15: lone HospitalAdmit,
f16: lone SurveillanceCamera
}

sig CrisisManagementSystem {}
sig Communication  {}
sig CrisisType  {}
sig GSMTelephony  {}
sig GPSLocation {}
sig Fire  {}
sig Theft  {}
sig CarAccident  {}
sig HealthEmergency  {}
sig Ambulance  {}
sig HospitalAdmit  {}
sig InternationalOperator {}
sig LocalOperator {}
sig Police  {}
sig FireStation  {}
sig SurveillanceCamera  {}


fact Configuration_container
{
	all c : Configuration | c in ProductConfigurations.configurations
}


//Constraints due to operators:

//Optional Fire

fact Invariant_Operator_1
{
	all c:Configuration | #c.f6=1 implies ( #c.f3=1)
}   


//Optional Healthemergency
fact Invariant_Operator_2
{
	all c:Configuration | #c.f7=1 implies ( #c.f3=1)
}   

//Optional Car Accident
fact Invariant_Operator_3
{
	all c:Configuration | #c.f8=1 implies ( #c.f3=1)
}   


//Optional Theft
   
fact Invariant_Operator_4
{
	all c:Configuration | #c.f9=1 implies ( #c.f3=1)
}   

//Optional Ambulance
//New type of constraint
 
fact Invariant_Operator_5
{
	all c:Configuration | #c.f12=1 and #c.f7=0 and #c.f8=0 implies ( #c.f6=1)
}  


//Optional Police
//New type of constraint
 
fact Invariant_Operator_6
{
	all c:Configuration | #c.f13=1 and #c.f9=0 implies ( #c.f8=1)
}  

//Optional Surveillance Camera

 
fact Invariant_Operator_7
{
	all c:Configuration | #c.f16=1 implies ( #c.f13=1)
}  


//LocalOperator XOR

fact Invariant_Operator_8
{
	all c:Configuration | #c.f10=1 implies ( #c.f4=1 and #c.f14=0)
}   


//InternationalOperator XOR

fact Invariant_Operator_9
{
	all c:Configuration | #c.f14=1 implies ( #c.f4=1 and #c.f10=0)
}   


//Fire AND

fact Invariant_Operator_10
{
	all c:Configuration | #c.f6=1 implies ( #c.f11=1 )
}   




//Health Emergency AND

fact Invariant_Operator_11
{
	all c:Configuration | #c.f7=1 implies ( #c.f12=1)
}   


//Ambulance AND

fact Invariant_Operator_12
{
	all c:Configuration | #c.f12=1 implies ( #c.f15=1 and (#c.f7=1 or #c.f8=1))
}   

//Car Accident AND

fact Invariant_Operator_13
{
	all c:Configuration | #c.f8=1 implies ( #c.f12=1)
}   

//Theft AND

fact Invariant_Operator_14
{
	all c:Configuration | #c.f9=1 implies ( #c.f13=1)
}   

//GSMTelephony AND

fact Invariant_Operator_15
{
	all c:Configuration | #c.f4=1 implies ( #c.f10=1 and #c.f14=0) or (#c.f10=0 and #c.f14=1)
}   


//FireStation AND
fact Invariant_Operator_16
{
	all c:Configuration | #c.f11=1 implies ( #c.f6=1)
}   


//Police AND
fact Invariant_Operator_17
{
	all c:Configuration | #c.f13=1 implies ( #c.f16=1 and (#c.f8=1 or #c.f9=1))
}   

pred Random{ #Configuration =7}

run Random for 7


