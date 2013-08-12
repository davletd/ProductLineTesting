
module CrisisManagementSystemModel

one sig ProductConfigurations
{	
	configurations : set Configuration
}

sig Configuration
{
f1: one CrisisManagementSystem,
f2: one Communication,
f3: one ExternalAgencies,
f4: one CrisisType,
f5: lone GSMGPS,
f6: one Medical,
f7: one Security,
f8: lone Fire,
f9: lone Theft,
f10: lone CarAccident,
f11: lone HealthEmergency,
f12: lone Ambulance,
f13: lone HospitalAdmit,
f14: lone Police,
f15: lone FireStation,
f16: lone SurveillanceCamera
}

sig CrisisManagementSystem {}
sig Communication  {}
sig ExternalAgencies  {}
sig CrisisType  {}
sig GSMGPS  {}
sig Medical  {}
sig Security  {}
sig Fire  {}
sig Theft  {}
sig CarAccident  {}
sig HealthEmergency  {}
sig Ambulance  {}
sig HospitalAdmit  {}
sig Police  {}
sig FireStation  {}
sig SurveillanceCamera  {}


fact Configuration_container
{
	all c : Configuration | c in ProductConfigurations.configurations
}


//Constraints due to operators:

//Optional Ambulance

fact Invariant_Operator_1
{
	all c:Configuration | #c.f12=1 implies ( #c.f6=1)
}   

//Optional Hospital Admit
fact Invariant_Operator_2
{
	all c:Configuration | #c.f13=1 implies ( #c.f6=1)
}   


//Optional Police
fact Invariant_Operator_3
{
	all c:Configuration | #c.f14=1 implies ( #c.f7=1)
}   

//Optional Fire Station
fact Invariant_Operator_4
{
	all c:Configuration | #c.f15=1 implies ( #c.f7=1)
}   

//Surveillance Camera if Police
fact Invariant_Operator_5
{
	all c:Configuration | #c.f16=1 implies ( #c.f14=1)
}   

//Fire XOR

fact Invariant_Operator_6
{
	all c:Configuration | #c.f8=1 implies ( #c.f9=0 and #c.f10=0 and #c.f11=0)
}   


//Theft XOR

fact Invariant_Operator_6
{
	all c:Configuration | #c.f9=1 implies ( #c.f8=0 and #c.f10=0 and #c.f11=0)
}   


//Car Accident XOR

fact Invariant_Operator_6
{
	all c:Configuration | #c.f10=1 implies ( #c.f8=0 and #c.f9=0 and #c.f11=0)
}   



//Health Emergency XOR

fact Invariant_Operator_6
{
	all c:Configuration | #c.f11=1 implies ( #c.f8=0 and #c.f9=0 and #c.f10=0)
}   


pred empty{}

run empty for 20
