module CarCrashCrisisManagementSystemModel

open util/boolean as Bool

//Context Signature

sig Context
{
	responseTime : Int
	dayOrNight : Bool
	
one sig ProductConfigurations
{	
	configurations : set Configuration
}

sig Configuration
{
f1: one CrisisManagementSystem,
f2: one LongDistanceCall,
f3: lone GSM,
f4: lone GPS,
f5: one InternalResource,
f6: one FirstAidMaterial,
f7: one HumanResource,
f8: one SystemAdmin,
f9: one Worker,
f10: one Coordinator,
f11: one FAWorker,
f12: lone Observer,
f13: lone RemoveObstacle,
f14: lone Rescue,
f15: lone Observe,
f16: lone Transport,
f17: one Mission,
f18: lone Investigation,
f19: lone NurseTheWounded,
f20: lone SortTheWounded,
f21: one Area,
f22: one Small,
f23: one ExternalServicesUsed,
f24: one GovernmentalServices,
f25: lone Police,
f26: lone FireDepartment,
f27: lone Policeman,
f28: lone DatabaseSystem,
f29: lone AuthenticationSystem,
f30: lone SurveillanceSystem,
f31: lone HumanVictims,
f32: lone Witness,
f33: one CrisisType,
f34: one SuddenCrisis,
f35: one MajorAccident,
f36: one CarCrash,
f37: lone ExternalCompany,
f38: lone GarageTowTruck,
f39: lone MedicalServices,
f40: lone PrivateAmbulanceCompany,
f41: lone Fireman,
f42: lone PublicHospital,
f43: lone HospitalWorker,
f44: lone Ambulance,
f45: lone FirstAidWorker,
f46: lone ITOption
}

sig CrisisManagementSystem {}
sig LongDistanceCall {}
sig GSM {}
sig GPS {}
sig InternalResource {}
sig FirstAidMaterial {}
sig HumanResource {}
sig SystemAdmin {}
sig Worker {}
sig Coordinator {}
sig FAWorker {}
sig Observer {}
sig RemoveObstacle {}
sig Rescue {}
sig Observe {}
sig Transport {}
sig Mission {}
sig Investigation {}
sig NurseTheWounded {}
sig SortTheWounded {}
sig Area {}
sig Small {}
sig ExternalServicesUsed {}
sig GovernmentalServices {}
sig Police {}
sig FireDepartment {}
sig Policeman {}
sig DatabaseSystem {}
sig AuthenticationSystem {}
sig SurveillanceSystem {}
sig HumanVictims {}
sig Witness {}
sig CrisisType {}
sig SuddenCrisis {}
sig MajorAccident {}
sig CarCrash {}
sig ExternalCompany {}
sig GarageTowTruck {}
sig MedicalServices {}
sig PrivateAmbulanceCompany {}
sig Fireman {}
sig PublicHospital {}
sig HospitalWorker {}
sig Ambulance {}
sig FirstAidWorker {}
sig ITOption {}



fact Configuration_container
{
	all c : Configuration | c in ProductConfigurations.configurations
}

//Constraints on Car Crash Crisis Management Feature Diagram


fact Invariant1
{
  	all c:Configuration | #c.f28==1 implies #c.f46=1
}

fact Invariant2
{
	all c:Configuration | #c.f29==1 implies #c.f46=1
}

fact Invariant3
{
	all c:Configuration | #c.f30==1 implies #c.f46=1
}

fact Invariant4
{
	all c:Configuration | #c.f25==1 implies #c.f27=1
}

fact Invariant5
{
	all c:Configuration | #c.f26==1 implies #c.f41=1
}

fact Invariant6
{
	all c:Configuration | #c.f38==1 implies #c.f37=1
}

fact Invariant7
{
	all c:Configuration | #c.f40==1 implies #c.f39=1
}

fact Invariant8
{
	all c:Configuration | #c.f42==1 implies #c.f39=1
}

fact Invariant9
{
	all c:Configuration | #c.f43==1 implies #c.f42=1
}

fact Invariant10
{
	all c:Configuration | #c.f42==1 implies #c.f45=1
}

fact Invariant11
{
	all c:Configuration | #c.f44==1 implies #c.f42=1
}

pred x{#Configuration=1}
run x for 20
