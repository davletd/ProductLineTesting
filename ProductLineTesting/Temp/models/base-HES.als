
module HealthEmergencySystem

one sig ProductConfigurations
{	
	configurations : set Configuration
}

sig Configuration
{
f1: one HealthEmergencySystem,
f2: one Transport,
f3: one HospitalAdmit,
f4: one Ambulance,
f5: one Documents,
f6: one Discharge,
f7: one Billing,
f8: one Treatment,
f9: one Pharmacy,
f10: lone Pharmacy_f,
f11: lone Pharmacy_m,
f12: lone Pharmacy_s,
f13: one Doctor,
f14: lone Doctor_f,
f15: lone Doctor_m,
f16: lone Doctor_s,
f17: lone Testing,
f18: lone Testing_f,
f19: lone Testing_m,
f20: lone Testing_s,
f21: one AdmitRoom,
f22: lone Ambulance_f,
f23: lone Ambulance_m,
f24: lone Ambulance_s,
f25: one HealthRecords,
f26: one InsuranceCompany,
f27: lone Catering,
f28: lone Catering_f,
f29: lone HealthRecords_f,
f30: lone InsuranceCompany_f,
f31: lone InsuranceCompany_m,
f32: lone InsuranceCompany_s,
f33: lone HealthRecords_m,
f34: lone HealthRecords_s,
f35: lone SpecialRoom,
f36: lone Ward,
f37: lone SpecialRoom_s,
f38: lone SpecialRoom_m,
f39: lone SpecialRoom_f,
f40: lone Ward_s,
f41: lone Ward_m,
f42: lone Ward_f,
f43: lone Catering_m,
f44: lone Catering_s
}
sig HealthEmergencySystem {}
sig Transport {}
sig HospitalAdmit {}
sig Ambulance {}
sig Documents {}
sig Discharge {}
sig Billing {}
sig Treatment {}
sig Pharmacy {}
sig Pharmacy_f {}
sig Pharmacy_m {}
sig Pharmacy_s {}
sig Doctor {}
sig Doctor_f {}
sig Doctor_m {}
sig Doctor_s {}
sig Testing {}
sig Testing_f {}
sig Testing_m {}
sig Testing_s {}
sig AdmitRoom {}
sig Ambulance_f {}
sig Ambulance_m {}
sig Ambulance_s {}
sig HealthRecords {}
sig InsuranceCompany {}
sig Catering {}
sig Catering_f {}
sig HealthRecords_f {}
sig InsuranceCompany_f {}
sig InsuranceCompany_m {}
sig InsuranceCompany_s {}
sig HealthRecords_m {}
sig HealthRecords_s {}
sig SpecialRoom {}
sig Ward {}
sig SpecialRoom_s {}
sig SpecialRoom_m {}
sig SpecialRoom_f {}
sig Ward_s {}
sig Ward_m {}
sig Ward_f {}
sig Catering_m {}
sig Catering_s {}

fact Configuration_container
{
	all c : Configuration | c in ProductConfigurations.configurations
}

//Constraints on FD

fact Invariant1
{
	all c:Configuration | #c.f4==1 implies ( ( #c.f22+  #c.f23 +  #c.f24 )=1)
}   


fact Invariant2
{
	all c:Configuration | #c.f25==1 implies ( ( #c.f29+  #c.f33 +  #c.f34 )=1)
}   



fact Invariant3
{
	all c:Configuration | #c.f26==1 implies ( ( #c.f30+  #c.f31 +  #c.f32 )=1)
}   



fact Invariant4
{
	all c:Configuration | #c.f21==1 implies ( ( #c.f35+  #c.f36)=1)
}   



fact Invariant5
{
	all c:Configuration | #c.f35==1 implies ( ( #c.f37+  #c.f38 +  #c.f39 )=1)
}   


fact Invariant6
{
	all c:Configuration | #c.f36==1 implies ( ( #c.f40+  #c.f41 +  #c.f42 )=1)
}   

fact Invariant7
{
	all c:Configuration | #c.f27==1 implies ( ( #c.f28+  #c.f43 +  #c.f44 )=1)
}   


fact Invariant8
{
	all c:Configuration | #c.f17==1 implies ( ( #c.f18+  #c.f19 +  #c.f20 )=1)
}   

fact Invariant9
{
	all c:Configuration | #c.f13==1 implies ( ( #c.f14+  #c.f15 +  #c.f16 )=1)
}   

fact Invariant10
{
	all c:Configuration | #c.f9==1 implies ( ( #c.f10+  #c.f11 +  #c.f12 )=1)
}   

fact Invariant11
{
	all c:Configuration | (#c.f44==1 or #c.f43==1 or #c.f28==1) implies #c.f27=1
}   

fact Invariant12
{
	all c:Configuration | (#c.f18==1 or #c.f19==1 or #c.f20==1) implies #c.f17=1
}   






pred empty{ #Configuration=7}


run empty for 20




