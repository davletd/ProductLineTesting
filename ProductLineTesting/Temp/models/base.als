
module CellPhoneModel

one sig ProductConfigurations
{	
	configurations : set Configuration
}

sig Configuration
{
f1: one SMS,
f2: lone MMS,
f3: one VoiceCall,
f4: lone WLAN,
f5: lone Bluetooth,
f6: lone UMTS,
f7: lone MP3,
f8: lone ThreeMP,
f9: lone EightMP,
f10: one BasicFunctions,
f11: one Message,
f12: lone Communication,
f13: one Extras,
f14: lone Camera,
f15: one CellPhone,
}

sig SMS{}
sig MMS{}
sig VoiceCall{}
sig WLAN{}
sig Bluetooth{}
sig UMTS{}
sig MP3{}
sig ThreeMP{}
sig EightMP{}
sig BasicFunctions{}
sig Message{}
sig Communication{}
sig Extras{}
sig Camera{}
sig CellPhone{}

fact Configuration_cardinality
{}

fact Configuration_container
{
	all c : Configuration | c in ProductConfigurations.configurations
}

//Constraints due to require and exclude

// Constraints due to the Operators
// MMS Optional condition   
fact Invariant_Opreator_1
{
	all c:Configuration | #c.f2==1 implies ( #c.f11=1)
}   
// WLAN Optional condition   
fact Invariant_Opreator_2
{
	all c:Configuration | #c.f4==1 implies ( #c.f12=1)
}   
// Bluetooth Optional condition   
fact Invariant_Opreator_3
{
	all c:Configuration | #c.f5==1 implies ( #c.f12=1)
}   
// UMTS Optional condition   
fact Invariant_Opreator_4
{
	all c:Configuration | #c.f6==1 implies ( #c.f12=1)
}   
// MP3 Optional condition   
fact Invariant_Opreator_5
{
	all c:Configuration | #c.f7==1 implies ( #c.f13=1)
}   
// BasicFunctions And Operator =>  Message AND  VoiceCall AND   
fact Invariant_Opreator_6
{
	all c:Configuration | #c.f10==1 implies ( #c.f11=1 and  #c.f3=1)
}   
// Message And Operator =>  SMS AND   
fact Invariant_Opreator_7
{
	all c:Configuration | #c.f11==1 implies ( #c.f1=1)
}   
// Communication Optional condition   
fact Invariant_Opreator_8
{
	all c:Configuration | #c.f12==1 implies ( #c.f15=1)
}   
// Communication And Operator =>   
fact Invariant_Opreator_9
{
}   
// Extras OR Operator =>  MP3 OR  Camera OR   
fact Invariant_Operator_10
{
	all c:Configuration | #c.f13==1 implies ( ( #c.f7 +  #c.f14 +  0)>=1 and ( #c.f7 +  #c.f14 +  0) <=2)
}   
// Camera Optional condition   
fact Invariant_Opreator_11
{
	all c:Configuration | #c.f14==1 implies ( #c.f13=1)
}   
// Camera XOR Operator =>  ThreeMP XOR  EightMP XOR   
fact Invariant_Opreator_12
{
	all c:Configuration | #c.f14==1 implies ( ( #c.f8 +  #c.f9 +  0)==1)
}   
// CellPhone And Operator =>  BasicFunctions AND  Extras AND   
fact Invariant_Opreator_13
{
	all c:Configuration | #c.f15==1 implies ( #c.f10=1 and  #c.f13=1)
}   

/*
fact AllConstraints
{

	pred_1 and  
	pred_2 and  
	pred_3 and  
	pred_4 and  
	pred_5 and  
	pred_6 and  
	pred_7 and  
	pred_8 and  
	pred_9 and  
	pred_10 and  
	pred_11 and  
	pred_12 and  
	pred_13

}
*/

