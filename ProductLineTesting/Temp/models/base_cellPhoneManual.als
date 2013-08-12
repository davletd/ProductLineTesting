module CellPhone


one sig ProductConfigurations
{	
	configurations : set Configuration
}


sig Configuration
{
f1: one CellPhone,
f2: one BasicFunctions,
f3: lone Communication,
f4: one VoiceCall,
f5: one SMS,
f6: lone MP3,
f7: lone MMS,
f8: lone WLAN,
f9: lone Bluetooth,
f10: lone UMTS,
f11: one Extras,
f12: lone Camera,
f13: lone ThreeMP,
f14: lone EightMP,
f15: one Message
}


sig CellPhone{}
sig BasicFunctions {}
sig Communication {}
sig VoiceCall {}
sig SMS {}
sig MMS {}
sig WLAN {}
sig Bluetooth {}
sig UMTS {}
sig Extras {}
sig Camera {}
sig ThreeMP{}
sig EightMP {}
sig MP3{}
sig Message{}

fact Configuration_container
{
	all c : Configuration | c in ProductConfigurations.configurations
}

//MMS requires Camera
fact CellPhoneInvariant_operator1
{
all c:Configuration | #c.f7=1 implies #c.f12 =1
}

//Bluetooth excludes MP3
fact CellPhoneInvariant_operator2
{
all c:Configuration | (#c.f9+#c.f6 =1)
}


//ThreeMP requires Camera
fact CellPhoneInvariant_operator3
{
all c:Configuration | (#c.f13=1  implies #c.f12=1)
}

// EightMP requires Camera
fact CellPhoneInvariant_operator4
{
all c:Configuration | (#c.f14=1 implies #c.f12=1)
}

//WLAN , Bluetooth, UMTS require Communication
fact CellPhoneInvariant_operator5
{
all c:Configuration | (#c.f8=1  implies #c.f3=1) and (#c.f9=1 implies #c.f3=1) and (#c.f10=1 implies #c.f3=1)
}


//ThreeMP xor EightMP
fact CellPhoneInvariant_operator6
{
all c:Configuration |(#c.f12=1 implies #c.f13+#c.f14 =1)
}


//MP3 or Camera

fact CellPhoneInvariant_operator7
{
	all c:Configuration | #c.f11=1 implies ( ( #c.f12 +  #c.f3 +0)<=2 and (#c.f12+c.f3+0)>=1)
}   
