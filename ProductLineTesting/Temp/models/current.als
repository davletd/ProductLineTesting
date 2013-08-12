
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

pred Tuple1 { some c: Configuration |#c.f1= 1 and #c.f2= 1  } 

pred Tuple2 { some c: Configuration |#c.f1= 1 and #c.f2= 0  } 

pred Tuple3 { some c: Configuration |#c.f1= 1 and #c.f3= 1  } 

pred Tuple5 { some c: Configuration |#c.f1= 1 and #c.f4= 1  } 

pred Tuple6 { some c: Configuration |#c.f1= 1 and #c.f4= 0  } 

pred Tuple7 { some c: Configuration |#c.f1= 1 and #c.f5= 1  } 

pred Tuple8 { some c: Configuration |#c.f1= 1 and #c.f5= 0  } 

pred Tuple9 { some c: Configuration |#c.f1= 1 and #c.f6= 1  } 

pred Tuple10 { some c: Configuration |#c.f1= 1 and #c.f6= 0  } 

pred Tuple11 { some c: Configuration |#c.f1= 1 and #c.f7= 1  } 

pred Tuple12 { some c: Configuration |#c.f1= 1 and #c.f7= 0  } 

pred Tuple13 { some c: Configuration |#c.f1= 1 and #c.f8= 1  } 

pred Tuple14 { some c: Configuration |#c.f1= 1 and #c.f8= 0  } 

pred Tuple15 { some c: Configuration |#c.f1= 1 and #c.f9= 1  } 

pred Tuple16 { some c: Configuration |#c.f1= 1 and #c.f9= 0  } 

pred Tuple17 { some c: Configuration |#c.f1= 1 and #c.f10= 1  } 

pred Tuple19 { some c: Configuration |#c.f1= 1 and #c.f11= 1  } 

pred Tuple21 { some c: Configuration |#c.f1= 1 and #c.f12= 1  } 

pred Tuple22 { some c: Configuration |#c.f1= 1 and #c.f12= 0  } 

pred Tuple23 { some c: Configuration |#c.f1= 1 and #c.f13= 1  } 

pred Tuple25 { some c: Configuration |#c.f1= 1 and #c.f14= 1  } 

pred Tuple26 { some c: Configuration |#c.f1= 1 and #c.f14= 0  } 

pred Tuple27 { some c: Configuration |#c.f1= 1 and #c.f15= 1  } 

pred Tuple57 { some c: Configuration |#c.f2= 1 and #c.f3= 1  } 

pred Tuple59 { some c: Configuration |#c.f2= 1 and #c.f4= 1  } 

pred Tuple60 { some c: Configuration |#c.f2= 1 and #c.f4= 0  } 

pred Tuple61 { some c: Configuration |#c.f2= 1 and #c.f5= 1  } 

pred Tuple62 { some c: Configuration |#c.f2= 1 and #c.f5= 0  } 

pred Tuple63 { some c: Configuration |#c.f2= 1 and #c.f6= 1  } 

pred Tuple64 { some c: Configuration |#c.f2= 1 and #c.f6= 0  } 

pred Tuple65 { some c: Configuration |#c.f2= 1 and #c.f7= 1  } 

pred Tuple66 { some c: Configuration |#c.f2= 1 and #c.f7= 0  } 

pred Tuple67 { some c: Configuration |#c.f2= 1 and #c.f8= 1  } 

pred Tuple68 { some c: Configuration |#c.f2= 1 and #c.f8= 0  } 

pred Tuple69 { some c: Configuration |#c.f2= 1 and #c.f9= 1  } 

pred Tuple70 { some c: Configuration |#c.f2= 1 and #c.f9= 0  } 

pred Tuple71 { some c: Configuration |#c.f2= 1 and #c.f10= 1  } 

pred Tuple73 { some c: Configuration |#c.f2= 1 and #c.f11= 1  } 

pred Tuple75 { some c: Configuration |#c.f2= 1 and #c.f12= 1  } 

pred Tuple76 { some c: Configuration |#c.f2= 1 and #c.f12= 0  } 

pred Tuple77 { some c: Configuration |#c.f2= 1 and #c.f13= 1  } 

pred Tuple79 { some c: Configuration |#c.f2= 1 and #c.f14= 1  } 

pred Tuple80 { some c: Configuration |#c.f2= 1 and #c.f14= 0  } 

pred Tuple81 { some c: Configuration |#c.f2= 1 and #c.f15= 1  } 

pred Tuple83 { some c: Configuration |#c.f2= 0 and #c.f3= 1  } 

pred Tuple85 { some c: Configuration |#c.f2= 0 and #c.f4= 1  } 

pred Tuple86 { some c: Configuration |#c.f2= 0 and #c.f4= 0  } 

pred Tuple87 { some c: Configuration |#c.f2= 0 and #c.f5= 1  } 

pred Tuple88 { some c: Configuration |#c.f2= 0 and #c.f5= 0  } 

pred Tuple89 { some c: Configuration |#c.f2= 0 and #c.f6= 1  } 

pred Tuple90 { some c: Configuration |#c.f2= 0 and #c.f6= 0  } 

pred Tuple91 { some c: Configuration |#c.f2= 0 and #c.f7= 1  } 

pred Tuple92 { some c: Configuration |#c.f2= 0 and #c.f7= 0  } 

pred Tuple93 { some c: Configuration |#c.f2= 0 and #c.f8= 1  } 

pred Tuple94 { some c: Configuration |#c.f2= 0 and #c.f8= 0  } 

pred Tuple95 { some c: Configuration |#c.f2= 0 and #c.f9= 1  } 

pred Tuple96 { some c: Configuration |#c.f2= 0 and #c.f9= 0  } 

pred Tuple97 { some c: Configuration |#c.f2= 0 and #c.f10= 1  } 

pred Tuple99 { some c: Configuration |#c.f2= 0 and #c.f11= 1  } 

pred Tuple101 { some c: Configuration |#c.f2= 0 and #c.f12= 1  } 

pred Tuple102 { some c: Configuration |#c.f2= 0 and #c.f12= 0  } 

pred Tuple103 { some c: Configuration |#c.f2= 0 and #c.f13= 1  } 

pred Tuple105 { some c: Configuration |#c.f2= 0 and #c.f14= 1  } 

pred Tuple106 { some c: Configuration |#c.f2= 0 and #c.f14= 0  } 

pred Tuple107 { some c: Configuration |#c.f2= 0 and #c.f15= 1  } 

pred Tuple109 { some c: Configuration |#c.f3= 1 and #c.f4= 1  } 

pred Tuple110 { some c: Configuration |#c.f3= 1 and #c.f4= 0  } 

pred Tuple111 { some c: Configuration |#c.f3= 1 and #c.f5= 1  } 

pred Tuple112 { some c: Configuration |#c.f3= 1 and #c.f5= 0  } 

pred Tuple113 { some c: Configuration |#c.f3= 1 and #c.f6= 1  } 

pred Tuple114 { some c: Configuration |#c.f3= 1 and #c.f6= 0  } 

pred Tuple115 { some c: Configuration |#c.f3= 1 and #c.f7= 1  } 

pred Tuple116 { some c: Configuration |#c.f3= 1 and #c.f7= 0  } 

pred Tuple117 { some c: Configuration |#c.f3= 1 and #c.f8= 1  } 

pred Tuple118 { some c: Configuration |#c.f3= 1 and #c.f8= 0  } 

pred Tuple119 { some c: Configuration |#c.f3= 1 and #c.f9= 1  } 

pred Tuple120 { some c: Configuration |#c.f3= 1 and #c.f9= 0  } 

pred Tuple121 { some c: Configuration |#c.f3= 1 and #c.f10= 1  } 

pred Tuple123 { some c: Configuration |#c.f3= 1 and #c.f11= 1  } 

pred Tuple125 { some c: Configuration |#c.f3= 1 and #c.f12= 1  } 

pred Tuple126 { some c: Configuration |#c.f3= 1 and #c.f12= 0  } 

pred Tuple127 { some c: Configuration |#c.f3= 1 and #c.f13= 1  } 

pred Tuple129 { some c: Configuration |#c.f3= 1 and #c.f14= 1  } 

pred Tuple130 { some c: Configuration |#c.f3= 1 and #c.f14= 0  } 

pred Tuple131 { some c: Configuration |#c.f3= 1 and #c.f15= 1  } 

pred Tuple157 { some c: Configuration |#c.f4= 1 and #c.f5= 1  } 

pred Tuple158 { some c: Configuration |#c.f4= 1 and #c.f5= 0  } 

pred Tuple159 { some c: Configuration |#c.f4= 1 and #c.f6= 1  } 

pred Tuple160 { some c: Configuration |#c.f4= 1 and #c.f6= 0  } 

pred Tuple161 { some c: Configuration |#c.f4= 1 and #c.f7= 1  } 

pred Tuple162 { some c: Configuration |#c.f4= 1 and #c.f7= 0  } 

pred Tuple163 { some c: Configuration |#c.f4= 1 and #c.f8= 1  } 

pred Tuple164 { some c: Configuration |#c.f4= 1 and #c.f8= 0  } 

pred Tuple165 { some c: Configuration |#c.f4= 1 and #c.f9= 1  } 

pred Tuple166 { some c: Configuration |#c.f4= 1 and #c.f9= 0  } 

pred Tuple167 { some c: Configuration |#c.f4= 1 and #c.f10= 1  } 

pred Tuple169 { some c: Configuration |#c.f4= 1 and #c.f11= 1  } 

pred Tuple171 { some c: Configuration |#c.f4= 1 and #c.f12= 1  } 

pred Tuple173 { some c: Configuration |#c.f4= 1 and #c.f13= 1  } 

pred Tuple175 { some c: Configuration |#c.f4= 1 and #c.f14= 1  } 

pred Tuple176 { some c: Configuration |#c.f4= 1 and #c.f14= 0  } 

pred Tuple177 { some c: Configuration |#c.f4= 1 and #c.f15= 1  } 

pred Tuple179 { some c: Configuration |#c.f4= 0 and #c.f5= 1  } 

pred Tuple180 { some c: Configuration |#c.f4= 0 and #c.f5= 0  } 

pred Tuple181 { some c: Configuration |#c.f4= 0 and #c.f6= 1  } 

pred Tuple182 { some c: Configuration |#c.f4= 0 and #c.f6= 0  } 

pred Tuple183 { some c: Configuration |#c.f4= 0 and #c.f7= 1  } 

pred Tuple184 { some c: Configuration |#c.f4= 0 and #c.f7= 0  } 

pred Tuple185 { some c: Configuration |#c.f4= 0 and #c.f8= 1  } 

pred Tuple186 { some c: Configuration |#c.f4= 0 and #c.f8= 0  } 

pred Tuple187 { some c: Configuration |#c.f4= 0 and #c.f9= 1  } 

pred Tuple188 { some c: Configuration |#c.f4= 0 and #c.f9= 0  } 

pred Tuple189 { some c: Configuration |#c.f4= 0 and #c.f10= 1  } 

pred Tuple191 { some c: Configuration |#c.f4= 0 and #c.f11= 1  } 

pred Tuple193 { some c: Configuration |#c.f4= 0 and #c.f12= 1  } 

pred Tuple194 { some c: Configuration |#c.f4= 0 and #c.f12= 0  } 

pred Tuple195 { some c: Configuration |#c.f4= 0 and #c.f13= 1  } 

pred Tuple197 { some c: Configuration |#c.f4= 0 and #c.f14= 1  } 

pred Tuple198 { some c: Configuration |#c.f4= 0 and #c.f14= 0  } 

pred Tuple199 { some c: Configuration |#c.f4= 0 and #c.f15= 1  } 

pred Tuple201 { some c: Configuration |#c.f5= 1 and #c.f6= 1  } 

pred Tuple202 { some c: Configuration |#c.f5= 1 and #c.f6= 0  } 

pred Tuple203 { some c: Configuration |#c.f5= 1 and #c.f7= 1  } 

pred Tuple204 { some c: Configuration |#c.f5= 1 and #c.f7= 0  } 

pred Tuple205 { some c: Configuration |#c.f5= 1 and #c.f8= 1  } 

pred Tuple206 { some c: Configuration |#c.f5= 1 and #c.f8= 0  } 

pred Tuple207 { some c: Configuration |#c.f5= 1 and #c.f9= 1  } 

pred Tuple208 { some c: Configuration |#c.f5= 1 and #c.f9= 0  } 

pred Tuple209 { some c: Configuration |#c.f5= 1 and #c.f10= 1  } 

pred Tuple211 { some c: Configuration |#c.f5= 1 and #c.f11= 1  } 

pred Tuple213 { some c: Configuration |#c.f5= 1 and #c.f12= 1  } 

pred Tuple215 { some c: Configuration |#c.f5= 1 and #c.f13= 1  } 

pred Tuple217 { some c: Configuration |#c.f5= 1 and #c.f14= 1  } 

pred Tuple218 { some c: Configuration |#c.f5= 1 and #c.f14= 0  } 

pred Tuple219 { some c: Configuration |#c.f5= 1 and #c.f15= 1  } 

pred Tuple221 { some c: Configuration |#c.f5= 0 and #c.f6= 1  } 

pred Tuple222 { some c: Configuration |#c.f5= 0 and #c.f6= 0  } 

pred Tuple223 { some c: Configuration |#c.f5= 0 and #c.f7= 1  } 

pred Tuple224 { some c: Configuration |#c.f5= 0 and #c.f7= 0  } 

pred Tuple225 { some c: Configuration |#c.f5= 0 and #c.f8= 1  } 

pred Tuple226 { some c: Configuration |#c.f5= 0 and #c.f8= 0  } 

pred Tuple227 { some c: Configuration |#c.f5= 0 and #c.f9= 1  } 

pred Tuple228 { some c: Configuration |#c.f5= 0 and #c.f9= 0  } 

pred Tuple229 { some c: Configuration |#c.f5= 0 and #c.f10= 1  } 

pred Tuple231 { some c: Configuration |#c.f5= 0 and #c.f11= 1  } 

pred Tuple233 { some c: Configuration |#c.f5= 0 and #c.f12= 1  } 

pred Tuple234 { some c: Configuration |#c.f5= 0 and #c.f12= 0  } 

pred Tuple235 { some c: Configuration |#c.f5= 0 and #c.f13= 1  } 

pred Tuple237 { some c: Configuration |#c.f5= 0 and #c.f14= 1  } 

pred Tuple238 { some c: Configuration |#c.f5= 0 and #c.f14= 0  } 

pred Tuple239 { some c: Configuration |#c.f5= 0 and #c.f15= 1  } 

pred Tuple241 { some c: Configuration |#c.f6= 1 and #c.f7= 1  } 

pred Tuple242 { some c: Configuration |#c.f6= 1 and #c.f7= 0  } 

pred Tuple243 { some c: Configuration |#c.f6= 1 and #c.f8= 1  } 

pred Tuple244 { some c: Configuration |#c.f6= 1 and #c.f8= 0  } 

pred Tuple245 { some c: Configuration |#c.f6= 1 and #c.f9= 1  } 

pred Tuple246 { some c: Configuration |#c.f6= 1 and #c.f9= 0  } 

pred Tuple247 { some c: Configuration |#c.f6= 1 and #c.f10= 1  } 

pred Tuple249 { some c: Configuration |#c.f6= 1 and #c.f11= 1  } 

pred Tuple251 { some c: Configuration |#c.f6= 1 and #c.f12= 1  } 

pred Tuple253 { some c: Configuration |#c.f6= 1 and #c.f13= 1  } 

pred Tuple255 { some c: Configuration |#c.f6= 1 and #c.f14= 1  } 

pred Tuple256 { some c: Configuration |#c.f6= 1 and #c.f14= 0  } 

pred Tuple257 { some c: Configuration |#c.f6= 1 and #c.f15= 1  } 

pred Tuple259 { some c: Configuration |#c.f6= 0 and #c.f7= 1  } 

pred Tuple260 { some c: Configuration |#c.f6= 0 and #c.f7= 0  } 

pred Tuple261 { some c: Configuration |#c.f6= 0 and #c.f8= 1  } 

pred Tuple262 { some c: Configuration |#c.f6= 0 and #c.f8= 0  } 

pred Tuple263 { some c: Configuration |#c.f6= 0 and #c.f9= 1  } 

pred Tuple264 { some c: Configuration |#c.f6= 0 and #c.f9= 0  } 

pred Tuple265 { some c: Configuration |#c.f6= 0 and #c.f10= 1  } 

pred Tuple267 { some c: Configuration |#c.f6= 0 and #c.f11= 1  } 

pred Tuple269 { some c: Configuration |#c.f6= 0 and #c.f12= 1  } 

pred Tuple270 { some c: Configuration |#c.f6= 0 and #c.f12= 0  } 

pred Tuple271 { some c: Configuration |#c.f6= 0 and #c.f13= 1  } 

pred Tuple273 { some c: Configuration |#c.f6= 0 and #c.f14= 1  } 

pred Tuple274 { some c: Configuration |#c.f6= 0 and #c.f14= 0  } 

pred Tuple275 { some c: Configuration |#c.f6= 0 and #c.f15= 1  } 

pred Tuple277 { some c: Configuration |#c.f7= 1 and #c.f8= 1  } 

pred Tuple278 { some c: Configuration |#c.f7= 1 and #c.f8= 0  } 

pred Tuple279 { some c: Configuration |#c.f7= 1 and #c.f9= 1  } 

pred Tuple280 { some c: Configuration |#c.f7= 1 and #c.f9= 0  } 

pred Tuple281 { some c: Configuration |#c.f7= 1 and #c.f10= 1  } 

pred Tuple283 { some c: Configuration |#c.f7= 1 and #c.f11= 1  } 

pred Tuple285 { some c: Configuration |#c.f7= 1 and #c.f12= 1  } 

pred Tuple286 { some c: Configuration |#c.f7= 1 and #c.f12= 0  } 

pred Tuple287 { some c: Configuration |#c.f7= 1 and #c.f13= 1  } 

pred Tuple289 { some c: Configuration |#c.f7= 1 and #c.f14= 1  } 

pred Tuple290 { some c: Configuration |#c.f7= 1 and #c.f14= 0  } 

pred Tuple291 { some c: Configuration |#c.f7= 1 and #c.f15= 1  } 

pred Tuple293 { some c: Configuration |#c.f7= 0 and #c.f8= 1  } 

pred Tuple294 { some c: Configuration |#c.f7= 0 and #c.f8= 0  } 

pred Tuple295 { some c: Configuration |#c.f7= 0 and #c.f9= 1  } 

pred Tuple296 { some c: Configuration |#c.f7= 0 and #c.f9= 0  } 

pred Tuple297 { some c: Configuration |#c.f7= 0 and #c.f10= 1  } 

pred Tuple299 { some c: Configuration |#c.f7= 0 and #c.f11= 1  } 

pred Tuple301 { some c: Configuration |#c.f7= 0 and #c.f12= 1  } 

pred Tuple302 { some c: Configuration |#c.f7= 0 and #c.f12= 0  } 

pred Tuple303 { some c: Configuration |#c.f7= 0 and #c.f13= 1  } 

pred Tuple305 { some c: Configuration |#c.f7= 0 and #c.f14= 1  } 

pred Tuple307 { some c: Configuration |#c.f7= 0 and #c.f15= 1  } 

pred Tuple309 { some c: Configuration |#c.f8= 1 and #c.f9= 1  } 

pred Tuple310 { some c: Configuration |#c.f8= 1 and #c.f9= 0  } 

pred Tuple311 { some c: Configuration |#c.f8= 1 and #c.f10= 1  } 

pred Tuple313 { some c: Configuration |#c.f8= 1 and #c.f11= 1  } 

pred Tuple315 { some c: Configuration |#c.f8= 1 and #c.f12= 1  } 

pred Tuple316 { some c: Configuration |#c.f8= 1 and #c.f12= 0  } 

pred Tuple317 { some c: Configuration |#c.f8= 1 and #c.f13= 1  } 

pred Tuple319 { some c: Configuration |#c.f8= 1 and #c.f14= 1  } 

pred Tuple320 { some c: Configuration |#c.f8= 1 and #c.f14= 0  } 

pred Tuple321 { some c: Configuration |#c.f8= 1 and #c.f15= 1  } 

pred Tuple323 { some c: Configuration |#c.f8= 0 and #c.f9= 1  } 

pred Tuple324 { some c: Configuration |#c.f8= 0 and #c.f9= 0  } 

pred Tuple325 { some c: Configuration |#c.f8= 0 and #c.f10= 1  } 

pred Tuple327 { some c: Configuration |#c.f8= 0 and #c.f11= 1  } 

pred Tuple329 { some c: Configuration |#c.f8= 0 and #c.f12= 1  } 

pred Tuple330 { some c: Configuration |#c.f8= 0 and #c.f12= 0  } 

pred Tuple331 { some c: Configuration |#c.f8= 0 and #c.f13= 1  } 

pred Tuple333 { some c: Configuration |#c.f8= 0 and #c.f14= 1  } 

pred Tuple334 { some c: Configuration |#c.f8= 0 and #c.f14= 0  } 

pred Tuple335 { some c: Configuration |#c.f8= 0 and #c.f15= 1  } 

pred Tuple337 { some c: Configuration |#c.f9= 1 and #c.f10= 1  } 

pred Tuple339 { some c: Configuration |#c.f9= 1 and #c.f11= 1  } 

pred Tuple341 { some c: Configuration |#c.f9= 1 and #c.f12= 1  } 

pred Tuple342 { some c: Configuration |#c.f9= 1 and #c.f12= 0  } 

pred Tuple343 { some c: Configuration |#c.f9= 1 and #c.f13= 1  } 

pred Tuple345 { some c: Configuration |#c.f9= 1 and #c.f14= 1  } 

pred Tuple346 { some c: Configuration |#c.f9= 1 and #c.f14= 0  } 

pred Tuple347 { some c: Configuration |#c.f9= 1 and #c.f15= 1  } 

pred Tuple349 { some c: Configuration |#c.f9= 0 and #c.f10= 1  } 

pred Tuple351 { some c: Configuration |#c.f9= 0 and #c.f11= 1  } 

pred Tuple353 { some c: Configuration |#c.f9= 0 and #c.f12= 1  } 

pred Tuple354 { some c: Configuration |#c.f9= 0 and #c.f12= 0  } 

pred Tuple355 { some c: Configuration |#c.f9= 0 and #c.f13= 1  } 

pred Tuple357 { some c: Configuration |#c.f9= 0 and #c.f14= 1  } 

pred Tuple358 { some c: Configuration |#c.f9= 0 and #c.f14= 0  } 

pred Tuple359 { some c: Configuration |#c.f9= 0 and #c.f15= 1  } 

pred Tuple361 { some c: Configuration |#c.f10= 1 and #c.f11= 1  } 

pred Tuple363 { some c: Configuration |#c.f10= 1 and #c.f12= 1  } 

pred Tuple364 { some c: Configuration |#c.f10= 1 and #c.f12= 0  } 

pred Tuple365 { some c: Configuration |#c.f10= 1 and #c.f13= 1  } 

pred Tuple367 { some c: Configuration |#c.f10= 1 and #c.f14= 1  } 

pred Tuple368 { some c: Configuration |#c.f10= 1 and #c.f14= 0  } 

pred Tuple369 { some c: Configuration |#c.f10= 1 and #c.f15= 1  } 

pred Tuple381 { some c: Configuration |#c.f11= 1 and #c.f12= 1  } 

pred Tuple382 { some c: Configuration |#c.f11= 1 and #c.f12= 0  } 

pred Tuple383 { some c: Configuration |#c.f11= 1 and #c.f13= 1  } 

pred Tuple385 { some c: Configuration |#c.f11= 1 and #c.f14= 1  } 

pred Tuple386 { some c: Configuration |#c.f11= 1 and #c.f14= 0  } 

pred Tuple387 { some c: Configuration |#c.f11= 1 and #c.f15= 1  } 

pred Tuple397 { some c: Configuration |#c.f12= 1 and #c.f13= 1  } 

pred Tuple399 { some c: Configuration |#c.f12= 1 and #c.f14= 1  } 

pred Tuple400 { some c: Configuration |#c.f12= 1 and #c.f14= 0  } 

pred Tuple401 { some c: Configuration |#c.f12= 1 and #c.f15= 1  } 

pred Tuple403 { some c: Configuration |#c.f12= 0 and #c.f13= 1  } 

pred Tuple405 { some c: Configuration |#c.f12= 0 and #c.f14= 1  } 

pred Tuple406 { some c: Configuration |#c.f12= 0 and #c.f14= 0  } 

pred Tuple407 { some c: Configuration |#c.f12= 0 and #c.f15= 1  } 

pred Tuple409 { some c: Configuration |#c.f13= 1 and #c.f14= 1  } 

pred Tuple410 { some c: Configuration |#c.f13= 1 and #c.f14= 0  } 

pred Tuple411 { some c: Configuration |#c.f13= 1 and #c.f15= 1  } 

pred Tuple417 { some c: Configuration |#c.f14= 1 and #c.f15= 1  } 

pred Tuple419 { some c: Configuration |#c.f14= 0 and #c.f15= 1  } 


pred ConjunctionTuple2{Tuple365 and Tuple201 and Tuple354 and Tuple107 and Tuple91 and Tuple114 and Tuple213 and Tuple95 and Tuple65 and Tuple6 and Tuple270 and Tuple3 and Tuple57 and Tuple353 and Tuple317 and Tuple234 and Tuple245 and Tuple246 and Tuple16 and Tuple331 and Tuple253 and Tuple117 and Tuple239 and Tuple226 and Tuple70 and Tuple275 and Tuple130 and Tuple233 and Tuple199 and Tuple294 and Tuple237 and Tuple358 and Tuple162 and Tuple88 and Tuple116 and Tuple279 and Tuple339 and Tuple410 and Tuple198 and Tuple273 and Tuple165 and Tuple105 and Tuple325 and Tuple217 and Tuple206 and Tuple224 and Tuple257 and Tuple251 and Tuple106 and Tuple173 and Tuple80 and Tuple19 and Tuple302 and Tuple243 and Tuple255 and Tuple11 and Tuple177 and Tuple180 and Tuple334 and Tuple102 and Tuple363 and Tuple167 and Tuple193 and Tuple351 and Tuple409 and Tuple320 and Tuple13 and Tuple309 and Tuple303 and Tuple296 and Tuple222 and Tuple244 and Tuple25 and Tuple327 }
 run ConjunctionTuple2 for 8