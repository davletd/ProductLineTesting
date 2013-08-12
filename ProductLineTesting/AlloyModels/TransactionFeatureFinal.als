module TransactionFeatureModel



one sig ProductConfigurations
{	
	configurations : set Configuration
}

all c: Configuration| (#c.f14==1) implies (#c.f9=1 and #c.f15=0) or  #c.f14=1

sig Configuration
{

f1: one Transaction, //Mandatory
f2: lone Nested,  //Optional
f3: one Recovering, //Mandatory
f4: one ConncurrencyControlStrategy, //Mandatory
f5: one PhysicalLogging, //Mandatory 
f6: lone TwoPhaseLocking, //XOR
f7: lone OptimisticValidation, //XOR
f8: lone Checkpointing, //XOR
f9: lone Deferring, //XOR
f10: one OutcomeAware, //Mandatory
f11: lone Checkpointable, 
f12: lone Tracing,
f13: lone Context, 
f14:  lone Copyable,
f15: lone Traceable,
f16: one Shared,
f17: lone SemanticClassified,
f18: one AccessClassified,
f19: one Lockable
}



sig Transaction {}
sig  Nested {}
sig  Recovering {}
sig  ConncurrencyControlStrategy {}
sig PhysicalLogging {}
sig TwoPhaseLocking  {}
sig  OptimisticValidation {}
sig  Checkpointing {}
sig  Deferring {}
sig  OutcomeAware {}
sig  Checkpointable {}
sig  Tracing {}
sig  Context {}
sig  Copyable {}
sig  Traceable {}
sig  Shared {}
sig  SemanticClassified {}
sig  AccessClassified {}
sig  Lockable {}



fact Configuration_container
{

all c : Configuration | c in ProductConfigurations.configurations
}

//Manual Inserted Constraints

//Compostion Rule 1: TwoPhaseLocking excudes "Recovering.Deferring"

fact compositionRule1
{
	all c: Configuration| #c.f6==1 implies (#c.f3==1 implies #c.f9==0)
}

//Composition Rule 2: OptimisticValidation required Recovering.Deferring"
fact compositionRule2
{

	all c:Configuration | #c.f7==1 implies (#c.f3=1 and #c.f9=1)
}
//Composition Rule 3: Deferreing.Traceable requires Traceable.SemanticClassified

fact compositionRule3
{
	all c:Configuration| (#c.f9==1 and #c.f15==1) implies (#c.f15=1 and #c.f17=1)
}

//Two Phase Locking XOR Optimistic Validation Constraint 1
pred TwoPhaseLocking_constraint
{
all c: Configuration | #c.f6==1 implies (#c.f4=1 and #c.f7=0)
}


//Two Phase Locking XOR Optimistic Validation Constraint 2
pred OptimisticValidation_constraint
{
all c: Configuration | #c.f7==1 implies (#c.f4=1 and #c.f6=0)
}

//Checkpointing XOR Deferring Constraint 1 
pred Checkpointing_constraint
{
all c: Configuration | #c.f8==1 implies (#c.f5=1 and #c.f7=0)
}

//Checkpointing XOR Deferring Constraint 2
pred Deferring_constraint
{
all c: Configuration | #c.f7==1 implies (#c.f5=1 and #c.f8=0)
}

//Checkpointable constraint

pred Checkpointable_constraint
{
all c: Configuration | #c.f8==1 implies #c.f11=1
}

//Tracing constraint

pred Tracing_constraint
{
all c: Configuration | (#c.f8==1 or #c.f6==1 )implies #c.f12=1
}

//Context constraint
pred Context_constraint
{
all c: Configuration | (#c.f8==1 or #c.f10==1 or #c.f2==1 or #c.f12==1 )implies #c.f13=1
}




//Copyable XOR constraint 1
pred Copyable_xor_constraint1
{
all c: Configuration| (#c.f14==1) implies (#c.f9=1 and #c.f15=0) or  #c.f14=1
}

// Traceable XOR constraint 2
pred Traceable_xor_constraint2
{
all c: Configuration| (#c.f15==1) implies (#c.f9=1 and #c.f14=0) or #c.f15=1
}


//SematicClassified constraint
pred SemanticClassified_constraint
{

all c: Configuration | (#c.f15==1 or #c.f9==1) implies (#c.f15=1 or #c.f15=0)
}
//Access Classified constraint
pred AccessClassified_constraint
{
all c: Configuration | (#c.f15==1 or #c.f6==1 or #c.f16==1) implies #c.f18=1
}

//Lockable constraint
pred Lockable_constraint
{
all c: Configuration | (#c.f16==1 or #c.f6==1) implies #c.f19=1
}




pred AllConstraints
{

TwoPhaseLocking_constraint 
and  OptimisticValidation_constraint 
and Checkpointing_constraint 
and Deferring_constraint 
and Checkpointable_constraint 
and Tracing_constraint 
and Context_constraint 
and Copyable_xor_constraint1 

and Traceable_xor_constraint2 
and SemanticClassified_constraint 
and AccessClassified_constraint 
and Lockable_constraint
}

pred atleastOneFeatureInConfigs
{
AllConstraints and

some c:Configuration | #c.f1=1 and
some c:Configuration | #c.f2=1 and
some c:Configuration | #c.f3=1 and
some c:Configuration | #c.f4=1 and
some c:Configuration | #c.f5=1 and
some c:Configuration | #c.f6=1 and
some c:Configuration | #c.f7=1 and
some c:Configuration | #c.f8=1 and
some c:Configuration | #c.f9=1 and
some c:Configuration | #c.f10=1 and
some c:Configuration | #c.f11=1 and
some c:Configuration | #c.f12=1 and
some c:Configuration | #c.f13=1 and
some c:Configuration | #c.f14=1 and
some c:Configuration | #c.f15=1 and
some c:Configuration | #c.f16=1 and
some c:Configuration | #c.f17=1 and
some c:Configuration | #c.f18=1 and
some c:Configuration | #c.f19=1 
}


pred allDFTBranchesInAllConfigs
{
AllConstraints and
some c1: Configuration, c2:Configuration, c3:Configuration, c4:Configuration, c5:Configuration, c6:Configuration
,c7: Configuration,c8: Configuration ,c9: Configuration ,c10: Configuration ,c11: Configuration ,c12: Configuration ,c13: Configuration 
,c14: Configuration ,c15: Configuration ,c16: Configuration   |

#c1.f1=1 and #c1.f2=1 and #c1.f13=1 and

#c2.f1=1 and #c2.f3=1 and #c2.f10=1 and #c2.f13=1 and 

#c3.f1=1 and #c3.f3=1 and #c3.f5=1 and#c3.f8=1 and #c3.f13=1 and

#c4.f1 = 1 and #c4.f3=1 and #c4.f5=1 and #c4.f8=1 and #c4.f11=1 and #c4.f14=1 and

#c5.f1 = 1 and #c5.f3=1 and #c5.f5=1 and #c5.f8=1 and #c5.f12=1 and #c5.f13=1 and

#c6.f1 = 1 and #c6.f3=1 and #c6.f5=1 and #c6.f8=1 and #c6.f12=1 and #c6.f15=1 and #c6.f17=1 and

#c7.f1 = 1 and #c7.f3=1 and #c7.f5=1 and #c7.f8=1 and #c7.f12=1 and #c7.f15=1 and #c7.f18=1 and

#c8.f1 = 1 and #c8.f3=1 and #c8.f5=1 and #c8.f9=1 and #c8.f14=1 and

#c9.f1 = 1 and #c9.f3=1 and #c9.f5=1 and #c9.f9=1 and #c9.f15=1 and  #c9.f17=1 and

#c10.f1 = 1 and #c10.f3=1 and #c10.f5=1 and #c10.f9=1 and #c10.f15=1 and  #c10.f18=1 and

#c11.f1=1 and #c11.f4=1 and #c11.f6=1 and #c11.f12=1 and #c11.f13=1 and

#c12.f1=1 and #c12.f4=1 and #c12.f6=1 and #c12.f12=1 and #c12.f15=1 and #c12.f17=1 and

#c13.f1=1 and #c13.f4=1 and #c13.f6=1 and #c13.f12=1 and #c13.f15=1 and #c13.f18=1 and


#c14.f1=1 and #c14.f4=1 and #c14.f6=1 and #c14.f18=1 and

#c15.f1=1 and #c15.f4=1 and #c15.f6=1 and #c15.f19=1 and

#c16.f1=1 and #c16.f4=1 and #c16.f7=1 
}

pred allDFTBranchesInDiffConfigs
{
AllConstraints and
some c1: Configuration, c2:Configuration, c3:Configuration, c4:Configuration, c5:Configuration, c6:Configuration
,c7: Configuration,c8: Configuration ,c9: Configuration ,c10: Configuration ,c11: Configuration ,c12: Configuration ,c13: Configuration 
,c14: Configuration ,c15: Configuration ,c16: Configuration   |

#c1.f1=1 and #c1.f2=1 and #c1.f13=1 and

#c2.f1=1 and #c2.f3=1 and #c2.f10=1 and #c2.f13=1 and 

#c3.f1=1 and #c3.f3=1 and #c3.f5=1 and#c3.f8=1 and #c3.f13=1 and

#c4.f1 = 1 and #c4.f3=1 and #c4.f5=1 and #c4.f8=1 and #c4.f11=1 and #c4.f14=1 and

#c5.f1 = 1 and #c5.f3=1 and #c5.f5=1 and #c5.f8=1 and #c5.f12=1 and #c5.f13=1 and

#c6.f1 = 1 and #c6.f3=1 and #c6.f5=1 and #c6.f8=1 and #c6.f12=1 and #c6.f15=1 and #c6.f17=1 and

#c7.f1 = 1 and #c7.f3=1 and #c7.f5=1 and #c7.f8=1 and #c7.f12=1 and #c7.f15=1 and #c7.f18=1 and

#c8.f1 = 1 and #c8.f3=1 and #c8.f5=1 and #c8.f9=1 and #c8.f14=1 and

#c9.f1 = 1 and #c9.f3=1 and #c9.f5=1 and #c9.f9=1 and #c9.f15=1 and  #c9.f17=1 and

#c10.f1 = 1 and #c10.f3=1 and #c10.f5=1 and #c10.f9=1 and #c10.f15=1 and  #c10.f18=1 and

#c11.f1=1 and #c11.f4=1 and #c11.f6=1 and #c11.f12=1 and #c11.f13=1 and

#c12.f1=1 and #c12.f4=1 and #c12.f6=1 and #c12.f12=1 and #c12.f15=1 and #c12.f17=1 and

#c13.f1=1 and #c13.f4=1 and #c13.f6=1 and #c13.f12=1 and #c13.f15=1 and #c13.f18=1 and


#c14.f1=1 and #c14.f4=1 and #c14.f6=1 and #c14.f18=1 and

#c15.f1=1 and #c15.f4=1 and #c15.f6=1 and #c15.f19=1 and

#c16.f1=1 and #c16.f4=1 and #c16.f7=1 and

disj[c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16]

}





pred Pair1
{ (some c: Configuration |#c.f1=1 and #c.f2=1) }
pred Pair2
{ (some c: Configuration |#c.f1=1 and #c.f3=1 ) }
pred Pair3
{ (some c: Configuration |#c.f1=1 and #c.f4=1 )}
pred Pair4
{ (some c: Configuration |#c.f1=1 and #c.f5=1) }
pred Pair5
{ (some c: Configuration |#c.f1=1 and #c.f6=1) }
pred Pair6
{ (some c: Configuration |#c.f1=1 and #c.f7=1 ) }
pred Pair7
{ (some c: Configuration |#c.f1=1 and #c.f8=1 ) }
pred Pair8
{ (some c: Configuration |#c.f1=1 and #c.f9=1) }
pred Pair9
{ (some c: Configuration |#c.f1=1 and #c.f10=1) }
pred Pair10
{ (some c: Configuration |#c.f1=1 and #c.f11=1 ) }
pred Pair11
{ (some c: Configuration |#c.f1=1 and #c.f12=1 ) }
pred Pair12
{ (some c: Configuration |#c.f1=1 and #c.f13=1) }
pred Pair13
{ (some c: Configuration |#c.f1=1 and #c.f14=1) }
pred Pair14
{ (some c: Configuration |#c.f1=1 and #c.f15=1 ) }
pred Pair15
{ (some c: Configuration |#c.f1=1 and #c.f16=1 ) }
pred Pair16
{ (some c: Configuration |#c.f1=1 and #c.f17=1) }
pred Pair17
{ (some c: Configuration |#c.f1=1 and #c.f18=1) } 
pred Pair18
{ (some c: Configuration |#c.f1=1 and #c.f19=1 ) }
pred Pair19
{ (some c: Configuration |#c.f2=1 and #c.f3=1 ) }
pred Pair20
{ (some c: Configuration |#c.f2=1 and #c.f4=1 ) }
pred Pair21
{ (some c: Configuration |#c.f2=1 and #c.f5=1) }
pred Pair22
{ (some c: Configuration |#c.f2=1 and #c.f6=1) }
pred Pair23
{ (some c: Configuration |#c.f2=1 and #c.f7=1 ) }
pred Pair24
{ (some c: Configuration |#c.f2=1 and #c.f8=1 ) }
pred Pair25
{ (some c: Configuration |#c.f2=1 and #c.f9=1) }
pred Pair26
{ (some c: Configuration |#c.f2=1 and #c.f10=1) }
pred Pair27
{ (some c: Configuration |#c.f2=1 and #c.f11=1 ) }
pred Pair28
{ (some c: Configuration |#c.f2=1 and #c.f12=1 ) }
pred Pair29
{ (some c: Configuration |#c.f2=1 and #c.f13=1) }
pred Pair30
{ (some c: Configuration |#c.f2=1 and #c.f14=1) }
pred Pair31
{ (some c: Configuration |#c.f2=1 and #c.f15=1 ) }
pred Pair32
{ (some c: Configuration |#c.f2=1 and #c.f16=1 ) }
pred Pair33
{ (some c: Configuration |#c.f2=1 and #c.f17=1) }
pred Pair34
{ (some c: Configuration |#c.f2=1 and #c.f18=1) }
pred Pair35
{ (some c: Configuration |#c.f2=1 and #c.f19=1 ) }
pred Pair36
{ (some c: Configuration |#c.f3=1 and #c.f4=1 ) }
pred Pair37
{ (some c: Configuration |#c.f3=1 and #c.f5=1) }
pred Pair38
{ (some c: Configuration |#c.f3=1 and #c.f6=1) }
pred Pair39
{ (some c: Configuration |#c.f3=1 and #c.f7=1 ) }
pred Pair40
{ (some c: Configuration |#c.f3=1 and #c.f8=1 ) }
pred Pair41
{ (some c: Configuration |#c.f3=1 and #c.f9=1) }
pred Pair42
{ (some c: Configuration |#c.f3=1 and #c.f10=1) }
pred Pair43
{ (some c: Configuration |#c.f3=1 and #c.f11=1 ) }
pred Pair44
{ (some c: Configuration |#c.f3=1 and #c.f12=1 ) }
pred Pair45
{ (some c: Configuration |#c.f3=1 and #c.f13=1) }
pred Pair46
{ (some c: Configuration |#c.f3=1 and #c.f14=1) }
pred Pair47
{ (some c: Configuration |#c.f3=1 and #c.f15=1 ) }
pred Pair48
{ (some c: Configuration |#c.f3=1 and #c.f16=1 ) }
pred Pair49
{ (some c: Configuration |#c.f3=1 and #c.f17=1) }
pred Pair50
{ (some c: Configuration |#c.f3=1 and #c.f18=1) }
pred Pair51
{ (some c: Configuration |#c.f3=1 and #c.f19=1 ) }
pred Pair52
{ (some c: Configuration |#c.f4=1 and #c.f5=1) }
pred Pair53
{ (some c: Configuration |#c.f4=1 and #c.f6=1) }
pred Pair54
{ (some c: Configuration |#c.f4=1 and #c.f7=1 ) }
pred Pair55
{ (some c: Configuration |#c.f4=1 and #c.f8=1 ) }
pred Pair56
{ (some c: Configuration |#c.f4=1 and #c.f9=1) }
pred Pair57
{ (some c: Configuration |#c.f4=1 and #c.f10=1) }
pred Pair58
{ (some c: Configuration |#c.f4=1 and #c.f11=1 ) }
pred Pair59
{ (some c: Configuration |#c.f4=1 and #c.f12=1 ) }
pred Pair60
{ (some c: Configuration |#c.f4=1 and #c.f13=1) }
pred Pair61
{ (some c: Configuration |#c.f4=1 and #c.f14=1) }
pred Pair62
{ (some c: Configuration |#c.f4=1 and #c.f15=1 ) }
pred Pair63
{ (some c: Configuration |#c.f4=1 and #c.f16=1 ) }
pred Pair64
{ (some c: Configuration |#c.f4=1 and #c.f17=1) }
pred Pair65
{ (some c: Configuration |#c.f4=1 and #c.f18=1) }
pred Pair66
{ (some c: Configuration |#c.f4=1 and #c.f19=1 ) }
pred Pair67
{ (some c: Configuration |#c.f5=1 and #c.f6=1) }
pred Pair68
{ (some c: Configuration |#c.f5=1 and #c.f7=1 ) }
pred Pair69
{ (some c: Configuration |#c.f5=1 and #c.f8=1 ) }
pred Pair70
{ (some c: Configuration |#c.f5=1 and #c.f9=1) }
pred Pair71
{ (some c: Configuration |#c.f5=1 and #c.f10=1) }
pred Pair72
{ (some c: Configuration |#c.f5=1 and #c.f11=1 ) }
pred Pair73
{ (some c: Configuration |#c.f5=1 and #c.f12=1 ) }
pred Pair74
{ (some c: Configuration |#c.f5=1 and #c.f13=1) }
pred Pair75
{ (some c: Configuration |#c.f5=1 and #c.f14=1) }
pred Pair76
{ (some c: Configuration |#c.f5=1 and #c.f15=1 ) }
pred Pair77
{ (some c: Configuration |#c.f5=1 and #c.f16=1 ) }
pred Pair78
{ (some c: Configuration |#c.f5=1 and #c.f17=1) }
pred Pair79
{ (some c: Configuration |#c.f5=1 and #c.f18=1) }
pred Pair80
{ (some c: Configuration |#c.f5=1 and #c.f19=1 ) }
pred Pair81
{ (some c: Configuration |#c.f6=1 and #c.f7=1 ) }
pred Pair82
{ (some c: Configuration |#c.f6=1 and #c.f8=1 ) }
pred Pair83
{ (some c: Configuration |#c.f6=1 and #c.f9=1) }
pred Pair84
{ (some c: Configuration |#c.f6=1 and #c.f10=1) }
pred Pair85
{ (some c: Configuration |#c.f6=1 and #c.f11=1 ) }
pred Pair86
{ (some c: Configuration |#c.f6=1 and #c.f12=1 ) }
pred Pair87
{ (some c: Configuration |#c.f6=1 and #c.f13=1) }
pred Pair88
{ (some c: Configuration |#c.f6=1 and #c.f14=1) }
pred Pair89
{ (some c: Configuration |#c.f6=1 and #c.f15=1 ) }
pred Pair90
{ (some c: Configuration |#c.f6=1 and #c.f16=1 ) }
pred Pair91
{ (some c: Configuration |#c.f6=1 and #c.f17=1) }
pred Pair92
{ (some c: Configuration |#c.f6=1 and #c.f18=1) }
pred Pair93
{ (some c: Configuration |#c.f6=1 and #c.f19=1 ) }
pred Pair94
{ (some c: Configuration |#c.f7=1 and #c.f8=1 ) }
pred Pair95
{ (some c: Configuration |#c.f7=1 and #c.f9=1) }
pred Pair96
{ (some c: Configuration |#c.f7=1 and #c.f10=1) }
pred Pair97
{ (some c: Configuration |#c.f7=1 and #c.f11=1 ) }
pred Pair98
{ (some c: Configuration |#c.f7=1 and #c.f12=1 ) }
pred Pair99
{ (some c: Configuration |#c.f7=1 and #c.f13=1) }
pred Pair100
{ (some c: Configuration |#c.f7=1 and #c.f14=1) }
pred Pair101
{ (some c: Configuration |#c.f7=1 and #c.f15=1 )}
pred Pair102
{ (some c: Configuration |#c.f7=1 and #c.f16=1 ) }
pred Pair103
{ (some c: Configuration |#c.f7=1 and #c.f17=1) }
pred Pair104
{ (some c: Configuration |#c.f7=1 and #c.f18=1) }
pred Pair105
{ (some c: Configuration |#c.f7=1 and #c.f19=1 ) }
pred Pair106
{ (some c: Configuration |#c.f8=1 and #c.f9=1) }
pred Pair107
{ (some c: Configuration |#c.f8=1 and #c.f10=1) }
pred Pair108
{ (some c: Configuration |#c.f8=1 and #c.f11=1 ) }
pred Pair109
{ (some c: Configuration |#c.f8=1 and #c.f12=1 ) }
pred Pair110
{ (some c: Configuration |#c.f8=1 and #c.f13=1) }
pred Pair111
{ (some c: Configuration |#c.f8=1 and #c.f14=1) }
pred Pair112
{ (some c: Configuration |#c.f8=1 and #c.f15=1 ) }
pred Pair113
{ (some c: Configuration |#c.f8=1 and #c.f16=1 ) }
pred Pair114
{ (some c: Configuration |#c.f8=1 and #c.f17=1) }
pred Pair115
{ (some c: Configuration |#c.f8=1 and #c.f18=1) }
pred Pair116
{ (some c: Configuration |#c.f8=1 and #c.f19=1 )}
pred Pair117
{ (some c: Configuration |#c.f9=1 and #c.f10=1) }
pred Pair118
{ (some c: Configuration |#c.f9=1 and #c.f11=1 ) }
pred Pair119
{ (some c: Configuration |#c.f9=1 and #c.f12=1 ) }
pred Pair120
{ (some c: Configuration |#c.f9=1 and #c.f13=1) }
pred Pair121
{ (some c: Configuration |#c.f9=1 and #c.f14=1) }
pred Pair122
{ (some c: Configuration |#c.f9=1 and #c.f15=1 ) }
pred Pair123
{ (some c: Configuration |#c.f9=1 and #c.f16=1 ) }
pred Pair124
{ (some c: Configuration |#c.f9=1 and #c.f17=1) }
pred Pair125
{ (some c: Configuration |#c.f9=1 and #c.f18=1) }
pred Pair126
{ (some c: Configuration |#c.f9=1 and #c.f19=1 ) }
pred Pair127
{ (some c: Configuration |#c.f10=1 and #c.f11=1 ) }
pred Pair128
{ (some c: Configuration |#c.f10=1 and #c.f12=1 ) }
pred Pair129
{ (some c: Configuration |#c.f10=1 and #c.f13=1) }
pred Pair130
{ (some c: Configuration |#c.f10=1 and #c.f14=1) }
pred Pair131
{ (some c: Configuration |#c.f10=1 and #c.f15=1 ) }
pred Pair132
{ (some c: Configuration |#c.f10=1 and #c.f16=1 ) }
pred Pair133
{ (some c: Configuration |#c.f10=1 and #c.f17=1) }
pred Pair134
{ (some c: Configuration |#c.f10=1 and #c.f18=1) }
pred Pair135
{ (some c: Configuration |#c.f10=1 and #c.f19=1 )}
pred Pair136
{ (some c: Configuration |#c.f11=1 and #c.f12=1 ) }
pred Pair137
{ (some c: Configuration |#c.f11=1 and #c.f13=1) }
pred Pair138
{ (some c: Configuration |#c.f11=1 and #c.f14=1) }
pred Pair139
{ (some c: Configuration |#c.f11=1 and #c.f15=1 ) }
pred Pair140
{ (some c: Configuration |#c.f11=1 and #c.f16=1 ) }
pred Pair141
{ (some c: Configuration |#c.f11=1 and #c.f17=1) }
pred Pair142
{ (some c: Configuration |#c.f11=1 and #c.f18=1) }
pred Pair143
{ (some c: Configuration |#c.f11=1 and #c.f19=1 ) }
pred Pair144
{ (some c: Configuration |#c.f12=1 and #c.f13=1) }
pred Pair145
{ (some c: Configuration |#c.f12=1 and #c.f14=1) }
pred Pair146
{ (some c: Configuration |#c.f12=1 and #c.f15=1 )}
pred Pair147
{ (some c: Configuration |#c.f12=1 and #c.f16=1 ) }
pred Pair148
{ (some c: Configuration |#c.f12=1 and #c.f17=1) }
pred Pair149
{ (some c: Configuration |#c.f12=1 and #c.f18=1) }
pred Pair150
{ (some c: Configuration |#c.f12=1 and #c.f19=1 ) }
pred Pair151
{ (some c: Configuration |#c.f13=1 and #c.f14=1) }
pred Pair152
{ (some c: Configuration |#c.f13=1 and #c.f15=1 ) }
pred Pair153
{ (some c: Configuration |#c.f13=1 and #c.f16=1 ) }
pred Pair154
{ (some c: Configuration |#c.f13=1 and #c.f17=1) }
pred Pair155
{ (some c: Configuration |#c.f13=1 and #c.f18=1) }
pred Pair156
{ (some c: Configuration |#c.f13=1 and #c.f19=1 ) }
pred Pair157
{ (some c: Configuration |#c.f14=1 and #c.f15=1 ) }
pred Pair158
{ (some c: Configuration |#c.f14=1 and #c.f16=1 ) }
pred Pair159
{ (some c: Configuration |#c.f14=1 and #c.f17=1) }
pred Pair160
{ (some c: Configuration |#c.f14=1 and #c.f18=1) }
pred Pair161
{ (some c: Configuration |#c.f14=1 and #c.f19=1 ) }
pred Pair162
{ (some c: Configuration |#c.f15=1 and #c.f16=1 ) }
pred Pair163
{ (some c: Configuration |#c.f15=1 and #c.f17=1) }
pred Pair164
{ (some c: Configuration |#c.f15=1 and #c.f18=1) }
pred Pair165
{ (some c: Configuration |#c.f15=1 and #c.f19=1 ) }
pred Pair166
{ (some c: Configuration |#c.f16=1 and #c.f17=1) }
pred Pair167
{ (some c: Configuration |#c.f16=1 and #c.f18=1) }
pred Pair168
{ (some c: Configuration |#c.f16=1 and #c.f19=1 )}
pred Pair169
{ (some c: Configuration |#c.f17=1 and #c.f18=1) }
pred Pair170
{ (some c: Configuration |#c.f17=1 and #c.f19=1 ) }
pred Pair171
{ (some c: Configuration |#c.f18=1 and #c.f19=1 ) }


pred Pair172
{ (some c: Configuration |#c.f1=0 and #c.f2=0)}
pred Pair173 { (some c: Configuration |#c.f1=0 and #c.f3=0 ) }
pred Pair174 { (some c: Configuration |#c.f1=0 and #c.f4=0 ) }
pred Pair175 { (some c: Configuration |#c.f1=0 and #c.f5=0) }
pred Pair176 { (some c: Configuration |#c.f1=0 and #c.f6=0) } 
pred Pair177 { (some c: Configuration |#c.f1=0 and #c.f7=0 ) }
pred Pair178 { (some c: Configuration |#c.f1=0 and #c.f8=0 ) }
pred Pair179 { (some c: Configuration |#c.f1=0 and #c.f9=0) }
pred Pair180 { (some c: Configuration |#c.f1=0 and #c.f10=0) } 
pred Pair181 { (some c: Configuration |#c.f1=0 and #c.f11=0 ) }
pred Pair182 { (some c: Configuration |#c.f1=0 and #c.f12=0 ) }
pred Pair183 { (some c: Configuration |#c.f1=0 and #c.f13=0) }
pred Pair184 { (some c: Configuration |#c.f1=0 and #c.f14=0) } 
pred Pair185 { (some c: Configuration |#c.f1=0 and #c.f15=0 ) }
pred Pair186 { (some c: Configuration |#c.f1=0 and #c.f16=0 ) }
pred Pair187 { (some c: Configuration |#c.f1=0 and #c.f17=0) }
pred Pair188 { (some c: Configuration |#c.f1=0 and #c.f18=0) } 
pred Pair189 { (some c: Configuration |#c.f1=0 and #c.f19=0 ) }
pred Pair190 { (some c: Configuration |#c.f2=0 and #c.f3=0 ) }
pred Pair191 { (some c: Configuration |#c.f2=0 and #c.f4=0 ) }
pred Pair192 { (some c: Configuration |#c.f2=0 and #c.f5=0) }
pred Pair193 { (some c: Configuration |#c.f2=0 and #c.f6=0) } 
pred Pair194 { (some c: Configuration |#c.f2=0 and #c.f7=0 ) }
pred Pair195 { (some c: Configuration |#c.f2=0 and #c.f8=0 ) }
pred Pair196 { (some c: Configuration |#c.f2=0 and #c.f9=0) }
pred Pair197 { (some c: Configuration |#c.f2=0 and #c.f10=0) } 
pred Pair198 { (some c: Configuration |#c.f2=0 and #c.f11=0 ) }
pred Pair199 { (some c: Configuration |#c.f2=0 and #c.f12=0 ) }
pred Pair200 { (some c: Configuration |#c.f2=0 and #c.f13=0) }
pred Pair201 { (some c: Configuration |#c.f2=0 and #c.f14=0) } 
pred Pair202 { (some c: Configuration |#c.f2=0 and #c.f15=0 ) }
pred Pair203 { (some c: Configuration |#c.f2=0 and #c.f16=0 ) }
pred Pair204 { (some c: Configuration |#c.f2=0 and #c.f17=0) }
pred Pair205 { (some c: Configuration |#c.f2=0 and #c.f18=0) } 
pred Pair206 { (some c: Configuration |#c.f2=0 and #c.f19=0 ) }
pred Pair207 { (some c: Configuration |#c.f3=0 and #c.f4=0 ) }
pred Pair208 { (some c: Configuration |#c.f3=0 and #c.f5=0) }
pred Pair209 { (some c: Configuration |#c.f3=0 and #c.f6=0) } 
pred Pair210 { (some c: Configuration |#c.f3=0 and #c.f7=0 ) }
pred Pair211 { (some c: Configuration |#c.f3=0 and #c.f8=0 ) }
pred Pair212 { (some c: Configuration |#c.f3=0 and #c.f9=0) }
pred Pair213 { (some c: Configuration |#c.f3=0 and #c.f10=0) } 
pred Pair214 { (some c: Configuration |#c.f3=0 and #c.f11=0 ) }
pred Pair215 { (some c: Configuration |#c.f3=0 and #c.f12=0 ) }
pred Pair216 { (some c: Configuration |#c.f3=0 and #c.f13=0) }
pred Pair217 { (some c: Configuration |#c.f3=0 and #c.f14=0) } 
pred Pair218 { (some c: Configuration |#c.f3=0 and #c.f15=0 ) }
pred Pair219 { (some c: Configuration |#c.f3=0 and #c.f16=0 ) }
pred Pair220 { (some c: Configuration |#c.f3=0 and #c.f17=0) }
pred Pair221 { (some c: Configuration |#c.f3=0 and #c.f18=0) } 
pred Pair222 { (some c: Configuration |#c.f3=0 and #c.f19=0 ) }
pred Pair223 { (some c: Configuration |#c.f4=0 and #c.f5=0) }
pred Pair224 { (some c: Configuration |#c.f4=0 and #c.f6=0) } 
pred Pair225 { (some c: Configuration |#c.f4=0 and #c.f7=0 ) }
pred Pair226 { (some c: Configuration |#c.f4=0 and #c.f8=0 ) }
pred Pair227 { (some c: Configuration |#c.f4=0 and #c.f9=0) }
pred Pair228 { (some c: Configuration |#c.f4=0 and #c.f10=0) } 
pred Pair229 { (some c: Configuration |#c.f4=0 and #c.f11=0 ) }
pred Pair230 { (some c: Configuration |#c.f4=0 and #c.f12=0 ) }
pred Pair231 { (some c: Configuration |#c.f4=0 and #c.f13=0) }
pred Pair232 { (some c: Configuration |#c.f4=0 and #c.f14=0) } 
pred Pair233 { (some c: Configuration |#c.f4=0 and #c.f15=0 ) }
pred Pair234 { (some c: Configuration |#c.f4=0 and #c.f16=0 ) }
pred Pair235 { (some c: Configuration |#c.f4=0 and #c.f17=0) }
pred Pair236 { (some c: Configuration |#c.f4=0 and #c.f18=0) } 
pred Pair237 { (some c: Configuration |#c.f4=0 and #c.f19=0 ) }
pred Pair238 { (some c: Configuration |#c.f5=0 and #c.f6=0) } 
pred Pair239 { (some c: Configuration |#c.f5=0 and #c.f7=0 ) }
pred Pair240 { (some c: Configuration |#c.f5=0 and #c.f8=0 ) }
pred Pair241 { (some c: Configuration |#c.f5=0 and #c.f9=0) }
pred Pair242 { (some c: Configuration |#c.f5=0 and #c.f10=0) } 
pred Pair243 { (some c: Configuration |#c.f5=0 and #c.f11=0 ) }
pred Pair244 { (some c: Configuration |#c.f5=0 and #c.f12=0 ) }
pred Pair245 { (some c: Configuration |#c.f5=0 and #c.f13=0) }
pred Pair246 { (some c: Configuration |#c.f5=0 and #c.f14=0) } 
pred Pair247 { (some c: Configuration |#c.f5=0 and #c.f15=0 ) }
pred Pair248 { (some c: Configuration |#c.f5=0 and #c.f16=0 ) }
pred Pair249 { (some c: Configuration |#c.f5=0 and #c.f17=0) }
pred Pair250 { (some c: Configuration |#c.f5=0 and #c.f18=0) } 
pred Pair251 { (some c: Configuration |#c.f5=0 and #c.f19=0 ) }
pred Pair252 { (some c: Configuration |#c.f6=0 and #c.f7=0 ) }
pred Pair253 { (some c: Configuration |#c.f6=0 and #c.f8=0 ) }
pred Pair254 { (some c: Configuration |#c.f6=0 and #c.f9=0) }
pred Pair255 { (some c: Configuration |#c.f6=0 and #c.f10=0) } 
pred Pair256 { (some c: Configuration |#c.f6=0 and #c.f11=0 ) }
pred Pair257 { (some c: Configuration |#c.f6=0 and #c.f12=0 ) }
pred Pair258 { (some c: Configuration |#c.f6=0 and #c.f13=0) }
pred Pair259 { (some c: Configuration |#c.f6=0 and #c.f14=0) } 
pred Pair260 { (some c: Configuration |#c.f6=0 and #c.f15=0 ) }
pred Pair261 { (some c: Configuration |#c.f6=0 and #c.f16=0 ) }
pred Pair262 { (some c: Configuration |#c.f6=0 and #c.f17=0) }
pred Pair263 { (some c: Configuration |#c.f6=0 and #c.f18=0) } 
pred Pair264 { (some c: Configuration |#c.f6=0 and #c.f19=0 ) }
pred Pair265 { (some c: Configuration |#c.f7=0 and #c.f8=0 ) }
pred Pair266 { (some c: Configuration |#c.f7=0 and #c.f9=0) }
pred Pair267 { (some c: Configuration |#c.f7=0 and #c.f10=0) } 
pred Pair268 { (some c: Configuration |#c.f7=0 and #c.f11=0 ) }
pred Pair269 { (some c: Configuration |#c.f7=0 and #c.f12=0 ) }
pred Pair270 { (some c: Configuration |#c.f7=0 and #c.f13=0) }
pred Pair271 { (some c: Configuration |#c.f7=0 and #c.f14=0) } 
pred Pair272 { (some c: Configuration |#c.f7=0 and #c.f15=0 ) }
pred Pair273 { (some c: Configuration |#c.f7=0 and #c.f16=0 ) }
pred Pair274 { (some c: Configuration |#c.f7=0 and #c.f17=0) }
pred Pair275 { (some c: Configuration |#c.f7=0 and #c.f18=0) } 
pred Pair276 { (some c: Configuration |#c.f7=0 and #c.f19=0 ) }
pred Pair277 { (some c: Configuration |#c.f8=0 and #c.f9=0) }
pred Pair278 { (some c: Configuration |#c.f8=0 and #c.f10=0) } 
pred Pair279 { (some c: Configuration |#c.f8=0 and #c.f11=0 ) }
pred Pair280 { (some c: Configuration |#c.f8=0 and #c.f12=0 ) }
pred Pair281 { (some c: Configuration |#c.f8=0 and #c.f13=0) }
pred Pair282 { (some c: Configuration |#c.f8=0 and #c.f14=0) } 
pred Pair283 { (some c: Configuration |#c.f8=0 and #c.f15=0 ) }
pred Pair284 { (some c: Configuration |#c.f8=0 and #c.f16=0 ) }
pred Pair285 { (some c: Configuration |#c.f8=0 and #c.f17=0) }
pred Pair286 { (some c: Configuration |#c.f8=0 and #c.f18=0) } 
pred Pair287 { (some c: Configuration |#c.f8=0 and #c.f19=0 ) }
pred Pair288 { (some c: Configuration |#c.f9=0 and #c.f10=0) } 
pred Pair289 { (some c: Configuration |#c.f9=0 and #c.f11=0 ) }
pred Pair290 { (some c: Configuration |#c.f9=0 and #c.f12=0 ) }
pred Pair291 { (some c: Configuration |#c.f9=0 and #c.f13=0) }
pred Pair292 { (some c: Configuration |#c.f9=0 and #c.f14=0) } 
pred Pair293 { (some c: Configuration |#c.f9=0 and #c.f15=0 ) }
pred Pair294 { (some c: Configuration |#c.f9=0 and #c.f16=0 ) }
pred Pair295 { (some c: Configuration |#c.f9=0 and #c.f17=0) }
pred Pair296 { (some c: Configuration |#c.f9=0 and #c.f18=0) } 
pred Pair297 { (some c: Configuration |#c.f9=0 and #c.f19=0 ) }
pred Pair298 { (some c: Configuration |#c.f10=0 and #c.f11=0 ) }
pred Pair299 { (some c: Configuration |#c.f10=0 and #c.f12=0 ) }
pred Pair301 { (some c: Configuration |#c.f10=0 and #c.f13=0) }
pred Pair302{ (some c: Configuration |#c.f10=0 and #c.f14=0) } 
pred Pair303 { (some c: Configuration |#c.f10=0 and #c.f15=0 ) }
pred Pair304 { (some c: Configuration |#c.f10=0 and #c.f16=0 ) }
pred Pair305 { (some c: Configuration |#c.f10=0 and #c.f17=0) }
pred Pair306 { (some c: Configuration |#c.f10=0 and #c.f18=0) } 
pred Pair307 { (some c: Configuration |#c.f10=0 and #c.f19=0 ) }
pred Pair308 { (some c: Configuration |#c.f11=0 and #c.f12=0 ) }
pred Pair309 { (some c: Configuration |#c.f11=0 and #c.f13=0) }
pred Pair310 { (some c: Configuration |#c.f11=0 and #c.f14=0) } 
pred Pair311 { (some c: Configuration |#c.f11=0 and #c.f15=0 ) }
pred Pair312 { (some c: Configuration |#c.f11=0 and #c.f16=0 ) }
pred Pair313 { (some c: Configuration |#c.f11=0 and #c.f17=0) }
pred Pair314 { (some c: Configuration |#c.f11=0 and #c.f18=0) } 
pred Pair315 { (some c: Configuration |#c.f11=0 and #c.f19=0 ) }
pred Pair316 { (some c: Configuration |#c.f12=0 and #c.f13=0) }
pred Pair317 { (some c: Configuration |#c.f12=0 and #c.f14=0) } 
pred Pair318 { (some c: Configuration |#c.f12=0 and #c.f15=0 ) }
pred Pair329 { (some c: Configuration |#c.f12=0 and #c.f16=0 ) }
pred Pair330 { (some c: Configuration |#c.f12=0 and #c.f17=0) }
pred Pair331 { (some c: Configuration |#c.f12=0 and #c.f18=0) } 
pred Pair332 { (some c: Configuration |#c.f12=0 and #c.f19=0 ) }
pred Pair333 { (some c: Configuration |#c.f13=0 and #c.f14=0) } 
pred Pair334 { (some c: Configuration |#c.f13=0 and #c.f15=0 ) }
pred Pair335 { (some c: Configuration |#c.f13=0 and #c.f16=0 ) }
pred Pair336 { (some c: Configuration |#c.f13=0 and #c.f17=0) }
pred Pair337 { (some c: Configuration |#c.f13=0 and #c.f18=0) } 
pred Pair338 { (some c: Configuration |#c.f13=0 and #c.f19=0 ) }
pred Pair339 { (some c: Configuration |#c.f14=0 and #c.f15=0 ) }
pred Pair340 { (some c: Configuration |#c.f14=0 and #c.f16=0 ) }
pred Pair341 { (some c: Configuration |#c.f14=0 and #c.f17=0) }
pred Pair342 { (some c: Configuration |#c.f14=0 and #c.f18=0) } 
pred Pair343 { (some c: Configuration |#c.f14=0 and #c.f19=0 ) }
pred Pair344 { (some c: Configuration |#c.f15=0 and #c.f16=0 ) }
pred Pair345 { (some c: Configuration |#c.f15=0 and #c.f17=0) }
pred Pair346 { (some c: Configuration |#c.f15=0 and #c.f18=0) } 
pred Pair347 { (some c: Configuration |#c.f15=0 and #c.f19=0 ) }
pred Pair348 { (some c: Configuration |#c.f16=0 and #c.f17=0) }
pred Pair349 { (some c: Configuration |#c.f16=0 and #c.f18=0) } 
pred Pair350 { (some c: Configuration |#c.f16=0 and #c.f19=0 ) }
pred Pair351 { (some c: Configuration |#c.f17=0 and #c.f18=0) } 
pred Pair352 { (some c: Configuration |#c.f17=0 and #c.f19=0 ) }
pred Pair353 { (some c: Configuration |#c.f18=0 and #c.f19=0 ) }


//pred PairWise3

pred Pair354 { (some c: Configuration |#c.f1=1 and #c.f2=0) } 
pred Pair355 { (some c: Configuration |#c.f1=1 and #c.f3=0 ) }
pred Pair356 { (some c: Configuration |#c.f1=1 and #c.f4=0 ) }
pred Pair357 { (some c: Configuration |#c.f1=1 and #c.f5=0) }
pred Pair358 { (some c: Configuration |#c.f1=1 and #c.f6=0) } 
pred Pair359 { (some c: Configuration |#c.f1=1 and #c.f7=0 ) }
pred Pair360 { (some c: Configuration |#c.f1=1 and #c.f8=0 ) }
pred Pair361 { (some c: Configuration |#c.f1=1 and #c.f9=0) }
pred Pair362 { (some c: Configuration |#c.f1=1 and #c.f10=0) } 
pred Pair363 { (some c: Configuration |#c.f1=1 and #c.f11=0 ) }
pred Pair364 { (some c: Configuration |#c.f1=1 and #c.f12=0 ) }
pred Pair365 { (some c: Configuration |#c.f1=1 and #c.f13=0) }
pred Pair366 { (some c: Configuration |#c.f1=1 and #c.f14=0) } 
pred Pair367 { (some c: Configuration |#c.f1=1 and #c.f15=0 ) }
pred Pair368 { (some c: Configuration |#c.f1=1 and #c.f16=0 ) }
pred Pair369 { (some c: Configuration |#c.f1=1 and #c.f17=0) }
pred Pair370 { (some c: Configuration |#c.f1=1 and #c.f18=0) } 
pred Pair371 { (some c: Configuration |#c.f1=1 and #c.f19=0 ) }
pred Pair372 { (some c: Configuration |#c.f2=1 and #c.f3=0 ) }
pred Pair373 { (some c: Configuration |#c.f2=1 and #c.f4=0 ) }
pred Pair374 { (some c: Configuration |#c.f2=1 and #c.f5=0) }
pred Pair375 { (some c: Configuration |#c.f2=1 and #c.f6=0) } 
pred Pair376 { (some c: Configuration |#c.f2=1 and #c.f7=0 ) }
pred Pair377 { (some c: Configuration |#c.f2=1 and #c.f8=0 ) }
pred Pair378 { (some c: Configuration |#c.f2=1 and #c.f9=0) }
pred Pair379 { (some c: Configuration |#c.f2=1 and #c.f10=0) } 
pred Pair380 { (some c: Configuration |#c.f2=1 and #c.f11=0 ) }
pred Pair381 { (some c: Configuration |#c.f2=1 and #c.f12=0 ) }
pred Pair382 { (some c: Configuration |#c.f2=1 and #c.f13=0) }
pred Pair383 { (some c: Configuration |#c.f2=1 and #c.f14=0) } 
pred Pair384 { (some c: Configuration |#c.f2=1 and #c.f15=0 ) }
pred Pair385 { (some c: Configuration |#c.f2=1 and #c.f16=0 ) }
pred Pair386 { (some c: Configuration |#c.f2=1 and #c.f17=0) }
pred Pair387 { (some c: Configuration |#c.f2=1 and #c.f18=0) } 
pred Pair388 { (some c: Configuration |#c.f2=1 and #c.f19=0 ) }
pred Pair389 { (some c: Configuration |#c.f3=1 and #c.f4=0 ) }
pred Pair390 { (some c: Configuration |#c.f3=1 and #c.f5=0) }
pred Pair391 { (some c: Configuration |#c.f3=1 and #c.f6=0) } 
pred Pair392 { (some c: Configuration |#c.f3=1 and #c.f7=0 ) }
pred Pair393 { (some c: Configuration |#c.f3=1 and #c.f8=0 ) }
pred Pair394 { (some c: Configuration |#c.f3=1 and #c.f9=0) }
pred Pair395 { (some c: Configuration |#c.f3=1 and #c.f10=0) } 
pred Pair396 { (some c: Configuration |#c.f3=1 and #c.f11=0 ) }
pred Pair397 { (some c: Configuration |#c.f3=1 and #c.f13=0) }
pred Pair400 { (some c: Configuration |#c.f3=1 and #c.f14=0) } 
pred Pair401 { (some c: Configuration |#c.f3=1 and #c.f15=0 ) }
pred Pair402 { (some c: Configuration |#c.f3=1 and #c.f16=0 ) }
pred Pair403 { (some c: Configuration |#c.f3=1 and #c.f17=0) }
pred Pair404 { (some c: Configuration |#c.f3=1 and #c.f18=0) } 
pred Pair405 { (some c: Configuration |#c.f3=1 and #c.f19=0 ) }
pred Pair406 { (some c: Configuration |#c.f4=1 and #c.f5=0) }
pred Pair407 { (some c: Configuration |#c.f4=1 and #c.f6=0) } 
pred Pair408 { (some c: Configuration |#c.f4=1 and #c.f7=0 ) }
pred Pair409 { (some c: Configuration |#c.f4=1 and #c.f8=0 ) }
pred Pair410 { (some c: Configuration |#c.f4=1 and #c.f9=0) }
pred Pair411 { (some c: Configuration |#c.f4=1 and #c.f10=0) } 
pred Pair412 { (some c: Configuration |#c.f4=1 and #c.f11=0 ) }
pred Pair413 { (some c: Configuration |#c.f4=1 and #c.f12=0 ) }
pred Pair414 { (some c: Configuration |#c.f4=1 and #c.f13=0) }
pred Pair415 { (some c: Configuration |#c.f4=1 and #c.f14=0) } 
pred Pair416 { (some c: Configuration |#c.f4=1 and #c.f15=0 ) }
pred Pair417 { (some c: Configuration |#c.f4=1 and #c.f16=0 ) }
pred Pair418 { (some c: Configuration |#c.f4=1 and #c.f17=0) }
pred Pair419 { (some c: Configuration |#c.f4=1 and #c.f18=0) } 
pred Pair420 { (some c: Configuration |#c.f4=1 and #c.f19=0 ) }
pred Pair421 { (some c: Configuration |#c.f5=1 and #c.f6=0) } 
pred Pair422 { (some c: Configuration |#c.f5=1 and #c.f7=0 ) }
pred Pair423 { (some c: Configuration |#c.f5=1 and #c.f8=0 ) }
pred Pair424 { (some c: Configuration |#c.f5=1 and #c.f9=0) }
pred Pair425 { (some c: Configuration |#c.f5=1 and #c.f10=0) } 
pred Pair426 { (some c: Configuration |#c.f5=1 and #c.f11=0 ) }
pred Pair427 { (some c: Configuration |#c.f5=1 and #c.f12=0 ) }
pred Pair428 { (some c: Configuration |#c.f5=1 and #c.f13=0) }
pred Pair429 { (some c: Configuration |#c.f5=1 and #c.f14=0) } 
pred Pair430 { (some c: Configuration |#c.f5=1 and #c.f15=0 ) }
pred Pair431 { (some c: Configuration |#c.f5=1 and #c.f16=0 ) }
pred Pair432 { (some c: Configuration |#c.f5=1 and #c.f17=0) }
pred Pair433 { (some c: Configuration |#c.f5=1 and #c.f18=0) } 
pred Pair434 { (some c: Configuration |#c.f5=1 and #c.f19=0 ) }
pred Pair435 { (some c: Configuration |#c.f6=1 and #c.f7=0 ) }
pred Pair436 { (some c: Configuration |#c.f6=1 and #c.f8=0 ) }
pred Pair437 { (some c: Configuration |#c.f6=1 and #c.f9=0) }
pred Pair438 { (some c: Configuration |#c.f6=1 and #c.f10=0) } 
pred Pair439 { (some c: Configuration |#c.f6=1 and #c.f11=0 ) }
pred Pair440 { (some c: Configuration |#c.f6=1 and #c.f12=0 ) }
pred Pair441 { (some c: Configuration |#c.f6=1 and #c.f13=0) }
pred Pair442 { (some c: Configuration |#c.f6=1 and #c.f14=0) } 
pred Pair443 { (some c: Configuration |#c.f6=1 and #c.f15=0 ) }
pred Pair444 { (some c: Configuration |#c.f6=1 and #c.f16=0 ) }
pred Pair445 { (some c: Configuration |#c.f6=1 and #c.f17=0) }
pred Pair446 { (some c: Configuration |#c.f6=1 and #c.f18=0) } 
pred Pair447 { (some c: Configuration |#c.f6=1 and #c.f19=0 ) }
pred Pair448 { (some c: Configuration |#c.f7=1 and #c.f8=0 ) }
pred Pair449 { (some c: Configuration |#c.f7=1 and #c.f9=0) }
pred Pair450 { (some c: Configuration |#c.f7=1 and #c.f10=0) } 
pred Pair451 { (some c: Configuration |#c.f7=1 and #c.f11=0 ) }
pred Pair452 { (some c: Configuration |#c.f7=1 and #c.f12=0 ) }
pred Pair453 { (some c: Configuration |#c.f7=1 and #c.f13=0) }
pred Pair454 { (some c: Configuration |#c.f7=1 and #c.f14=0) } 
pred Pair455 { (some c: Configuration |#c.f7=1 and #c.f15=0 ) }
pred Pair456 { (some c: Configuration |#c.f7=1 and #c.f16=0 ) }
pred Pair457 { (some c: Configuration |#c.f7=1 and #c.f17=0) }
pred Pair458 { (some c: Configuration |#c.f7=1 and #c.f18=0) } 
pred Pair459 { (some c: Configuration |#c.f7=1 and #c.f19=0 ) }
pred Pair460 { (some c: Configuration |#c.f8=1 and #c.f9=0) }
pred Pair461 { (some c: Configuration |#c.f8=1 and #c.f10=0) } 
pred Pair462 { (some c: Configuration |#c.f8=1 and #c.f11=0 ) }
pred Pair463 { (some c: Configuration |#c.f8=1 and #c.f12=0 ) }
pred Pair464 { (some c: Configuration |#c.f8=1 and #c.f13=0) }
pred Pair465 { (some c: Configuration |#c.f8=1 and #c.f14=0) } 
pred Pair466 { (some c: Configuration |#c.f8=1 and #c.f15=0 ) }
pred Pair467 { (some c: Configuration |#c.f8=1 and #c.f16=0 ) }
pred Pair468 { (some c: Configuration |#c.f8=1 and #c.f17=0) }
pred Pair469 { (some c: Configuration |#c.f8=1 and #c.f18=0) } 
pred Pair470 { (some c: Configuration |#c.f8=1 and #c.f19=0 ) }
pred Pair471 { (some c: Configuration |#c.f9=1 and #c.f10=0) } 
pred Pair472 { (some c: Configuration |#c.f9=1 and #c.f11=0 ) }
pred Pair473 { (some c: Configuration |#c.f9=1 and #c.f12=0 ) }
pred Pair474 { (some c: Configuration |#c.f9=1 and #c.f13=0) }
pred Pair475 { (some c: Configuration |#c.f9=1 and #c.f14=0) } 
pred Pair476 { (some c: Configuration |#c.f9=1 and #c.f15=0 ) }
pred Pair477 { (some c: Configuration |#c.f9=1 and #c.f16=0 ) }
pred Pair478 { (some c: Configuration |#c.f9=1 and #c.f17=0) }
pred Pair479 { (some c: Configuration |#c.f9=1 and #c.f18=0) } 
pred Pair480 { (some c: Configuration |#c.f9=1 and #c.f19=0 ) }
pred Pair481 { (some c: Configuration |#c.f10=1 and #c.f11=0 ) }
pred Pair482 { (some c: Configuration |#c.f10=1 and #c.f12=0 ) }
pred Pair483 { (some c: Configuration |#c.f10=1 and #c.f13=0) }
pred Pair484 { (some c: Configuration |#c.f10=1 and #c.f14=0) } 
pred Pair485 { (some c: Configuration |#c.f10=1 and #c.f15=0 ) }
pred Pair486 { (some c: Configuration |#c.f10=1 and #c.f16=0 ) }
pred Pair487 { (some c: Configuration |#c.f10=1 and #c.f17=0) }
pred Pair488 { (some c: Configuration |#c.f10=1 and #c.f18=0) } 
pred Pair489 { (some c: Configuration |#c.f10=1 and #c.f19=0 ) }
pred Pair490 { (some c: Configuration |#c.f11=1 and #c.f12=0 ) }
pred Pair491 { (some c: Configuration |#c.f11=1 and #c.f13=0) }
pred Pair492 { (some c: Configuration |#c.f11=1 and #c.f14=0) } 
pred Pair493 { (some c: Configuration |#c.f11=1 and #c.f15=0 ) }
pred Pair494 { (some c: Configuration |#c.f11=1 and #c.f16=0 ) }
pred Pair495 { (some c: Configuration |#c.f11=1 and #c.f17=0) }
pred Pair496 { (some c: Configuration |#c.f11=1 and #c.f18=0) } 
pred Pair497 { (some c: Configuration |#c.f11=1 and #c.f19=0 ) }
pred Pair498 { (some c: Configuration |#c.f12=1 and #c.f13=0) }
pred Pair499 { (some c: Configuration |#c.f12=1 and #c.f14=0) } 
pred Pair500 { (some c: Configuration |#c.f12=1 and #c.f15=0 ) }
pred Pair501 { (some c: Configuration |#c.f12=1 and #c.f16=0 ) }
pred Pair502 { (some c: Configuration |#c.f12=1 and #c.f17=0) }
pred Pair503 { (some c: Configuration |#c.f12=1 and #c.f18=0) } 
pred Pair504 { (some c: Configuration |#c.f12=1 and #c.f19=0 ) }
pred Pair505 { (some c: Configuration |#c.f13=1 and #c.f14=0) } 
pred Pair506 { (some c: Configuration |#c.f13=1 and #c.f15=0 ) }
pred Pair507 { (some c: Configuration |#c.f13=1 and #c.f16=0 ) }
pred Pair508 { (some c: Configuration |#c.f13=1 and #c.f17=0) }
pred Pair509 { (some c: Configuration |#c.f13=1 and #c.f18=0) } 
pred Pair510 { (some c: Configuration |#c.f13=1 and #c.f19=0 ) }
pred Pair511 { (some c: Configuration |#c.f14=1 and #c.f15=0 ) }
pred Pair512 { (some c: Configuration |#c.f14=1 and #c.f16=0 ) }
pred Pair513 { (some c: Configuration |#c.f14=1 and #c.f17=0) }
pred Pair514 { (some c: Configuration |#c.f14=1 and #c.f18=0) } 
pred Pair515 { (some c: Configuration |#c.f14=1 and #c.f19=0 ) }
pred Pair516 { (some c: Configuration |#c.f15=1 and #c.f16=0 ) }
pred Pair517 { (some c: Configuration |#c.f15=1 and #c.f17=0) }
pred Pair518 { (some c: Configuration |#c.f15=1 and #c.f18=0) } 
pred Pair519 { (some c: Configuration |#c.f15=1 and #c.f19=0 ) }
pred Pair520 { (some c: Configuration |#c.f16=1 and #c.f17=0) }
pred Pair521 { (some c: Configuration |#c.f16=1 and #c.f18=0) } 
pred Pair522 { (some c: Configuration |#c.f16=1 and #c.f19=0 ) }
pred Pair523 { (some c: Configuration |#c.f17=1 and #c.f18=0) } 
pred Pair524 { (some c: Configuration |#c.f17=1 and #c.f19=0 ) }
pred Pair525 { (some c: Configuration |#c.f18=1 and #c.f19=0 ) }

//PairWise 4
pred Pair526 { (some c: Configuration |#c.f1=0 and #c.f2=1) } 
pred Pair527 { (some c: Configuration |#c.f1=0 and #c.f3=1 ) }
pred Pair528 { (some c: Configuration |#c.f1=0 and #c.f4=1 ) }
pred Pair529 { (some c: Configuration |#c.f1=0 and #c.f5=1) }
pred Pair530 { (some c: Configuration |#c.f1=0 and #c.f6=1) } 
pred Pair531 { (some c: Configuration |#c.f1=0 and #c.f7=1 ) }
pred Pair532 { (some c: Configuration |#c.f1=0 and #c.f8=1 ) }
pred Pair533 { (some c: Configuration |#c.f1=0 and #c.f9=1) }
pred Pair534 { (some c: Configuration |#c.f1=0 and #c.f10=1) } 
pred Pair535 { (some c: Configuration |#c.f1=0 and #c.f11=1 ) }
pred Pair536 { (some c: Configuration |#c.f1=0 and #c.f12=1 ) }
pred Pair537 { (some c: Configuration |#c.f1=0 and #c.f13=1) }
pred Pair538 { (some c: Configuration |#c.f1=0 and #c.f14=1) } 
pred Pair539 { (some c: Configuration |#c.f1=0 and #c.f15=1 ) }
pred Pair540 { (some c: Configuration |#c.f1=0 and #c.f16=1 ) }
pred Pair541 { (some c: Configuration |#c.f1=0 and #c.f17=1) }
pred Pair542 { (some c: Configuration |#c.f1=0 and #c.f18=1) } 
pred Pair543 { (some c: Configuration |#c.f1=0 and #c.f19=1 ) }
pred Pair544 { (some c: Configuration |#c.f2=0 and #c.f3=1 ) }
pred Pair545 { (some c: Configuration |#c.f2=0 and #c.f4=1 ) }
pred Pair546 { (some c: Configuration |#c.f2=0 and #c.f5=1) }
pred Pair547 { (some c: Configuration |#c.f2=0 and #c.f6=1) } 
pred Pair548 { (some c: Configuration |#c.f2=0 and #c.f7=1 ) }
pred Pair549 { (some c: Configuration |#c.f2=0 and #c.f8=1 ) }
pred Pair550 { (some c: Configuration |#c.f2=0 and #c.f9=1) }
pred Pair551 { (some c: Configuration |#c.f2=0 and #c.f10=1) } 
pred Pair552 { (some c: Configuration |#c.f2=0 and #c.f11=1 ) }
pred Pair553 { (some c: Configuration |#c.f2=0 and #c.f12=1 ) }
pred Pair554 { (some c: Configuration |#c.f2=0 and #c.f13=1) }
pred Pair555 { (some c: Configuration |#c.f2=0 and #c.f14=1) } 
pred Pair556 { (some c: Configuration |#c.f2=0 and #c.f15=1 ) }
pred Pair557 { (some c: Configuration |#c.f2=0 and #c.f16=1 ) }
pred Pair558 { (some c: Configuration |#c.f2=0 and #c.f17=1) }
pred Pair559 { (some c: Configuration |#c.f2=0 and #c.f18=1) } 
pred Pair560 { (some c: Configuration |#c.f2=0 and #c.f19=1 ) }
pred Pair561 { (some c: Configuration |#c.f3=0 and #c.f4=1 ) }
pred Pair562 { (some c: Configuration |#c.f3=0 and #c.f5=1) }
pred Pair563 { (some c: Configuration |#c.f3=0 and #c.f6=1) } 
pred Pair564 { (some c: Configuration |#c.f3=0 and #c.f7=1 ) }
pred Pair565 { (some c: Configuration |#c.f3=0 and #c.f8=1 ) }
pred Pair566 { (some c: Configuration |#c.f3=0 and #c.f9=1) }
pred Pair567 { (some c: Configuration |#c.f3=0 and #c.f10=1) } 
pred Pair568 { (some c: Configuration |#c.f3=0 and #c.f11=1 ) }
pred Pair569 { (some c: Configuration |#c.f3=0 and #c.f12=1 ) }
pred Pair570 { (some c: Configuration |#c.f3=0 and #c.f13=1) }
pred Pair571 { (some c: Configuration |#c.f3=0 and #c.f14=1) } 
pred Pair572 { (some c: Configuration |#c.f3=0 and #c.f15=1 ) }
pred Pair573 { (some c: Configuration |#c.f3=0 and #c.f16=1 ) }
pred Pair574 { (some c: Configuration |#c.f3=0 and #c.f17=1) }
pred Pair575 { (some c: Configuration |#c.f3=0 and #c.f18=1) } 
pred Pair576 { (some c: Configuration |#c.f3=0 and #c.f19=1 ) }
pred Pair577 { (some c: Configuration |#c.f4=0 and #c.f5=1) }
pred Pair578 { (some c: Configuration |#c.f4=0 and #c.f6=1) } 
pred Pair579 { (some c: Configuration |#c.f4=0 and #c.f7=1 ) }
pred Pair580 { (some c: Configuration |#c.f4=0 and #c.f8=1 ) }
pred Pair581 { (some c: Configuration |#c.f4=0 and #c.f9=1) }
pred Pair582 { (some c: Configuration |#c.f4=0 and #c.f10=1) } 
pred Pair583 { (some c: Configuration |#c.f4=0 and #c.f11=1 ) }
pred Pair584 { (some c: Configuration |#c.f4=0 and #c.f12=1 ) }
pred Pair585 { (some c: Configuration |#c.f4=0 and #c.f13=1) }
pred Pair586 { (some c: Configuration |#c.f4=0 and #c.f14=1) } 
pred Pair587 { (some c: Configuration |#c.f4=0 and #c.f15=1 ) }
pred Pair588 { (some c: Configuration |#c.f4=0 and #c.f16=1 ) }
pred Pair589 { (some c: Configuration |#c.f4=0 and #c.f17=1) }
pred Pair590 { (some c: Configuration |#c.f4=0 and #c.f18=1) } 
pred Pair591 { (some c: Configuration |#c.f4=0 and #c.f19=1 ) }
pred Pair592 { (some c: Configuration |#c.f5=0 and #c.f6=1) } 
pred Pair593 { (some c: Configuration |#c.f5=0 and #c.f7=1 ) }
pred Pair594 { (some c: Configuration |#c.f5=0 and #c.f8=1 ) }
pred Pair595 { (some c: Configuration |#c.f5=0 and #c.f9=1) }
pred Pair596 { (some c: Configuration |#c.f5=0 and #c.f10=1) } 
pred Pair597 { (some c: Configuration |#c.f5=0 and #c.f11=1 ) }
pred Pair598 { (some c: Configuration |#c.f5=0 and #c.f12=1 ) }
pred Pair599 { (some c: Configuration |#c.f5=0 and #c.f13=1) }
pred Pair601 { (some c: Configuration |#c.f5=0 and #c.f14=1) } 
pred Pair602 { (some c: Configuration |#c.f5=0 and #c.f15=1 ) }
pred Pair603 { (some c: Configuration |#c.f5=0 and #c.f16=1 ) }
pred Pair604 { (some c: Configuration |#c.f5=0 and #c.f17=1) }
pred Pair605 { (some c: Configuration |#c.f5=0 and #c.f18=1) } 
pred Pair606 { (some c: Configuration |#c.f5=0 and #c.f19=1 ) }
pred Pair607 { (some c: Configuration |#c.f6=0 and #c.f7=1 ) }
pred Pair608 { (some c: Configuration |#c.f6=0 and #c.f8=1 ) }
pred Pair609 { (some c: Configuration |#c.f6=0 and #c.f9=1) }
pred Pair610 { (some c: Configuration |#c.f6=0 and #c.f10=1) } 
pred Pair611 { (some c: Configuration |#c.f6=0 and #c.f11=1 ) }
pred Pair612 { (some c: Configuration |#c.f6=0 and #c.f12=1 ) }
pred Pair613 { (some c: Configuration |#c.f6=0 and #c.f13=1) }
pred Pair614 { (some c: Configuration |#c.f6=0 and #c.f14=1) } 
pred Pair615 { (some c: Configuration |#c.f6=0 and #c.f15=1 ) }
pred Pair616 { (some c: Configuration |#c.f6=0 and #c.f16=1 ) }
pred Pair617 { (some c: Configuration |#c.f6=0 and #c.f17=1) }
pred Pair618 { (some c: Configuration |#c.f6=0 and #c.f18=1) } 
pred Pair619 { (some c: Configuration |#c.f6=0 and #c.f19=1 ) }
pred Pair620 { (some c: Configuration |#c.f7=0 and #c.f8=1) }
pred Pair621 { (some c: Configuration |#c.f7=0 and #c.f9=1) }
pred Pair622 { (some c: Configuration |#c.f7=0 and #c.f10=1) } 
pred Pair623 { (some c: Configuration |#c.f7=0 and #c.f11=1 ) }
pred Pair624 { (some c: Configuration |#c.f7=0 and #c.f12=1 ) }
pred Pair625 { (some c: Configuration |#c.f7=0 and #c.f13=1) }
pred Pair626 { (some c: Configuration |#c.f7=0 and #c.f14=1) } 
pred Pair627 { (some c: Configuration |#c.f7=0 and #c.f15=1 ) }
pred Pair628 { (some c: Configuration |#c.f7=0 and #c.f16=1 ) }
pred Pair629 { (some c: Configuration |#c.f7=0 and #c.f17=1) }
pred Pair630 { (some c: Configuration |#c.f7=0 and #c.f18=1) } 
pred Pair631 { (some c: Configuration |#c.f7=0 and #c.f19=1 ) }
pred Pair632 { (some c: Configuration |#c.f8=0 and #c.f9=1) }
pred Pair633 { (some c: Configuration |#c.f8=0 and #c.f10=1) } 
pred Pair634 { (some c: Configuration |#c.f8=0 and #c.f11=1 ) }
pred Pair635 { (some c: Configuration |#c.f8=0 and #c.f12=1 ) }
pred Pair636 { (some c: Configuration |#c.f8=0 and #c.f13=1) }
pred Pair637 { (some c: Configuration |#c.f8=0 and #c.f14=1) } 
pred Pair638 { (some c: Configuration |#c.f8=0 and #c.f15=1 ) }
pred Pair639 { (some c: Configuration |#c.f8=0 and #c.f16=1 ) }
pred Pair640 { (some c: Configuration |#c.f8=0 and #c.f17=1) }
pred Pair641 { (some c: Configuration |#c.f8=0 and #c.f18=1) } 
pred Pair642 { (some c: Configuration |#c.f8=0 and #c.f19=1 ) }
pred Pair643 { (some c: Configuration |#c.f9=0 and #c.f10=1) } 
pred Pair644 { (some c: Configuration |#c.f9=0 and #c.f11=1 ) }
pred Pair645 { (some c: Configuration |#c.f9=0 and #c.f12=1 ) }
pred Pair646 { (some c: Configuration |#c.f9=0 and #c.f13=1) }
pred Pair647 { (some c: Configuration |#c.f9=0 and #c.f14=1) } 
pred Pair648 { (some c: Configuration |#c.f9=0 and #c.f15=1 ) }
pred Pair649 { (some c: Configuration |#c.f9=0 and #c.f16=1 ) }
pred Pair650 { (some c: Configuration |#c.f9=0 and #c.f17=1) }
pred Pair651 { (some c: Configuration |#c.f9=0 and #c.f18=1) } 
pred Pair652 { (some c: Configuration |#c.f9=0 and #c.f19=1 ) }
pred Pair653 { (some c: Configuration |#c.f10=0 and #c.f11=1 ) }
pred Pair654 { (some c: Configuration |#c.f10=0 and #c.f12=1 ) }
pred Pair655 { (some c: Configuration |#c.f10=0 and #c.f13=1) }
pred Pair656 { (some c: Configuration |#c.f10=0 and #c.f14=1) } 
pred Pair657 { (some c: Configuration |#c.f10=0 and #c.f15=1 ) }
pred Pair658 { (some c: Configuration |#c.f10=0 and #c.f16=1 ) }
pred Pair659 { (some c: Configuration |#c.f10=0 and #c.f17=1) }
pred Pair660 { (some c: Configuration |#c.f10=0 and #c.f18=1) } 
pred Pair661 { (some c: Configuration |#c.f10=0 and #c.f19=1 ) }
pred Pair662 { (some c: Configuration |#c.f11=0 and #c.f12=1 ) }
pred Pair663 { (some c: Configuration |#c.f11=0 and #c.f13=1) }
pred Pair664 { (some c: Configuration |#c.f11=0 and #c.f14=1) } 
pred Pair665 { (some c: Configuration |#c.f11=0 and #c.f15=1 ) }
pred Pair666 { (some c: Configuration |#c.f11=0 and #c.f16=1 ) }
pred Pair667 { (some c: Configuration |#c.f11=0 and #c.f17=1) }
pred Pair668 { (some c: Configuration |#c.f11=0 and #c.f18=1) } 
pred Pair669 { (some c: Configuration |#c.f11=0 and #c.f19=1 ) }
pred Pair670 { (some c: Configuration |#c.f12=0 and #c.f13=1) }
pred Pair671 { (some c: Configuration |#c.f12=0 and #c.f14=1) } 
pred Pair672 { (some c: Configuration |#c.f12=0 and #c.f15=1 ) }
pred Pair673 { (some c: Configuration |#c.f12=0 and #c.f16=1 ) }
pred Pair674 { (some c: Configuration |#c.f12=0 and #c.f17=1) }
pred Pair675 { (some c: Configuration |#c.f12=0 and #c.f18=1) } 
pred Pair676 { (some c: Configuration |#c.f12=0 and #c.f19=1 ) }
pred Pair677 { (some c: Configuration |#c.f13=0 and #c.f14=1) } 
pred Pair678 { (some c: Configuration |#c.f13=0 and #c.f15=1 ) }
pred Pair679 { (some c: Configuration |#c.f13=0 and #c.f16=1 ) }
pred Pair680 { (some c: Configuration |#c.f13=0 and #c.f17=1) }
pred Pair681 { (some c: Configuration |#c.f13=0 and #c.f18=1) } 
pred Pair682 { (some c: Configuration |#c.f13=0 and #c.f19=1 ) }
pred Pair683 { (some c: Configuration |#c.f14=0 and #c.f15=1 ) }
pred Pair684 { (some c: Configuration |#c.f14=0 and #c.f16=1 ) }
pred Pair685 { (some c: Configuration |#c.f14=0 and #c.f17=1) }
pred Pair686 { (some c: Configuration |#c.f14=0 and #c.f18=1) } 
pred Pair687 { (some c: Configuration |#c.f14=0 and #c.f19=1 ) }
pred Pair688 { (some c: Configuration |#c.f15=0 and #c.f16=1 ) }
pred Pair689 { (some c: Configuration |#c.f15=0 and #c.f17=1) }
pred Pair690 { (some c: Configuration |#c.f15=0 and #c.f18=1) } 
pred Pair691 { (some c: Configuration |#c.f15=0 and #c.f19=1 ) }
pred Pair692 { (some c: Configuration |#c.f16=0 and #c.f17=1) }
pred Pair693 { (some c: Configuration |#c.f16=0 and #c.f18=1) } 
pred Pair694 { (some c: Configuration |#c.f16=0 and #c.f19=1 ) }
pred Pair695 { (some c: Configuration |#c.f17=0 and #c.f18=1) } 
pred Pair696 { (some c: Configuration |#c.f17=0 and #c.f19=1 ) }
pred Pair697 { (some c: Configuration |#c.f18=0 and #c.f19=1 ) }


//PairWise

pred PairWise
{
Pair1 and 
Pair2 and 
Pair3 and 
Pair4 and 
Pair5 and 
Pair6 and 
Pair7 and 
Pair8 and 
Pair9 and 
Pair10 and 
Pair11 and 
Pair12 and 
Pair13 and 
Pair14 and 
Pair15 and 
Pair16 and 
Pair17 and 
Pair18 and 
Pair19 and 
Pair20 and 
Pair21 and 
Pair22 and 
Pair23 and 
Pair24 and 
Pair25 and 
Pair26 and 
Pair27 and 
Pair28 and 
Pair29 and 
Pair30 and 
Pair31 and 
Pair32 and 
Pair33 and 
Pair34 and 
Pair35 and 
Pair36 and 
Pair37 and 
Pair38 and 
Pair39 and 
Pair40 and 
Pair41 and 
Pair42 and 
Pair43 and 
Pair44 and 
Pair45 and 
Pair46 and 
Pair47 and 
Pair48 and 
Pair49 and 
Pair50 and 
Pair51 and 
Pair52 and 
Pair53 and 
Pair54 and 
Pair55 and 
Pair56 and 
Pair57 and 
Pair58 and 
Pair59 and 
Pair60 and 
Pair61 and 
Pair62 and 
Pair63 and 
Pair64 and 
Pair65 and 
Pair66 and 
Pair67 and 
Pair68 and 
Pair69 and 
Pair70 and 
Pair71 and 
Pair72 and 
Pair73 and 
Pair74 and 
Pair75 and 
Pair76 and 
Pair77 and 
Pair78 and 
Pair79 and 
Pair80 and 
//Pair81 and 
Pair82 and 
//Pair83 and 
Pair84 and 
Pair85 and 
Pair86 and 
Pair87 and 
Pair88 and 
Pair89 and 
Pair90 and 
Pair91 and 
Pair92 and 
Pair93 and 
Pair94 and 
Pair95 and 
Pair96 and 
Pair97 and 
Pair98 and 
Pair99 and 
Pair100 and 
Pair101 and 
Pair102 and 
Pair103 and 
Pair104 and 
Pair105 and 
Pair106 and 
Pair107 and 
Pair108 and 
Pair109 and 
Pair110 and 
Pair111 and 
Pair112 and 
Pair113 and 
Pair114 and 
Pair115 and 
Pair116 and 
Pair117 and 
Pair118 and 
Pair119 and 
Pair120 and 
Pair121 and 
Pair122 and 
Pair123 and 
Pair124 and 
Pair125 and 
Pair126 and 
Pair127 and 
Pair128 and 
Pair129 and 
Pair130 and 
Pair131 and 
Pair132 and 
Pair133 and 
Pair134 and 
Pair135 and 
Pair136 and 
Pair137 and 
Pair138 and 
Pair139 and 
Pair140 and 
Pair141 and 
Pair142 and 
Pair143 and 
Pair144 and 
Pair145 and 
Pair146 and 
Pair147 and 
Pair148 and 
Pair149 and 
Pair150 and 
Pair151 and 
Pair152 and 
Pair153 and 
Pair154 and 
Pair155 and 
Pair156 and 
Pair157 and 
Pair158 and 
Pair159 and 
Pair160 and 
Pair161 and 
Pair162 and 
Pair163 and 
Pair164 and 
Pair165 and 
Pair166 and 
Pair167 and 
Pair168 and 
Pair169 and 
Pair170 and 
Pair171 and 
/*
Pair172 and 
Pair173 and 
Pair174 and 
Pair175 and 
Pair176 and 
Pair177 and 
Pair178 and 
Pair179 and 
Pair180 and 
Pair181 and 
Pair182 and 
Pair183 and 
Pair184 and 
Pair185 and 
Pair186 and 
Pair187 and 
Pair188 and 
Pair189 and 
Pair190 and 
Pair191 and 
Pair192 and*/
Pair193 and 
Pair194 and 
Pair195 and 
Pair196 and 
//Pair197 and
Pair198 and 
Pair199 and 
Pair200 and 
Pair201 and 
Pair202 and 
//Pair203 and 
Pair204 and 
/*
Pair205 and 
Pair206 and 
Pair207 and 
Pair208 and 
Pair209 and 
Pair210 and 
Pair211 and 
Pair212 and 
Pair213 and 
Pair214 and 
Pair215 and 
Pair216 and 
Pair217 and 
Pair218 and 
Pair219 and 
Pair220 and 
Pair221 and 
Pair222 and 
Pair223 and 
Pair224 and 
Pair225 and 
Pair226 and 
Pair227 and 
Pair228 and 
Pair229 and 
Pair230 and 
Pair231 and 
Pair232 and 
Pair233 and 
Pair234 and 
Pair235 and 
Pair236 and 
Pair237 and 
Pair238 and 
Pair239 and 
Pair240 and 
Pair241 and 
Pair242 and 
Pair243 and 
Pair244 and 
Pair245 and 
Pair246 and 
Pair247 and 
Pair248 and 
Pair249 and 
Pair250 and 
Pair251 and */
Pair252 and 
Pair253 and 
Pair254 and 
//Pair255 and 
Pair256 and 
Pair257 and 
Pair258 and 
Pair259 and 
Pair260 and 
//Pair261 and 
Pair262 and 
//Pair263 and 
//Pair264 and 
Pair265 and 
Pair266 and 
//Pair267 and 
Pair268 and 
Pair269 and 
Pair270 and 
Pair271 and 
Pair272 and 
//Pair273 and 
Pair274 and 
//Pair275 and 
//Pair276 and 
Pair277 and 
//Pair278 and 
Pair279 and 
Pair280 and 
Pair281 and 
Pair282 and 
Pair283 and 
//Pair284 and 
Pair285 and 
//Pair286 and 
//Pair287 and 
//Pair288 and 
Pair289 and 
Pair290 and 
Pair291 and 
Pair292 and 
Pair293 and 
//Pair294 and 
Pair295 and 
/*
Pair296 and 
Pair297 and 
Pair298 and 
Pair299 and*/ 
//Pair300 and 
/*
Pair301 and 
Pair302 and 
Pair303 and 
Pair304 and 
Pair305 and 
Pair306 and 
Pair307 and*/ 
Pair308 and 
Pair309 and 
Pair310 and 
Pair311 and 
//Pair312 and 
Pair313 and 
//Pair314 and 
//Pair315 and 
Pair316 and 
Pair317 and 
Pair318 and 
//Pair319 and 
//Pair320 and 
//Pair321 and 
//Pair322 and 
//Pair323 and 
//Pair324 and 
//Pair325 and 
//Pair326 and 
//Pair327 and 
//Pair328 and 
//Pair329 and 
Pair330 and 
//Pair331 and 
//Pair332 and 
Pair333 and 
Pair334 and 
//Pair335 and 
Pair336 and 
//Pair337 and 
//Pair338 and 
Pair339 and 
//Pair340 and 
Pair341 and 
/*
Pair342 and 
Pair343 and 
Pair344 and 
Pair345 and 
Pair346 and 
Pair347 and 
Pair348 and 
Pair349 and 
Pair350 and 
Pair351 and 
Pair352 and 
Pair353 and*/ 
Pair354 and 
//Pair355 and 
//Pair356 and 
//Pair357 and 
Pair358 and 
Pair359 and 
Pair360 and 
Pair361 and 
//Pair362 and 
Pair363 and 
Pair364 and 
Pair365 and 
Pair366 and 
Pair367 and 
//Pair368 and 
Pair369 and 
/*
Pair370 and 
Pair371 and 
Pair372 and 
Pair373 and 
Pair374 and */
Pair375 and 
Pair376 and 
Pair377 and 
Pair378 and 
//Pair379 and 
Pair380 and 
Pair381 and 
Pair382 and 
Pair383 and 
Pair384 and 
//Pair385 and 
Pair386 and 
/*
Pair387 and 
Pair388 and 
Pair389 and 
Pair390 and*/ 
Pair391 and 
Pair392 and 
Pair393 and 
Pair394 and 
//Pair395 and 
Pair396 and 
Pair397 and 
//Pair398 and 
//Pair399 and 
Pair400 and 
Pair401 and 
//Pair402 and 
Pair403 and 
//Pair404 and 
//Pair405 and 
//Pair406 and 
Pair407 and 
Pair408 and 
Pair409 and 
Pair410 and 
//Pair411 and 
Pair412 and 
Pair413 and 
Pair414 and 
Pair415 and 
Pair416 and 
//Pair417 and 
Pair418 and 
//Pair419 and 
//Pair420 and 
Pair421 and 
Pair422 and 
Pair423 and 
Pair424 and 
//Pair425 and 
Pair426 and 
Pair427 and 
Pair428 and 
Pair429 and 
Pair430 and 
//Pair431 and 
Pair432 and 
//Pair433 and 
//Pair434 and 
Pair435 and 
Pair436 and 
Pair437 and 
//Pair438 and 
Pair439 and 
Pair440 and 
Pair441 and 
Pair442 and 
Pair443 and 
//Pair444 and 
Pair445 and 
//Pair446 and 
//Pair447 and 
Pair448 and 
//Pair449 and 
//Pair450 and 
Pair451 and 
Pair452 and 
Pair453 and 
Pair454 and 
Pair455 and 
//Pair456 and 
Pair457 and 
//Pair458 and 
//Pair459 and 
Pair460 and 
//Pair461 and 
Pair462 and 
Pair463 and 
Pair464 and 
Pair465 and 
Pair466 and 
//Pair467 and 
Pair468 and 
//Pair469 and 
//Pair470 and 
//Pair471 and 
Pair472 and 
Pair473 and 
Pair474 and 
Pair475 and 
Pair476 and 
//Pair477 and 
Pair478 and 
//Pair479 and 
//Pair480 and 
Pair481 and 
Pair482 and 
Pair483 and 
Pair484 and 
Pair485 and 
//Pair486 and 
Pair487 and 
//Pair488 and 
//Pair489 and 
Pair490 and 
Pair491 and 
Pair492 and 
Pair493 and 
//Pair494 and 
Pair495 and 
//Pair496 and 
//Pair497 and 
Pair498 and 
Pair499 and 
Pair500 and 
//Pair501 and 
Pair502 and 
//Pair503 and 
//Pair504 and 
Pair505 and 
Pair506 and 
//Pair507 and 
Pair508 and 
//Pair509 and 
//Pair510 and 
Pair511 and 
//Pair512 and 
Pair513 and 
/*
Pair514 and 
Pair515 and 
Pair516 and*/ 
Pair517 and 
//Pair518 and 
//Pair519 and 
Pair520 and 
/*
Pair521 and 
Pair522 and 
Pair523 and 
Pair524 and 
Pair525 and 
Pair526 and 
Pair527 and 
Pair528 and 
Pair529 and 
Pair530 and 
Pair531 and 
Pair532 and*/ 
Pair533 and 
Pair534 and 
Pair535 and 
/*
Pair536 and 
Pair537 and 
Pair538 and 
Pair539 and 
Pair540 and 
Pair541 and 
Pair542 and 
Pair543 and*/ 
Pair544 and 
Pair545 and 
Pair546 and 
Pair547 and 
Pair548 and 
Pair549 and 
Pair550 and 
Pair551 and 
Pair552 and 
Pair553 and 
Pair554 and 
Pair555 and 
Pair556 and 
Pair557 and 
Pair558 and 
Pair559 and 
Pair560 and 
/*
Pair561 and 
Pair562 and 
Pair563 and 
Pair564 and 
Pair565 and 
Pair566 and 
Pair567 and 
Pair568 and 
Pair569 and 
Pair570 and 
Pair571 and 
Pair572 and 
Pair573 and 
Pair574 and 
Pair575 and 
Pair576 and 
Pair577 and 
Pair578 and 
Pair579 and 
Pair580 and 
Pair581 and 
Pair582 and 
Pair583 and 
Pair584 and 
Pair585 and 
Pair586 and 
Pair587 and 
Pair588 and 
Pair589 and 
Pair590 and 
Pair591 and 
Pair592 and 
Pair593 and 
Pair594 and 
Pair595 and 
Pair596 and 
Pair597 and 
Pair598 and 
Pair599 and 
Pair600 and 
Pair601 and 
Pair602 and 
Pair603 and 
Pair604 and 
Pair605 and 
Pair606 and*/ 
Pair607 and 
Pair608 and 
Pair609 and 
Pair610 and 
Pair611 and 
Pair612 and 
Pair613 and 
Pair614 and 
Pair615 and 
Pair616 and 
Pair617 and 
Pair618 and 
Pair619 and 
Pair620 and 
Pair621 and 
Pair622 and 
Pair623 and 
Pair624 and 
Pair625 and 
Pair626 and 
Pair627 and 
Pair628 and 
Pair629 and 
Pair630 and 
Pair631 and 
Pair632 and 
Pair633 and 
Pair634 and 
Pair635 and 
Pair636 and 
Pair637 and 
Pair638 and 
Pair639 and 
Pair640 and 
Pair641 and 
Pair642 and 
Pair643 and 
Pair644 and 
Pair645 and 
Pair646 and 
Pair647 and 
Pair648 and 
Pair649 and 
Pair650 and 
Pair651 and 
Pair652 and 
/*
Pair653 and 
Pair654 and 
Pair655 and 
Pair656 and 
Pair657 and 
Pair658 and 
Pair659 and 
Pair660 and 
Pair661 and*/ 
Pair662 and 
Pair663 and 
Pair664 and 
Pair665 and 
Pair666 and 
Pair667 and 
Pair668 and 
Pair669 and 
Pair670 and 
Pair671 and 
Pair672 and 
Pair673 and 
Pair674 and 
Pair675 and 
Pair676 and 
Pair677 and 
Pair678 and 
Pair679 and 
Pair680 and 
Pair681 and 
Pair682 and 
Pair683 and 
Pair684 and 
Pair685 and 
Pair686 and 
Pair687 and 
Pair688 and 
Pair689 and 
Pair690 and 
Pair691 and 
/*
Pair692 and 
Pair693 and 
Pair694 and*/ 
Pair695 and 
Pair696
}

//Strategy 1 (All Features in all Product Configurations)
//run atleastOneFeatureInConfigs for 30
//Strategy 2 (All Branches of DFT in all Configurations)
//run allDFTBranchesInAllConfigs for 30
//Strategy 3 (All Branches of DFT in Diff Configurations)
//run allDFTBranchesInDiffConfigs for 30
//Strategy 4 (Pair Wise for 681 pairs)
run PairWise for 15
//Detecting Valid Pairs

/*
run Pair1 for 45
run Pair2 for 45
run Pair3 for 45
run Pair4 for 45
run Pair5 for 45
run Pair6 for 45
run Pair7 for 45
run Pair8 for 45
run Pair9 for 45
run Pair10 for 45
run Pair11 for 45
run Pair12 for 45
run Pair13 for 45
run Pair14 for 45
run Pair15 for 45
run Pair16 for 45
run Pair17 for 45
run Pair18 for 45
run Pair19 for 45
run Pair20 for 45
run Pair21 for 45
run Pair22 for 45
run Pair23 for 45
run Pair24 for 45
run Pair25 for 45
run Pair26 for 45
run Pair27 for 45
run Pair28 for 45
run Pair29 for 45
run Pair30 for 45
run Pair31 for 45
run Pair32 for 45
run Pair33 for 45
run Pair34 for 45
run Pair35 for 45
run Pair36 for 45
run Pair37 for 45
run Pair38 for 45
run Pair39 for 45
run Pair40 for 45
run Pair41 for 45
run Pair42 for 45
run Pair43 for 45
run Pair44 for 45
run Pair45 for 45
run Pair46 for 45
run Pair47 for 45
run Pair48 for 45
run Pair49 for 45
run Pair50 for 45
run Pair51 for 45
run Pair52 for 45
run Pair53 for 45
run Pair54 for 45
run Pair55 for 45
run Pair56 for 45
run Pair57 for 45
run Pair58 for 45
run Pair59 for 45
run Pair60 for 45
run Pair61 for 45
run Pair62 for 45
run Pair63 for 45
run Pair64 for 45
run Pair65 for 45
run Pair66 for 45
run Pair67 for 45
run Pair68 for 45
run Pair69 for 45
run Pair70 for 45
run Pair71 for 45
run Pair72 for 45
run Pair73 for 45
run Pair74 for 45
run Pair75 for 45
run Pair76 for 45
run Pair77 for 45
run Pair78 for 45
run Pair79 for 45
run Pair80 for 45
run Pair81 for 45
run Pair82 for 45
run Pair83 for 45
run Pair84 for 45
run Pair85 for 45
run Pair86 for 45
run Pair87 for 45
run Pair88 for 45
run Pair89 for 45
run Pair90 for 45
run Pair91 for 45
run Pair92 for 45
run Pair93 for 45
run Pair94 for 45
run Pair95 for 45
run Pair96 for 45
run Pair97 for 45
run Pair98 for 45
run Pair99 for 45
run Pair100 for 45
run Pair101 for 45
run Pair102 for 45
run Pair103 for 45
run Pair104 for 45
run Pair105 for 45
run Pair106 for 45
run Pair107 for 45
run Pair108 for 45
run Pair109 for 45
run Pair110 for 45
run Pair111 for 45
run Pair112 for 45
run Pair113 for 45
run Pair114 for 45
run Pair115 for 45
run Pair116 for 45
run Pair117 for 45
run Pair118 for 45
run Pair119 for 45
run Pair120 for 45
run Pair121 for 45
run Pair122 for 45
run Pair123 for 45
run Pair124 for 45
run Pair125 for 45
run Pair126 for 45
run Pair127 for 45
run Pair128 for 45
run Pair129 for 45
run Pair130 for 45
run Pair131 for 45
run Pair132 for 45
run Pair133 for 45
run Pair134 for 45
run Pair135 for 45
run Pair136 for 45
run Pair137 for 45
run Pair138 for 45
run Pair139 for 45
run Pair140 for 45
run Pair141 for 45
run Pair142 for 45
run Pair143 for 45
run Pair144 for 45
run Pair145 for 45
run Pair146 for 45
run Pair147 for 45
run Pair148 for 45
run Pair149 for 45
run Pair150 for 45
run Pair151 for 45
run Pair152 for 45
run Pair153 for 45
run Pair154 for 45
run Pair155 for 45
run Pair156 for 45
run Pair157 for 45
run Pair158 for 45
run Pair159 for 45
run Pair160 for 45
run Pair161 for 45
run Pair162 for 45
run Pair163 for 45
run Pair164 for 45
run Pair165 for 45
run Pair166 for 45
run Pair167 for 45
run Pair168 for 45
run Pair169 for 45
run Pair170 for 45
run Pair171 for 45
run Pair172 for 45
run Pair173 for 45
run Pair174 for 45
run Pair175 for 45
run Pair176 for 45
run Pair177 for 45
run Pair178 for 45
run Pair179 for 45
run Pair180 for 45
run Pair181 for 45
run Pair182 for 45
run Pair183 for 45
run Pair184 for 45
run Pair185 for 45
run Pair186 for 45
run Pair187 for 45
run Pair188 for 45
run Pair189 for 45
run Pair190 for 45
run Pair191 for 45
run Pair192 for 45
run Pair193 for 45
run Pair194 for 45
run Pair195 for 45
run Pair196 for 45
run Pair197 for 45
run Pair198 for 45
run Pair199 for 45
run Pair200 for 45
run Pair201 for 45
run Pair202 for 45
run Pair203 for 45
run Pair204 for 45
run Pair205 for 45
run Pair206 for 45
run Pair207 for 45
run Pair208 for 45
run Pair209 for 45
run Pair210 for 45
run Pair211 for 45
run Pair212 for 45
run Pair213 for 45
run Pair214 for 45
run Pair215 for 45
run Pair216 for 45
run Pair217 for 45
run Pair218 for 45
run Pair219 for 45
run Pair220 for 45
run Pair221 for 45
run Pair222 for 45
run Pair223 for 45
run Pair224 for 45
run Pair225 for 45
run Pair226 for 45
run Pair227 for 45
run Pair228 for 45
run Pair229 for 45
run Pair230 for 45
run Pair231 for 45
run Pair232 for 45
run Pair233 for 45
run Pair234 for 45
run Pair235 for 45
run Pair236 for 45
run Pair237 for 45
run Pair238 for 45
run Pair239 for 45
run Pair240 for 45
run Pair241 for 45
run Pair242 for 45
run Pair243 for 45
run Pair244 for 45
run Pair245 for 45
run Pair246 for 45
run Pair247 for 45
run Pair248 for 45
run Pair249 for 45
run Pair250 for 45
run Pair251 for 45
run Pair252 for 45
run Pair253 for 45
run Pair254 for 45
run Pair255 for 45
run Pair256 for 45
run Pair257 for 45
run Pair258 for 45
run Pair259 for 45
run Pair260 for 45
run Pair261 for 45
run Pair262 for 45
run Pair263 for 45
run Pair264 for 45
run Pair265 for 45
run Pair266 for 45
run Pair267 for 45
run Pair268 for 45
run Pair269 for 45
run Pair270 for 45
run Pair271 for 45
run Pair272 for 45
run Pair273 for 45
run Pair274 for 45
run Pair275 for 45
run Pair276 for 45
run Pair277 for 45
run Pair278 for 45
run Pair279 for 45
run Pair280 for 45
run Pair281 for 45
run Pair282 for 45
run Pair283 for 45
run Pair284 for 45
run Pair285 for 45
run Pair286 for 45
run Pair287 for 45
run Pair288 for 45
run Pair289 for 45
run Pair290 for 45
run Pair291 for 45
run Pair292 for 45
run Pair293 for 45
run Pair294 for 45
run Pair295 for 45
run Pair296 for 45
run Pair297 for 45
run Pair298 for 45
run Pair299 for 45
//run Pair300 for 45
run Pair301 for 45
run Pair302 for 45
run Pair303 for 45
run Pair304 for 45
run Pair305 for 45
run Pair306 for 45
run Pair307 for 45
run Pair308 for 45
run Pair309 for 45
run Pair310 for 45
run Pair311 for 45
run Pair312 for 45
run Pair313 for 45
run Pair314 for 45
run Pair315 for 45
run Pair316 for 45
run Pair317 for 45
run Pair318 for 45
//run Pair319 for 45
//run Pair320 for 45
//run Pair321 for 45
//run Pair322 for 45
//run Pair323 for 45
//run Pair324 for 45
//run Pair325 for 45
//run Pair326 for 45
//run Pair327 for 45
//run Pair328 for 45
run Pair329 for 45
run Pair330 for 45
run Pair331 for 45
run Pair332 for 45
run Pair333 for 45
run Pair334 for 45
run Pair335 for 45
run Pair336 for 45
run Pair337 for 45
run Pair338 for 45
run Pair339 for 45
run Pair340 for 45
run Pair341 for 45
run Pair342 for 45
run Pair343 for 45
run Pair344 for 45
run Pair345 for 45
run Pair346 for 45
run Pair347 for 45
run Pair348 for 45
run Pair349 for 45
run Pair350 for 45
run Pair351 for 45
run Pair352 for 45
run Pair353 for 45
run Pair354 for 45
run Pair355 for 45
run Pair356 for 45
run Pair357 for 45
run Pair358 for 45
run Pair359 for 45
run Pair360 for 45
run Pair361 for 45
run Pair362 for 45
run Pair363 for 45
run Pair364 for 45
run Pair365 for 45
run Pair366 for 45
run Pair367 for 45
run Pair368 for 45
run Pair369 for 45
run Pair370 for 45
run Pair371 for 45
run Pair372 for 45
run Pair373 for 45
run Pair374 for 45
run Pair375 for 45
run Pair376 for 45
run Pair377 for 45
run Pair378 for 45
run Pair379 for 45
run Pair380 for 45
run Pair381 for 45
run Pair382 for 45
run Pair383 for 45
run Pair384 for 45
run Pair385 for 45
run Pair386 for 45
run Pair387 for 45
run Pair388 for 45
run Pair389 for 45
run Pair390 for 45
run Pair391 for 45
run Pair392 for 45
run Pair393 for 45
run Pair394 for 45
run Pair395 for 45
run Pair396 for 45
run Pair397 for 45
//run Pair398 for 45
//run Pair399 for 45
run Pair400 for 45
run Pair401 for 45
run Pair402 for 45
run Pair403 for 45
run Pair404 for 45
run Pair405 for 45
run Pair406 for 45
run Pair407 for 45
run Pair408 for 45
run Pair409 for 45
run Pair410 for 45
run Pair411 for 45
run Pair412 for 45
run Pair413 for 45
run Pair414 for 45
run Pair415 for 45
run Pair416 for 45
run Pair417 for 45
run Pair418 for 45
run Pair419 for 45
run Pair420 for 45
run Pair421 for 45
run Pair422 for 45
run Pair423 for 45
run Pair424 for 45
run Pair425 for 45
run Pair426 for 45
run Pair427 for 45
run Pair428 for 45
run Pair429 for 45
run Pair430 for 45
run Pair431 for 45
run Pair432 for 45
run Pair433 for 45
run Pair434 for 45
run Pair435 for 45
run Pair436 for 45
run Pair437 for 45
run Pair438 for 45
run Pair439 for 45
run Pair440 for 45
run Pair441 for 45
run Pair442 for 45
run Pair443 for 45
run Pair444 for 45
run Pair445 for 45
run Pair446 for 45
run Pair447 for 45
run Pair448 for 45
run Pair449 for 45
run Pair450 for 45
run Pair451 for 45
run Pair452 for 45
run Pair453 for 45
run Pair454 for 45
run Pair455 for 45
run Pair456 for 45
run Pair457 for 45
run Pair458 for 45
run Pair459 for 45
run Pair460 for 45
run Pair461 for 45
run Pair462 for 45
run Pair463 for 45
run Pair464 for 45
run Pair465 for 45
run Pair466 for 45
run Pair467 for 45
run Pair468 for 45
run Pair469 for 45
run Pair470 for 45
run Pair471 for 45
run Pair472 for 45
run Pair473 for 45
run Pair474 for 45
run Pair475 for 45
run Pair476 for 45
run Pair477 for 45
run Pair478 for 45
run Pair479 for 45
run Pair480 for 45
run Pair481 for 45
run Pair482 for 45
run Pair483 for 45
run Pair484 for 45
run Pair485 for 45
run Pair486 for 45
run Pair487 for 45
run Pair488 for 45
run Pair489 for 45
run Pair490 for 45
run Pair491 for 45
run Pair492 for 45
run Pair493 for 45
run Pair494 for 45
run Pair495 for 45
run Pair496 for 45
run Pair497 for 45
run Pair498 for 45
run Pair499 for 45
run Pair500 for 45
run Pair501 for 45
run Pair502 for 45
run Pair503 for 45
run Pair504 for 45
run Pair505 for 45
run Pair506 for 45
run Pair507 for 45
run Pair508 for 45
run Pair509 for 45
run Pair510 for 45
run Pair511 for 45
run Pair512 for 45
run Pair513 for 45
run Pair514 for 45
run Pair515 for 45
run Pair516 for 45
run Pair517 for 45
run Pair518 for 45
run Pair519 for 45
run Pair520 for 45
run Pair521 for 45
run Pair522 for 45
run Pair523 for 45
run Pair524 for 45
run Pair525 for 45
run Pair526 for 45
run Pair527 for 45
run Pair528 for 45
run Pair529 for 45
run Pair530 for 45
run Pair531 for 45
run Pair532 for 45
run Pair533 for 45
run Pair534 for 45
run Pair535 for 45
run Pair536 for 45
run Pair537 for 45
run Pair538 for 45
run Pair539 for 45
run Pair540 for 45
run Pair541 for 45
run Pair542 for 45
run Pair543 for 45
run Pair544 for 45
run Pair545 for 45
run Pair546 for 45
run Pair547 for 45
run Pair548 for 45
run Pair549 for 45
run Pair550 for 45
run Pair551 for 45
run Pair552 for 45
run Pair553 for 45
run Pair554 for 45
run Pair555 for 45
run Pair556 for 45
run Pair557 for 45
run Pair558 for 45
run Pair559 for 45
run Pair560 for 45
run Pair561 for 45
run Pair562 for 45
run Pair563 for 45
run Pair564 for 45
run Pair565 for 45
run Pair566 for 45
run Pair567 for 45
run Pair568 for 45
run Pair569 for 45
run Pair570 for 45
run Pair571 for 45
run Pair572 for 45
run Pair573 for 45
run Pair574 for 45
run Pair575 for 45
run Pair576 for 45
run Pair577 for 45
run Pair578 for 45
run Pair579 for 45
run Pair580 for 45
run Pair581 for 45
run Pair582 for 45
run Pair583 for 45
run Pair584 for 45
run Pair585 for 45
run Pair586 for 45
run Pair587 for 45
run Pair588 for 45
run Pair589 for 45
run Pair590 for 45
run Pair591 for 45
run Pair592 for 45
run Pair593 for 45
run Pair594 for 45
run Pair595 for 45
run Pair596 for 45
run Pair597 for 45
run Pair598 for 45
run Pair599 for 45
//run Pair600 for 45
run Pair601 for 45
run Pair602 for 45
run Pair603 for 45
run Pair604 for 45
run Pair605 for 45
run Pair606 for 45
run Pair607 for 45
run Pair608 for 45
run Pair609 for 45
run Pair610 for 45
run Pair611 for 45
run Pair612 for 45
run Pair613 for 45
run Pair614 for 45
run Pair615 for 45
run Pair616 for 45
run Pair617 for 45
run Pair618 for 45
run Pair619 for 45
run Pair620 for 45
run Pair621 for 45
run Pair622 for 45
run Pair623 for 45
run Pair624 for 45
run Pair625 for 45
run Pair626 for 45
run Pair627 for 45
run Pair628 for 45
run Pair629 for 45
run Pair630 for 45
run Pair631 for 45
run Pair632 for 45
run Pair633 for 45
run Pair634 for 45
run Pair635 for 45
run Pair636 for 45
run Pair637 for 45
run Pair638 for 45
run Pair639 for 45
run Pair640 for 45
run Pair641 for 45
run Pair642 for 45
run Pair643 for 45
run Pair644 for 45
run Pair645 for 45
run Pair646 for 45
run Pair647 for 45
run Pair648 for 45
run Pair649 for 45
run Pair650 for 45
run Pair651 for 45
run Pair652 for 45
run Pair653 for 45
run Pair654 for 45
run Pair655 for 45
run Pair656 for 45
run Pair657 for 45
run Pair658 for 45
run Pair659 for 45
run Pair660 for 45
run Pair661 for 45
run Pair662 for 45
run Pair663 for 45
run Pair664 for 45
run Pair665 for 45
run Pair666 for 45
run Pair667 for 45
run Pair668 for 45
run Pair669 for 45
run Pair670 for 45
run Pair671 for 45
run Pair672 for 45
run Pair673 for 45
run Pair674 for 45
run Pair675 for 45
run Pair676 for 45
run Pair677 for 45
run Pair678 for 45
run Pair679 for 45
run Pair680 for 45
run Pair681 for 45
run Pair682 for 45
run Pair683 for 45
run Pair684 for 45
run Pair685 for 45
run Pair686 for 45
run Pair687 for 45
run Pair688 for 45
run Pair689 for 45
run Pair690 for 45
run Pair691 for 45
run Pair692 for 45
run Pair693 for 45
run Pair694 for 45
run Pair695 for 45
run Pair696 for 45
*/
