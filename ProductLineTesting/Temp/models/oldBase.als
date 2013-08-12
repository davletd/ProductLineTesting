module TransactionFeatureModel



one sig ProductConfigurations
{	
	configurations : set Configuration
}



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



pred Tuple1 { #f1= 1 and #f2= 1  } 

run Tuple11

pred Tuple1 { #f1= 1 and #f2= 1  } 

run Tuple11

pred Tuple1 { #f1= 1 and #f2= 1  } 

run Tuple1 for 1

pred Tuple1 { #f1= 1 and #f2= 1  } 

run Tuple1 for 1
