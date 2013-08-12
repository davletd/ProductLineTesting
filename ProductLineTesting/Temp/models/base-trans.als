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


