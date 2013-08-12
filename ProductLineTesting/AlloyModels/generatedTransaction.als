
module TransactionModel

one sig ProductConfigurations
{	
	configurations : set Configuration
}

sig Configuration
{
f1: one Transaction,
f2: lone Nested,
f3: one Recovering,
f4: one ConncurrencyControlStrategy,
f5: one PhysicalLogging,
f6: lone TwoPhaseLocking,
f7: lone OptimisticValidation,
f8: lone Checkpointing,
f9: lone Deferring,
f10: one OutcomeAware,
f11: lone Checkpointable,
f12: lone Tracing,
f13: one Context,
f14: lone Copyable,
f15: lone Traceable,
f16: one Shared,
f17: lone SemanticClassified,
f18: one AccessClassified,
f19: one Lockable,
}

sig Transaction{}
sig Nested{}
sig Recovering{}
sig ConncurrencyControlStrategy{}
sig PhysicalLogging{}
sig TwoPhaseLocking{}
sig OptimisticValidation{}
sig Checkpointing{}
sig Deferring{}
sig OutcomeAware{}
sig Checkpointable{}
sig Tracing{}
sig Context{}
sig Copyable{}
sig Traceable{}
sig Shared{}
sig SemanticClassified{}
sig AccessClassified{}
sig Lockable{}

fact Configuration_cardinality
{}

fact Configuration_container
{
	all c : Configuration | c in ProductConfigurations.configurations
}

//Constraints due to require and exclude

// TwoPhaseLocking excludes Deferring
fact Invariant_1
{
	all c:Configuration | #c.f6==1 implies (#c.f9=0)
}

// OptimisticValidation requires Deferring
fact Invariant_2
{
	all c:Configuration | #c.f7==1 implies (#c.f9=1)
}   

// Traceable requires SemanticClassified
fact Invariant_3
{
	all c:Configuration | #c.f15==1 implies (#c.f17=1)
}   

// Constraints due to the Operators
// Transaction And Operator =>  Recovering AND  ConncurrencyControlStrategy AND  Shared AND   
fact Invariant_Opreator_1
{
	all c:Configuration | #c.f1==1 implies ( #c.f3=1 and  #c.f4=1 and  #c.f16=1)
}   
// Nested Optional condition   
fact Invariant_Opreator_2
{
	all c:Configuration | #c.f2==1 implies ( #c.f1=1)
}   
// Nested And Operator =>  Context AND   
fact Invariant_Opreator_3
{
	all c:Configuration | #c.f2==1 implies ( #c.f13=1)
}   
// Recovering And Operator =>  PhysicalLogging AND  OutcomeAware AND   
fact Invariant_Opreator_4
{
	all c:Configuration | #c.f3==1 implies ( #c.f5=1 and  #c.f10=1)
}   
// ConncurrencyControlStrategy XOR Operator =>  TwoPhaseLocking XOR  OptimisticValidation XOR   
fact Invariant_Opreator_5
{
	all c:Configuration | #c.f4==1 implies ( ( #c.f6 +  #c.f7 +  0)==1)
}   
// PhysicalLogging XOR Operator =>  Checkpointing XOR  Deferring XOR   
fact Invariant_Opreator_6
{
	all c:Configuration | #c.f5==1 implies ( ( #c.f8 +  #c.f9 +  0)==1)
}   
// TwoPhaseLocking And Operator =>  Tracing AND  AccessClassified AND  Lockable AND   
fact Invariant_Opreator_7
{
	all c:Configuration | #c.f6==1 implies ( #c.f12=1 and  #c.f18=1 and  #c.f19=1)
}   
// Checkpointing And Operator =>  Checkpointable AND  Tracing AND  Context AND   
fact Invariant_Opreator_8
{
	all c:Configuration | #c.f8==1 implies ( #c.f11=1 and  #c.f12=1 and  #c.f13=1)
}   
// Deferring XOR Operator =>  Copyable XOR  Traceable XOR   
fact Invariant_Opreator_9
{
	all c:Configuration | #c.f9==1 implies ( ( #c.f14 +  #c.f15 +  0)==1)
}   
// OutcomeAware And Operator =>  Context AND   
fact Invariant_Opreator_10
{
	all c:Configuration | #c.f10==1 implies ( #c.f13=1)
}   
// Checkpointable And Operator =>  Copyable AND   
fact Invariant_Opreator_11
{
	all c:Configuration | #c.f11==1 implies ( #c.f14=1)
}   
// Tracing And Operator =>  Context AND  Traceable AND   
fact Invariant_Opreator_12
{
	all c:Configuration | #c.f12==1 implies ( #c.f13=1 and  #c.f15=1)
}   
// Traceable And Operator =>  AccessClassified AND   
fact Invariant_Opreator_13
{
	all c:Configuration | #c.f15==1 implies ( #c.f18=1)
}   
// Shared And Operator =>  AccessClassified AND  Lockable AND   
fact Invariant_Opreator_14
{
	all c:Configuration | #c.f16==1 implies ( #c.f18=1 and  #c.f19=1)
}   
// SemanticClassified Optional condition   
fact Invariant_Opreator_15
{
	all c:Configuration | #c.f17==1 implies ( #c.f15=1)
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
	pred_13 and  
	pred_14 and  
	pred_15

}
*/