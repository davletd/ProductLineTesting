
module catalogStructureModel

one sig ProductConfigurations
{	
	configurations : set Configuration
}

sig Configuration
{
f1: one catalogStructure,
f2: one productInformation,
f3: lone Categories,
f4: lone AssociatedAssets,
f5: lone TwoDImage,
f6: lone ThreeDImage,
f7: lone MultipleClassification,
f8: lone MultipleLevel,
f9: lone Description,
f10: lone Thumbnails,
}

sig catalogStructure{}
sig productInformation{}
sig Categories{}
sig AssociatedAssets{}
sig TwoDImage{}
sig ThreeDImage{}
sig MultipleClassification{}
sig MultipleLevel{}
sig Description{}
sig Thumbnails{}

fact Configuration_cardinality
{}

fact Configuration_container
{
	all c : Configuration | c in ProductConfigurations.configurations
}

//Constraints due to require and exclude

// Thumbnails requires TwoDImage
fact Invariant_1
{
	all c:Configuration | #c.f10==1 implies (#c.f5=1)
}   

// Constraints due to the Operators
// catalogStructure And Operator =>  productInformation AND   
fact Invariant_Opreator_1
{
	all c:Configuration | #c.f1==1 implies ( #c.f2=1)
}   
// productInformation And Operator =>   
fact Invariant_Opreator_2
{
}   
// Categories Optional condition   
fact Invariant_Opreator_3
{
	all c:Configuration | #c.f3==1 implies ( #c.f1=1)
}   
// Categories And Operator =>   
fact Invariant_Opreator_4
{
}   
// AssociatedAssets Optional condition   
fact Invariant_Opreator_5
{
	all c:Configuration | #c.f4==1 implies ( #c.f2=1)
}   
// AssociatedAssets XOR Operator =>  TwoDImage XOR  ThreeDImage XOR   
fact Invariant_Opreator_6
{
	all c:Configuration | #c.f4==1 implies ( ( #c.f5 +  #c.f6 +  0)==1)
}   
// MultipleClassification Optional condition   
fact Invariant_Opreator_7
{
	all c:Configuration | #c.f7==1 implies ( #c.f3=1)
}   
// MultipleLevel Optional condition   
fact Invariant_Opreator_8
{
	all c:Configuration | #c.f8==1 implies ( #c.f3=1)
}   
// Description Optional condition   
fact Invariant_Opreator_9
{
	all c:Configuration | #c.f9==1 implies ( #c.f3=1)
}   
// Thumbnails Optional condition   
fact Invariant_Opreator_10
{
	all c:Configuration | #c.f10==1 implies ( #c.f3=1)
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
	pred_10

}
*/