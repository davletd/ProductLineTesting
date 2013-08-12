
module VideoSurveillanceApplicationModel

one sig ProductConfigurations
{	
	configurations : set Configuration
}

sig Configuration
{
f1: one VideoSurveillanceApplication,
f2: lone Counting,
f3: lone IntrusionDetection,
f4: lone Tracking,
f5: lone Person,
f6: lone Vehicle,
f7: lone Immovable,
f8: lone SelfPropelled,
f9: lone ExternallyPropelled,
f10: lone SingleObject,
f11: lone GroupOfObjects,
f12: lone MonoSensor,
f13: lone MultiSensor,
f14: lone Server,
f15: lone ProgrammerDefined,
f16: lone ClientDefined,
f17: lone TopView,
f18: lone SideView,
f19: lone Normal,
f20: lone BlackAndWhite,
f21: lone FramesPerSecond,
f22: lone Color,
f23: lone InfraRed,
f24: lone Resolution,
f25: lone Large,
f26: lone Narrow,
f27: lone DepthOfField,
f28: lone NaturalLight,
f29: lone ArtificialLight,
f30: lone Day,
f31: lone Night,
f32: lone Indoors,
f33: lone VegetationMovement,
f34: lone SandOrDust,
f35: lone SeaOceanWaves,
f36: lone Flashes,
f37: lone Shadows,
f38: lone ComputerLoad,
f39: lone ResponseTime,
f40: lone Precision,
f41: lone Sensitivity,
f42: one Scenery3DModel,
f43: lone BehaviourLibrary,
f44: one Task,
f45: one ObjectOfInterest,
f46: one Scene,
f47: one QualityOfService,
f48: one Environment,
f49: lone Noise,
f50: one APrioriKnowledge,
f51: lone DeploymentArchitecture,
f52: lone Sensor,
f53: lone SensorView,
f54: lone Camera,
f55: lone CameraType,
f56: lone FieldOfView,
f57: lone LightingType,
f58: one LightingConditions,
f59: lone Outdoors,
f60: lone BackgroundMovement,
f61: lone LightingVariation,
f62: lone Quality,
f63: one Sort,
f64: one Mobility,
f65: one Cardinality,
f66: lone Movable,
f67: lone Natural,
f68: lone Manufactured,
f69: lone BehaviourRecognition,
f70: lone TimeOfDay,
}

sig VideoSurveillanceApplication{}
sig Counting{}
sig IntrusionDetection{}
sig Tracking{}
sig Person{}
sig Vehicle{}
sig Immovable{}
sig SelfPropelled{}
sig ExternallyPropelled{}
sig SingleObject{}
sig GroupOfObjects{}
sig MonoSensor{}
sig MultiSensor{}
sig Server{}
sig ProgrammerDefined{}
sig ClientDefined{}
sig TopView{}
sig SideView{}
sig Normal{}
sig BlackAndWhite{}
sig FramesPerSecond{}
sig Color{}
sig InfraRed{}
sig Resolution{}
sig Large{}
sig Narrow{}
sig DepthOfField{}
sig NaturalLight{}
sig ArtificialLight{}
sig Day{}
sig Night{}
sig Indoors{}
sig VegetationMovement{}
sig SandOrDust{}
sig SeaOceanWaves{}
sig Flashes{}
sig Shadows{}
sig ComputerLoad{}
sig ResponseTime{}
sig Precision{}
sig Sensitivity{}
sig Scenery3DModel{}
sig BehaviourLibrary{}
sig Task{}
sig ObjectOfInterest{}
sig Scene{}
sig QualityOfService{}
sig Environment{}
sig Noise{}
sig APrioriKnowledge{}
sig DeploymentArchitecture{}
sig Sensor{}
sig SensorView{}
sig Camera{}
sig CameraType{}
sig FieldOfView{}
sig LightingType{}
sig LightingConditions{}
sig Outdoors{}
sig BackgroundMovement{}
sig LightingVariation{}
sig Quality{}
sig Sort{}
sig Mobility{}
sig Cardinality{}
sig Movable{}
sig Natural{}
sig Manufactured{}
sig BehaviourRecognition{}
sig TimeOfDay{}

fact Configuration_cardinality
{}

fact Configuration_container
{
	all c : Configuration | c in ProductConfigurations.configurations
}

//Constraints due to require and exclude

// Constraints due to the Operators
// VideoSurveillanceApplication And Operator =>  Task AND  ObjectOfInterest AND  Scene AND  QualityOfService AND   
fact Invariant_Opreator_1
{
	all c:Configuration | #c.f1==1 implies ( #c.f44=1 and  #c.f45=1 and  #c.f46=1 and  #c.f47=1)
}   
// ProgrammerDefined Optional condition   
fact Invariant_Opreator_2
{
	all c:Configuration | #c.f15==1 implies ( #c.f51=1)
}   
// ClientDefined Optional condition   
fact Invariant_Opreator_3
{
	all c:Configuration | #c.f16==1 implies ( #c.f51=1)
}   
// VegetationMovement Optional condition   
fact Invariant_Opreator_4
{
	all c:Configuration | #c.f33==1 implies ( #c.f60=1)
}   
// SandOrDust Optional condition   
fact Invariant_Opreator_5
{
	all c:Configuration | #c.f34==1 implies ( #c.f60=1)
}   
// SeaOceanWaves Optional condition   
fact Invariant_Opreator_6
{
	all c:Configuration | #c.f35==1 implies ( #c.f60=1)
}   
// Flashes Optional condition   
fact Invariant_Opreator_7
{
	all c:Configuration | #c.f36==1 implies ( #c.f61=1)
}   
// Shadows Optional condition   
fact Invariant_Opreator_8
{
	all c:Configuration | #c.f37==1 implies ( #c.f61=1)
}   
// BehaviourLibrary Optional condition   
fact Invariant_Opreator_9
{
	all c:Configuration | #c.f43==1 implies ( #c.f50=1)
}   
// Task OR Operator =>  Counting OR  BehaviourRecognition OR  Tracking OR   
fact Invariant_Opreator_10
{
	all c:Configuration | #c.f44==1 implies ( ( #c.f2 +  #c.f69 +  #c.f4 +  0)<=3)
}   
// ObjectOfInterest And Operator =>  Sort AND  Cardinality AND  Mobility AND   
fact Invariant_Opreator_11
{
	all c:Configuration | #c.f45==1 implies ( #c.f63=1 and  #c.f65=1 and  #c.f64=1)
}   
// Scene And Operator =>  APrioriKnowledge AND  Environment AND   
fact Invariant_Opreator_12
{
	all c:Configuration | #c.f46==1 implies ( #c.f50=1 and  #c.f48=1)
}   
// QualityOfService OR Operator =>  ComputerLoad OR  ResponseTime OR  Quality OR   
fact Invariant_Opreator_13
{
	all c:Configuration | #c.f47==1 implies ( ( #c.f38 +  #c.f39 +  #c.f62 +  0)<=3)
}   
// Environment And Operator =>  LightingConditions AND   
fact Invariant_Opreator_14
{
	all c:Configuration | #c.f48==1 implies ( #c.f58=1)
}   
// Noise Optional condition   
fact Invariant_Opreator_15
{
	all c:Configuration | #c.f49==1 implies ( #c.f48=1)
}   
// Noise And Operator =>   
fact Invariant_Opreator_16
{
}   
// APrioriKnowledge And Operator =>  Scenery3DModel AND   
fact Invariant_Opreator_17
{
	all c:Configuration | #c.f50==1 implies ( #c.f42=1)
}   
// DeploymentArchitecture Optional condition   
fact Invariant_Opreator_18
{
	all c:Configuration | #c.f51==1 implies ( #c.f50=1)
}   
// DeploymentArchitecture And Operator =>  MonoSensor AND  MultiSensor AND  Server AND  Sensor AND   
fact Invariant_Opreator_19
{
	all c:Configuration | #c.f51==1 implies ( #c.f12=1 and  #c.f13=1 and  #c.f14=1 and  #c.f52=1)
}   
// Sensor And Operator =>  SensorView AND  Camera AND   
fact Invariant_Opreator_20
{
	all c:Configuration | #c.f52==1 implies ( #c.f53=1 and  #c.f54=1)
}   
// SensorView XOR Operator =>  TopView XOR  SideView XOR  Normal XOR   
fact Invariant_Opreator_21
{
	all c:Configuration | #c.f53==1 implies ( ( #c.f17 +  #c.f18 +  #c.f19 +  0)==1)
}   
// Camera And Operator =>  FramesPerSecond AND  CameraType AND  Resolution AND  DepthOfField AND  FieldOfView AND   
fact Invariant_Opreator_22
{
	all c:Configuration | #c.f54==1 implies ( #c.f21=1 and  #c.f55=1 and  #c.f24=1 and  #c.f27=1 and  #c.f56=1)
}   
// CameraType XOR Operator =>  BlackAndWhite XOR  InfraRed XOR  Color XOR   
fact Invariant_Opreator_23
{
	all c:Configuration | #c.f55==1 implies ( ( #c.f20 +  #c.f23 +  #c.f22 +  0)==1)
}   
// FieldOfView XOR Operator =>  Large XOR  Narrow XOR   
fact Invariant_Opreator_24
{
	all c:Configuration | #c.f56==1 implies ( ( #c.f25 +  #c.f26 +  0)==1)
}   
// LightingType OR Operator =>  NaturalLight OR  ArtificialLight OR   
fact Invariant_Opreator_25
{
	all c:Configuration | #c.f57==1 implies ( ( #c.f28 +  #c.f29 +  0)<=2)
}   
// LightingConditions OR Operator =>  LightingType OR  Outdoors OR  Indoors OR   
fact Invariant_Opreator_26
{
	all c:Configuration | #c.f58==1 implies ( ( #c.f57 +  #c.f59 +  #c.f32 +  0)<=3)
}   
// Outdoors And Operator =>  TimeOfDay AND   
fact Invariant_Opreator_27
{
	all c:Configuration | #c.f59==1 implies ( #c.f70=1)
}   
// BackgroundMovement Optional condition   
fact Invariant_Opreator_28
{
	all c:Configuration | #c.f60==1 implies ( #c.f49=1)
}   
// BackgroundMovement OR Operator =>  VegetationMovement OR  SandOrDust OR  SeaOceanWaves OR   
fact Invariant_Opreator_29
{
	all c:Configuration | #c.f60==1 implies ( ( #c.f33 +  #c.f34 +  #c.f35 +  0)<=3)
}   
// LightingVariation Optional condition   
fact Invariant_Opreator_30
{
	all c:Configuration | #c.f61==1 implies ( #c.f49=1)
}   
// LightingVariation OR Operator =>  Flashes OR  Shadows OR   
fact Invariant_Opreator_31
{
	all c:Configuration | #c.f61==1 implies ( ( #c.f36 +  #c.f37 +  0)<=2)
}   
// Quality OR Operator =>  Precision OR  Sensitivity OR   
fact Invariant_Opreator_32
{
	all c:Configuration | #c.f62==1 implies ( ( #c.f40 +  #c.f41 +  0)<=2)
}   
// Sort OR Operator =>  Natural OR  Manufactured OR   
fact Invariant_Opreator_33
{
	all c:Configuration | #c.f63==1 implies ( ( #c.f67 +  #c.f68 +  0)<=2)
}   
// Mobility XOR Operator =>  Immovable XOR  Movable XOR   
fact Invariant_Opreator_34
{
	all c:Configuration | #c.f64==1 implies ( ( #c.f7 +  #c.f66 +  0)==1)
}   
// Cardinality XOR Operator =>  SingleObject XOR  GroupOfObjects XOR   
fact Invariant_Opreator_35
{
	all c:Configuration | #c.f65==1 implies ( ( #c.f10 +  #c.f11 +  0)==1)
}   
// Movable XOR Operator =>  SelfPropelled XOR  ExternallyPropelled XOR   
fact Invariant_Opreator_36
{
	all c:Configuration | #c.f66==1 implies ( ( #c.f8 +  #c.f9 +  0)==1)
}   
// Natural And Operator =>  Person AND   
fact Invariant_Opreator_37
{
	all c:Configuration | #c.f67==1 implies ( #c.f5=1)
}   
// Manufactured And Operator =>  Vehicle AND   
fact Invariant_Opreator_38
{
	all c:Configuration | #c.f68==1 implies ( #c.f6=1)
}   
// BehaviourRecognition OR Operator =>  IntrusionDetection OR   
fact Invariant_Opreator_39
{
	all c:Configuration | #c.f69==1 implies ( ( #c.f3 +  0)<=1)
}   
// TimeOfDay OR Operator =>  Day OR  Night OR   
fact Invariant_Opreator_40
{
	all c:Configuration | #c.f70==1 implies ( ( #c.f30 +  #c.f31 +  0)<=2)
}   

// MonoSensor XOR Multisensor 
fact Invariant_Opreator_37
{
	all c:Configuration | (#c.f12==1 implies #c.f13=0) or (#c.f13=1 implies #c.f12=0)
}   


pred Test
{

#Configuration=1
}

run Test for 1
