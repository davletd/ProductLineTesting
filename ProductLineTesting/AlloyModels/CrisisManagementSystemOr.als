
module CrisisManagementSystemModel

one sig ProductConfigurations
{	
	configurations : set Configuration
}

sig Configuration
{
f1: one CrisisManagementSystem,
f2: one LongDistanceCall,
f3: lone PDA,
f4: lone GSM,
f5: lone WalkieTalkie,
f6: one Coordinator,
f7: lone MultiCoordinators,
f8: one Mission,
f9: lone Rescue,
f10: lone Observe,
f11: lone Transport,
f12: lone RemoveObstacle,
f13: lone Investigation,
f14: lone NurseWounded,
f15: lone Pumping,
f16: lone Repair,
f17: lone ElecLine,
f18: lone TelecomLine,
f19: lone SortWounded,
f20: lone ITOption,
f21: lone SecureCommunincation,
f22: lone SurveillanceSystem,
f23: lone AuthentificationSystem,
f24: lone DataBaseSystem,
f25: one ServiceUsed,
f26: one GovernementalServices,
f27: lone FireDepartment,
f28: lone FireMan,
f29: lone FireTruck,
f30: lone Police,
f31: lone PoliceMan,
f32: lone PoliceSpecialUnit,
f33: lone Army,
f34: lone Navy,
f35: lone NavySoldier,
f36: lone Boat,
f37: lone TheArmy,
f38: lone Soldier,
f39: lone ArmySpecialUnit,
f40: lone LogisticVehicle,
f41: lone AirForce,
f42: lone Helicopter,
f43: lone AirForceSoldier,
f44: lone Aircraft,
f45: lone CargoAircraft,
f46: lone MedicalServices,
f47: lone PublicHospital,
f48: lone PublicFirstAidDoctor,
f49: lone FirstAidWorker,
f50: lone Ambulance,
f51: lone PrivateHospital,
f52: lone PrivateFirstAidDoctor,
f53: lone PrivateAmbulance,
f54: lone FirstAidDoctor,
f55: lone PrivateAmbulanceCompagny,
f56: lone ExternalCompagny,
f57: lone Electricity,
f58: lone Telecom,
f59: lone ContainsHumanVictims,
f60: one Area,
f61: lone Small,
f62: lone Medium,
f63: lone Large,
f64: one CrisisType,
f65: one SuddenCrises,
f66: lone PlantExplosion,
f67: lone NuclearPlantExplosion,
f68: lone TraditionalPlantExplosion,
f69: lone ChemicalPlantExplosion,
f70: lone MajorAccident,
f71: lone PlaneCrash,
f72: lone CarCrash,
f73: lone TerroristAttack,
f74: lone BombAttack,
f75: lone ChemicalAttack,
f76: lone NaturalDisaster,
f77: lone Flood,
f78: lone Earthquake,
f79: lone Fire,
f80: lone Storm,
f81: lone Hurricane,
f82: lone Snowstorm,
}

sig CrisisManagementSystem{}
sig LongDistanceCall{}
sig PDA{}
sig GSM{}
sig WalkieTalkie{}
sig Coordinator{}
sig MultiCoordinators{}
sig Mission{}
sig Rescue{}
sig Observe{}
sig Transport{}
sig RemoveObstacle{}
sig Investigation{}
sig NurseWounded{}
sig Pumping{}
sig Repair{}
sig ElecLine{}
sig TelecomLine{}
sig SortWounded{}
sig ITOption{}
sig SecureCommunincation{}
sig SurveillanceSystem{}
sig AuthentificationSystem{}
sig DataBaseSystem{}
sig ServiceUsed{}
sig GovernementalServices{}
sig FireDepartment{}
sig FireMan{}
sig FireTruck{}
sig Police{}
sig PoliceMan{}
sig PoliceSpecialUnit{}
sig Army{}
sig Navy{}
sig NavySoldier{}
sig Boat{}
sig TheArmy{}
sig Soldier{}
sig ArmySpecialUnit{}
sig LogisticVehicle{}
sig AirForce{}
sig Helicopter{}
sig AirForceSoldier{}
sig Aircraft{}
sig CargoAircraft{}
sig MedicalServices{}
sig PublicHospital{}
sig PublicFirstAidDoctor{}
sig FirstAidWorker{}
sig Ambulance{}
sig PrivateHospital{}
sig PrivateFirstAidDoctor{}
sig PrivateAmbulance{}
sig FirstAidDoctor{}
sig PrivateAmbulanceCompagny{}
sig ExternalCompagny{}
sig Electricity{}
sig Telecom{}
sig ContainsHumanVictims{}
sig Area{}
sig Small{}
sig Medium{}
sig Large{}
sig CrisisType{}
sig SuddenCrises{}
sig PlantExplosion{}
sig NuclearPlantExplosion{}
sig TraditionalPlantExplosion{}
sig ChemicalPlantExplosion{}
sig MajorAccident{}
sig PlaneCrash{}
sig CarCrash{}
sig TerroristAttack{}
sig BombAttack{}
sig ChemicalAttack{}
sig NaturalDisaster{}
sig Flood{}
sig Earthquake{}
sig Fire{}
sig Storm{}
sig Hurricane{}
sig Snowstorm{}

fact Configuration_cardinality
{}

fact Configuration_container
{
	all c : Configuration | c in ProductConfigurations.configurations
}

//Constraints due to require and exclude

// TerroristAttack requires ArmySpecialUnit
fact Invariant_1
{
	all c:Configuration | #c.f73==1 implies (#c.f39=1)
}   

// TerroristAttack requires PoliceSpecialUnit
fact Invariant_2
{
	all c:Configuration | #c.f73==1 implies (#c.f32=1)
}   

// NuclearPlantExplosion requires TheArmy
fact Invariant_3
{
	all c:Configuration | #c.f67==1 implies (#c.f37=1)
}   

// Constraints due to the Operators
// CrisisManagementSystem And Operator =>  LongDistanceCall AND  Coordinator AND  Mission AND  ServiceUsed AND  Area AND  CrisisType AND   
fact Invariant_Opreator_1
{
	all c:Configuration | #c.f1==1 implies ( #c.f2=1 and  #c.f6=1 and  #c.f8=1 and  #c.f25=1 and  #c.f60=1 and  #c.f64=1)
}   
// LongDistanceCall OR Operator =>  PDA OR  GSM OR  WalkieTalkie OR   
fact Invariant_Opreator_2
{
	all c:Configuration | #c.f2==1 implies ( ( #c.f3 +  #c.f4 +  #c.f5 +  0)<=3)
}   
// Coordinator And Operator =>   
fact Invariant_Opreator_3
{
}   
// MultiCoordinators Optional condition   
fact Invariant_Opreator_4
{
	all c:Configuration | #c.f7==1 implies ( #c.f6=1)
}   
// Mission OR Operator =>  Rescue OR  Observe OR  Transport OR  RemoveObstacle OR  Investigation OR  NurseWounded OR  Pumping OR  Repair OR  SortWounded OR   
fact Invariant_Opreator_5
{
	all c:Configuration | #c.f8==1 implies ( ( #c.f9 +  #c.f10 +  #c.f11 +  #c.f12 +  #c.f13 +  #c.f14 +  #c.f15 +  #c.f16 +  #c.f19 +  0)<=9)
}   
// Repair OR Operator =>  ElecLine OR  TelecomLine OR   
fact Invariant_Opreator_6
{
	all c:Configuration | #c.f16==1 implies ( ( #c.f17 +  #c.f18 +  0)<=2)
}   
// ITOption Optional condition   
fact Invariant_Opreator_7
{
	all c:Configuration | #c.f20==1 implies ( #c.f1=1)
}   
// ITOption OR Operator =>  SecureCommunincation OR  SurveillanceSystem OR  AuthentificationSystem OR  DataBaseSystem OR   
fact Invariant_Opreator_8
{
	all c:Configuration | #c.f20==1 implies ( ( #c.f21 +  #c.f22 +  #c.f23 +  #c.f24 +  0)<=4)
}   
// ServiceUsed And Operator =>  GovernementalServices AND   
fact Invariant_Opreator_9
{
	all c:Configuration | #c.f25==1 implies ( #c.f26=1)
}   
// GovernementalServices And Operator =>   
fact Invariant_Opreator_10
{
}   
// FireDepartment Optional condition   
fact Invariant_Opreator_11
{
	all c:Configuration | #c.f27==1 implies ( #c.f26=1)
}   
// FireDepartment And Operator =>  FireMan AND   
fact Invariant_Opreator_12
{
	all c:Configuration | #c.f27==1 implies ( #c.f28=1)
}   
// FireTruck Optional condition   
fact Invariant_Opreator_13
{
	all c:Configuration | #c.f29==1 implies ( #c.f27=1)
}   
// Police Optional condition   
fact Invariant_Opreator_14
{
	all c:Configuration | #c.f30==1 implies ( #c.f26=1)
}   
// Police And Operator =>  PoliceMan AND   
fact Invariant_Opreator_15
{
	all c:Configuration | #c.f30==1 implies ( #c.f31=1)
}   
// PoliceSpecialUnit Optional condition   
fact Invariant_Opreator_16
{
	all c:Configuration | #c.f32==1 implies ( #c.f30=1)
}   
// Army Optional condition   
fact Invariant_Opreator_17
{
	all c:Configuration | #c.f33==1 implies ( #c.f26=1)
}   
// Army OR Operator =>  Navy OR  TheArmy OR  AirForce OR   
fact Invariant_Opreator_18
{
	all c:Configuration | #c.f33==1 implies ( ( #c.f34 +  #c.f37 +  #c.f41 +  0)<=3)
}   
// Navy And Operator =>  NavySoldier AND   
fact Invariant_Opreator_19
{
	all c:Configuration | #c.f34==1 implies ( #c.f35=1)
}   
// Boat Optional condition   
fact Invariant_Opreator_20
{
	all c:Configuration | #c.f36==1 implies ( #c.f34=1)
}   
// TheArmy And Operator =>  Soldier AND   
fact Invariant_Opreator_21
{
	all c:Configuration | #c.f37==1 implies ( #c.f38=1)
}   
// ArmySpecialUnit Optional condition   
fact Invariant_Opreator_22
{
	all c:Configuration | #c.f39==1 implies ( #c.f37=1)
}   
// LogisticVehicle Optional condition   
fact Invariant_Opreator_23
{
	all c:Configuration | #c.f40==1 implies ( #c.f37=1)
}   
// AirForce And Operator =>  AirForceSoldier AND   
fact Invariant_Opreator_24
{
	all c:Configuration | #c.f41==1 implies ( #c.f43=1)
}   
// Helicopter Optional condition   
fact Invariant_Opreator_25
{
	all c:Configuration | #c.f42==1 implies ( #c.f41=1)
}   
// Aircraft Optional condition   
fact Invariant_Opreator_26
{
	all c:Configuration | #c.f44==1 implies ( #c.f41=1)
}   
// Aircraft And Operator =>   
fact Invariant_Opreator_27
{
}   
// CargoAircraft Optional condition   
fact Invariant_Opreator_28
{
	all c:Configuration | #c.f45==1 implies ( #c.f44=1)
}   
// MedicalServices Optional condition   
fact Invariant_Opreator_29
{
	all c:Configuration | #c.f46==1 implies ( #c.f25=1)
}   
// MedicalServices OR Operator =>  PublicHospital OR  PrivateHospital OR  FirstAidDoctor OR  PrivateAmbulanceCompagny OR   
fact Invariant_Opreator_30
{
	all c:Configuration | #c.f46==1 implies ( ( #c.f47 +  #c.f51 +  #c.f54 +  #c.f55 +  0)<=4)
}   
// PublicHospital And Operator =>  FirstAidWorker AND   
fact Invariant_Opreator_31
{
	all c:Configuration | #c.f47==1 implies ( #c.f49=1)
}   
// PublicFirstAidDoctor Optional condition   
fact Invariant_Opreator_32
{
	all c:Configuration | #c.f48==1 implies ( #c.f47=1)
}   
// Ambulance Optional condition   
fact Invariant_Opreator_33
{
	all c:Configuration | #c.f50==1 implies ( #c.f47=1)
}   
// PrivateHospital And Operator =>   
fact Invariant_Opreator_34
{
}   
// PrivateFirstAidDoctor Optional condition   
fact Invariant_Opreator_35
{
	all c:Configuration | #c.f52==1 implies ( #c.f51=1)
}   
// PrivateAmbulance Optional condition   
fact Invariant_Opreator_36
{
	all c:Configuration | #c.f53==1 implies ( #c.f51=1)
}   
// ExternalCompagny Optional condition   
fact Invariant_Opreator_37
{
	all c:Configuration | #c.f56==1 implies ( #c.f25=1)
}   
// ExternalCompagny OR Operator =>  Electricity OR  Telecom OR   
fact Invariant_Opreator_38
{
	all c:Configuration | #c.f56==1 implies ( ( #c.f57 +  #c.f58 +  0)<=2)
}   
// ContainsHumanVictims Optional condition   
fact Invariant_Opreator_39
{
	all c:Configuration | #c.f59==1 implies ( #c.f1=1)
}   
// Area XOR Operator =>  Small XOR  Medium XOR  Large XOR   
fact Invariant_Opreator_40
{
	all c:Configuration | #c.f60==1 implies ( ( #c.f61 +  #c.f62 +  #c.f63 +  0)==1)
}   
// CrisisType And Operator =>  SuddenCrises AND   
fact Invariant_Opreator_41
{
	all c:Configuration | #c.f64==1 implies ( #c.f65=1)
}   
// SuddenCrises XOR Operator =>  PlantExplosion XOR  MajorAccident XOR  TerroristAttack XOR  NaturalDisaster XOR   
fact Invariant_Opreator_42
{
	all c:Configuration | #c.f65==1 implies ( ( #c.f66 +  #c.f70 +  #c.f73 +  #c.f76 +  0)==1)
}   
// PlantExplosion XOR Operator =>  NuclearPlantExplosion XOR  TraditionalPlantExplosion XOR  ChemicalPlantExplosion XOR   
fact Invariant_Opreator_43
{
	all c:Configuration | #c.f66==1 implies ( ( #c.f67 +  #c.f68 +  #c.f69 +  0)==1)
}   
// MajorAccident XOR Operator =>  PlaneCrash XOR  CarCrash XOR   
fact Invariant_Opreator_44
{
	all c:Configuration | #c.f70==1 implies ( ( #c.f71 +  #c.f72 +  0)==1)
}   
// TerroristAttack XOR Operator =>  BombAttack XOR  ChemicalAttack XOR   
fact Invariant_Opreator_45
{
	all c:Configuration | #c.f73==1 implies ( ( #c.f74 +  #c.f75 +  0)==1)
}   
// NaturalDisaster XOR Operator =>  Fire XOR  Storm XOR  Flood XOR  Earthquake XOR   
fact Invariant_Opreator_46
{
	all c:Configuration | #c.f76==1 implies ( ( #c.f79 +  #c.f80 +  #c.f77 +  #c.f78 +  0)==1)
}   
// Storm XOR Operator =>  Hurricane XOR  Snowstorm XOR   
fact Invariant_Opreator_47
{
	all c:Configuration | #c.f80==1 implies ( ( #c.f81 +  #c.f82 +  0)==1)
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
	pred_15 and  
	pred_16 and  
	pred_17 and  
	pred_18 and  
	pred_19 and  
	pred_20 and  
	pred_21 and  
	pred_22 and  
	pred_23 and  
	pred_24 and  
	pred_25 and  
	pred_26 and  
	pred_27 and  
	pred_28 and  
	pred_29 and  
	pred_30 and  
	pred_31 and  
	pred_32 and  
	pred_33 and  
	pred_34 and  
	pred_35 and  
	pred_36 and  
	pred_37 and  
	pred_38 and  
	pred_39 and  
	pred_40 and  
	pred_41 and  
	pred_42 and  
	pred_43 and  
	pred_44 and  
	pred_45 and  
	pred_46 and  
	pred_47

}
*/