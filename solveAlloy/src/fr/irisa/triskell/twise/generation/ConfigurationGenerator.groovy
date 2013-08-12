/**
 * 
 */
package fr.irisa.triskell.twise.generation

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution

class ConfigurationGenerator {
	public ArrayList<ConjunctionTuple> pool_
	public TupleSet initial_
	Integer twise_
	ArrayList<Feature> productFeatures_
	String root_
	String filename_
	String tempFileName_
	String solutionPath_
	Integer minScopeDetect_
	Integer maxScopeDetect_
	Integer minScope_
	Integer maxScope_
	Integer maxDurationDetect_
	Integer maxDurationExp_
	ExperimentLog binarySplitExperiment_
	ExperimentLog incrementalGrowthExperiment_
	TestSuite testModels_
	private boolean isIncremental_

	public ConfigurationGenerator(Integer twise,
			ArrayList<Feature> productFeatures,
			String root,
			String filename,
			String tempFileName,
			String solutionPath,
			Integer minScopeDetect,
			Integer maxScopeDetect,
			Integer minScope,
			Integer maxScope,
			Integer maxDurationDetect,
			Integer maxDurationExp) throws Err, IOException
	{
		twise_ = twise
		productFeatures_= productFeatures
		root_= root
		filename_= filename
		tempFileName_= tempFileName
		solutionPath_=solutionPath
		minScopeDetect_ = minScopeDetect
		maxScopeDetect_ = maxScopeDetect
		minScope_ = minScope
		maxScope_ = maxScope
		maxDurationDetect_= maxDurationDetect
		maxDurationExp_ = maxDurationExp
		binarySplitExperiment_ = new ExperimentLog()
		incrementalGrowthExperiment_ = new ExperimentLog()
		pool_ = new ArrayList<ConjunctionTuple>()
		initial_ = new TupleSet()
		initial_.createCreateAllTuples(productFeatures,twise)
		initial_.getVaildTuples(root,filename,tempFileName, minScopeDetect, maxScopeDetect, maxDurationDetect)
	}

	def isIncremental() 
	{
		isIncremental_
	}

	def showTupleSet(ArrayList<Tuple> input) {
		def tupleString = ""
		input.each { it -> tupleString += "Tuple${it.number}," }
		return "{" +tupleString.substring(0,tupleString.length()-1)+"}"		
	}
	
	public static boolean deleteDir(File dir) 
	{
		if (dir.isDirectory()) {
			for (child in dir.list())
			{
				def file = new File(dir, child)
				if(!file.delete())
					return false				
			}		
		}
		// The directory is now empty so delete it
		return true;
	}


	public void cleanUpSolutions(String solutionPath)
	{
		def dir = new File(solutionPath)

		if(deleteDir(dir))
			println "Clean up of solution directory successful..."
		else
			println "Clean up of solution directory failed..."
	}
	
	public void fillPoolIncremental(Integer solutionNumber) throws Err, IOException
	{
		isIncremental_ = true;
		def currentTupleSet = new ArrayList<Tuple>();
		A4Solution currentSolution=null;
		def remainingTupleSet=new ArrayList<Tuple>();
		remainingTupleSet.addAll(initial_.validTupleSet);
		def setNumber = 1;
		pool_.clear();
		def result= true;

		while(!remainingTupleSet.isEmpty()) {
			def temp = new ConjunctionTuple();
			temp.tuples = new ArrayList<Tuple>();
			temp.tuples.clear();
			currentTupleSet.clear();
			println "\nCreating test set number ${setNumber}"
			result=true;
			while(result == true && !remainingTupleSet.isEmpty())
			{
				result = false 
				if(temp.outputSolution!=null)
					currentSolution = temp.outputSolution
				def tupleIndex= 0;
				tupleIndex= initial_.selectNextTuple(currentTupleSet,remainingTupleSet, SelectStrategy.RANDOM);
				currentTupleSet.add(remainingTupleSet.get(tupleIndex));
				remainingTupleSet.remove(tupleIndex);
				def lastPosition = currentTupleSet.size()-1;
				temp=new ConjunctionTuple(setNumber,initial_.baseAlloyModel,root_,tempFileName_,currentTupleSet);
				
				//Solve the conjuction
				result = temp.solve(minScope_, maxScope_, maxDurationExp_);
				this.incrementalGrowthExperiment_.add((int)temp.timeTaken, (int)temp.scopeUsed);
				
				if(!result) {
					remainingTupleSet.add(currentTupleSet.get(lastPosition));
					currentTupleSet.remove(lastPosition);
					temp.outputSolution=currentSolution;
					temp.tuples.clear();
					temp.tuples.addAll(currentTupleSet);					
				}
				if(result)
				{
					//System.out.println("Current Status:"+this.showTupleSet(temp.tuples)+" of set "+setNumber);
				}
				if(remainingTupleSet.isEmpty())
				{

					temp.tuples.clear();
					temp.tuples.addAll(currentTupleSet);
					//	System.out.println("Final Status:"+this.showTupleSet(temp.tuples)+" of set "+setNumber);
				}


			}

			//System.out.println("Current tuple set is =");
			//System.out.println(this.showTupleSet(currentTupleSet));
			//Insert the current set of tuples to the Pool
			//	Product p = new Product();
			//	p.setSolution(solutionNumber, temp.outputSolution);
			//	this.testModels.addProduct(p);
			pool_.add(temp);
			//Save tuple into a file
			def solutionFileName = "Set ${setNumber}_${twise_}wise_tuples.xml"
			def solDirectoy = root_ + solutionPath_+"\\Solution"+solutionNumber
			
			if ((new File(solDirectoy)).mkdir()) 
				println "Solution Directory: ${solDirectoy} created"
			
			temp.dumpSolution(root_, "${solutionPath_}\\Solution${solutionNumber}\\${solutionFileName}")

			//System.out.println("Tuples added in pool=");
			//	System.out.println(this.showTupleSet(Pool.get(0).tuples));

			remainingTupleSet.removeAll(currentTupleSet)


			if(!remainingTupleSet.isEmpty()) {
				//	System.out.println("Remaining tuples are...");
				//	System.out.println(this.showTupleSet(remainingTupleSet));
			}
			setNumber++
		}
		//Compute the values in the experiment logger
		incrementalGrowthExperiment_.compute()
		incrementalGrowthExperiment_.numberOfSolutions=pool_.size()
		//System.out.println(this.IncrementalGrowthExperiment);
		incrementalGrowthExperiment_.solutionNumber = solutionNumber
		incrementalGrowthExperiment_.save("${root_}${solutionPath_}\\Solution${solutionNumber}\\Solution${solutionNumber}_result.txt")

	}

	public ArrayList<Tuple> orderRandom(ArrayList<Tuple> tupleSet)
	{
		def rgen = new Random();

		for (i in 0..tupleSet.size()) {
			int randomPosition = rgen.nextInt(tupleSet.size());
			Tuple temp = tupleSet.get(i);
			tupleSet.set(i, tupleSet.get(randomPosition));
			tupleSet.set(randomPosition, temp);
		}
		return tupleSet;


	}
	public int getIndexLargest(ArrayList<ConjunctionTuple> current)
	{
		def index = 0
		int maxValue = 0
		
		for(i in 0..current.size()) {
			if (current.get(i).tuples.size() > maxValue) {
				maxValue=current.get(i).tuples.size();
				index=i;
			}
		}

		return index;
	}

	public ArrayList<ConjunctionTuple> selectAndSplit(int setNumber, ArrayList<ConjunctionTuple> setOfConjunctions, SplitSelectStrategy strategy)
	{
		if (strategy!=SplitSelectStrategy.LARGEST)
			return setOfConjunctions
		
			// Random generator = new Random();
		def maxIndex = getIndexLargest(setOfConjunctions);
		ConjunctionTuple current = setOfConjunctions.get(maxIndex);


		def half1 = new ArrayList<Tuple>();
		def half2 = new ArrayList<Tuple>();
		def half1conj = new ConjunctionTuple();
		def half2conj = new ConjunctionTuple();

		if(current.tuples.size() == 1) {
			println "Size is unity. Cannot be split further"
			return setOfConjunctions
		}
		
		if(current.tuples.size() > 1) {
			def halfPoint = (int) Math.floor(current.tuples.size()/2)
			half1.addAll(current.tuples.subList(0,halfPoint))
			half2.addAll(current.tuples.subList(halfPoint+1, current.tuples.size()-1))
			//System.out.println("Number of tuples in first half="+half1.size());
			//System.out.println("Number of tuples in second half="+half2.size());
			half1conj = new ConjunctionTuple(setNumber, initial_.baseAlloyModel, root_, tempFileName_, half1)
			setNumber++;
			half2conj = new ConjunctionTuple(setNumber, initial_.baseAlloyModel, root_, tempFileName_,half2)
			//Remove the split entity
			setOfConjunctions.remove(maxIndex)
			//Add the entities after the split
			setOfConjunctions.add(half1conj)
			setOfConjunctions.add(half2conj)
		}
		return setOfConjunctions		
	}

	public void fillPoolBinary(Integer solutionNumber) throws Err, IOException
	{
		isIncremental_ = false

		def initialTupleSet = new ArrayList<Tuple>()

		initialTupleSet.addAll(initial_.validTupleSet)

		//Random ordering of initial set of tuples

		initialTupleSet = orderRandom(initialTupleSet)
		def setNumber = 1
		def result = false
		def allResult = true
		def setOfConjunctions = new ArrayList<ConjunctionTuple>();
		def initialConjunction = new ConjunctionTuple(setNumber,initial_.baseAlloyModel,this.root_,this.tempFileName_,initialTupleSet);
				setOfConjunctions.clear();
		setOfConjunctions.add(initialConjunction);
		pool_.clear();
		println "Number of valid tuples=${initialTupleSet.size()}"
		//System.out.println("Number of valid conjunctions=" + setOfConjunctions.size());
		//productLineTestGeneration.setNumberOfconjunctions(setOfConjunctions.size());
		allResult=false
		while(!allResult) {
			allResult=true
			
			for (temp in setOfConjunctions)	{
				temp.solve(minScope_, maxScope_, maxDurationExp_)
				allResult = allResult && result
			}
			if(allResult) {
				pool_.addAll(setOfConjunctions);
				for (temp in pool_) {
					binarySplitExperiment_.add((int)temp.timeTaken,(int)temp.scopeUsed);
				}
			}
			//System.out.println("All result="+Allresult);
			setOfConjunctions = selectAndSplit(setNumber,setOfConjunctions,SplitSelectStrategy.LARGEST)

			if(!allResult)
				pool_.clear()			
			if (pool_.size()==initial_.validTupleSet.size())
				break			
		}

		for(temp in pool_)
		{
			String solutionFileName="Set${pool_.indexOf(temp)}_${twise_}_wise_tuples.xml"
			String solDirectoy =root_+solutionPath_+"\\Solution"+solutionNumber;
			
			if ((new File(solDirectoy)).mkdir()) 
				println "Solution Directory: ${solDirectoy} created"
			//Product p = new Product();
			//p.setSolution(solutionNumber, temp.outputSolution);
			//this.testModels.addProduct(p);

			temp.dumpSolution(root_, solutionPath_+"\\Solution"+solutionNumber+"\\"+solutionFileName);
		}
		//Compute experiment details and print
		binarySplitExperiment_.compute();
		binarySplitExperiment_.numberOfSolutions=pool_.size();
		binarySplitExperiment_.solutionNumber=solutionNumber;
		def solutionResultName="Solution"+solutionNumber+"_result"+".txt";
		binarySplitExperiment_.save(root_+solutionPath_+"\\Solution"+solutionNumber+"\\"+solutionResultName);
		//System.out.println(this.BinarySplitExperiment);

	}

	public String toString()
	{
		String PoolString = "{";
		System.out.println("\n Number of test sets = "+pool_.size());
		System.out.println("\n Test sets are:");

		PoolString="{";
		
		pool_.each {it -> println it.String toString() }
		
		for(int i=0;i<pool_.size();i++)
		{
			System.out.println(this.showTupleSet(pool_.get(i).tuples));
			PoolString = PoolString + this.showTupleSet(pool_.get(i).tuples)+ ",";
		}
		PoolString = PoolString.substring(0,PoolString.length()-1);
		PoolString = PoolString + " }\n";


		return PoolString;

	}
}
