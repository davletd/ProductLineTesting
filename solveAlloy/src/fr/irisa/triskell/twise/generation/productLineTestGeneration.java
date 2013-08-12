package fr.irisa.triskell.twise.generation;


import java.util.StringTokenizer;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.Random;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;
import java.util.logging.Level;
//import java.util.logging.Logger;
import java.io.*;
import java.math.*;

import lu.uni.lassy.metrics.AlloyFeatureExtractor;
import lu.uni.lassy.metrics.FeatureModel2JGraph;
import lu.uni.lassy.metrics.MetricsStore;
import lu.uni.lassy.metrics.Redundancy;

//import sun.tools.tree.ThisExpression;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprConstant;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Func;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.parser.Module;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Tuple;
import edu.mit.csail.sdg.alloy4compiler.translator.A4TupleSet;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;
import static edu.mit.csail.sdg.alloy4compiler.ast.Sig.UNIV;

//Enumeration for strategy selection

enum SelectStrategy {RANDOM, DISTANCE};
enum SplitSelectStrategy {LARGEST};






class ConjunctionTuple
{
	public ArrayList<Tuple> tuples;
	public String name;
	public Integer number;
	public String baseAlloyModel;
	public String tempFile;
	public A4Solution outputSolution;
	public String root;
	public long timeTaken;
	public long scopeUsed;
	private boolean solveThreadFinished = false;

	public ConjunctionTuple()
	{}

	public ConjunctionTuple(Integer number, String alloyModel, String root, String tempFileName, ArrayList<Tuple> tuplesInCon)
	{
		this.number = number;
		this.name = "ConjunctionTuple" + number;
		this.baseAlloyModel = alloyModel;
		this.tempFile = tempFileName;
		this.tuples=new ArrayList<Tuple>();
		this.tuples.addAll(tuplesInCon);
		this.root = root;
		this.outputSolution=null;
	}


	public String getPredicate()
	{
		String predicate = "pred "+this.name+"{";
		for(int i=0;i<this.tuples.size();i++)
		{
			predicate= predicate + this.tuples.get(i).getName()+" and ";
		}
		predicate = predicate.substring(0,predicate.length()-4);
		predicate = predicate +"}";
		return predicate;
	}

	public String getCommand(Integer scope)
	{
		String command =" run ";
		command = command + this.name +" for ";
		command = command + scope;
		return command;
	}

	public void dumpSolution(String path, String solutionFileName) throws Err
	{

		if(this.outputSolution!=null)
		{
			System.out.println("Attempting to write file "+path+solutionFileName);
			if (this.outputSolution.satisfiable()) {
				// You can query "ans" to find out the values of each set or type.
				// This can be useful for debugging.
				//
				// You can also write the outcome to an XML file
				System.out.println("Writing file "+path+solutionFileName);
				this.outputSolution.writeXML(path+solutionFileName);

			}    
		}
	}

	public void deleteTemp(String fileName) 
	{

		// A File object to represent the filename
		File f = new File(fileName);

		// Make sure the file or directory exists and isn't write protected
		if (!f.exists())
			throw new IllegalArgumentException("Delete: no such file or directory: " + fileName);

		if (!f.canWrite())
			throw new IllegalArgumentException("Delete: write protected: "
					+ fileName);

		// If it is a directory, make sure it is empty
		if (f.isDirectory()) {
			String[] files = f.list();
			if (files.length > 0)
				throw new IllegalArgumentException(
						"Delete: directory not empty: " + fileName);
		}
	}
	@SuppressWarnings("static-access")
	public synchronized Boolean solve(Integer minScope, Integer maxScope, Integer maxDuration) throws Err, IOException
	{
		//
		boolean isSolved = false;

		A4Reporter rep = new A4Reporter() {
			// For example, here we choose to display each "warning" by printing it to System.out
			@Override public void warning(ErrorWarning msg) {
				System.out.print("Relevance Warning:\n"+(msg.toString().trim())+"\n\n");
				System.out.flush();
			}
		};

		Integer scope;
		long start;
		long end;
		long duration=0;
		scope=minScope;
		String currentAlloyString ="";
		Boolean verbose=true;
		String tempFileName = this.root + this.tempFile;

		BufferedWriter outInitial = new BufferedWriter(new FileWriter(tempFileName));
		outInitial.write(currentAlloyString);
		outInitial.close();
		Module world=null;
		// Choose some default options for how you want to execute the commands
		A4Options options = new A4Options();
		options.solver = A4Options.SatSolver.MiniSatJNI;
		A4Solution ans;
		BufferedWriter out;
		Integer modelCopy=new Integer(0);

		//scope<=maxScope && duration <= maxDuration 
		//Changed here
		while(scope<=maxScope && duration <= maxDuration)
		{
			duration=0;

			currentAlloyString = this.baseAlloyModel + "\n" + this.getPredicate() + "\n" + this.getCommand(scope);
			//Delete temp file
			this.deleteTemp(tempFileName);
			//Write a new temp file
			out = new BufferedWriter(new FileWriter(tempFileName));
			out.write(currentAlloyString);
			out.close();
			// Parse+typecheck the model
			if(verbose==true)
			{System.out.println("=========== Parsing+Typechecking "+tempFileName+" =============");}
			world = CompUtil.parseEverything_fromFile(rep, null, tempFileName);
			boolean solveInDueTime = false;

			modelCopy=0;
			ExecutorService exec = Executors.newSingleThreadExecutor();
			for (Command command: world.getAllCommands()) {
				if(verbose==true)
				{System.out.println("============ Command "+command+": ============");}

				//TranslateAlloyToKodkodThreadController controller = new TranslateAlloyToKodkodThreadController(rep, world.getAllReachableSigs(), command, options, duration);
				productLineTestGeneration.setNumberOfconjunctions(productLineTestGeneration.getNumberOfconjunctions()+1);
				TranslateAlloyToKodkodThread ta2kt=new TranslateAlloyToKodkodThread(rep,world.getAllReachableSigs(),command,options,maxDuration); 
				
				
				
					ta2kt.setPriority(Thread.MIN_PRIORITY); // or MAX_PRIORITY ??? 
					exec.execute(ta2kt); 
					System.out.println("starting Solving thread" + ta2kt.getName());
					exec.shutdown();
					start = System.currentTimeMillis();
					
					try {
						solveInDueTime= exec.awaitTermination(maxDuration, TimeUnit.MILLISECONDS);
					} catch (InterruptedException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
					

				end = System.currentTimeMillis();

				duration = end-start;

				if (!solveInDueTime) {
					System.out.println("Discarded this solution : " + duration + " >= " + maxDuration+ " ms");
					productLineTestGeneration.setNumberOfDiscardedConjunctions(productLineTestGeneration.getNumberOfDiscardedConjunctions()+1);
					ta2kt=null;
					break;
				}
				
				this.timeTaken= duration;

				this.scopeUsed = scope;


				if(verbose==true)
				{System.out.println("Answer " +modelCopy.toString()+" : ");
				System.out.println("Time taken: " +duration+" ms");}

				modelCopy=modelCopy+1;

				// If satisfiable...
				ans = ta2kt.getAns();
				if (ans!=null&&ans.satisfiable()) {
					if(verbose==true)
					{System.out.println("The Conjunction Tuple "+this.name+" is satisfiable!");}

					this.outputSolution=ans;
					if(this.outputSolution==null)
					{
						System.out.println("Null solution!");

					}
					//System.out.println("here!"+ans.toString());
					isSolved=true;
					ta2kt= null;
				} else {
					isSolved=false;

					ta2kt=null;
				}
			}
			scope++;
		}
		if (verbose)
			System.out.println("end of solving...");
		//System.gc(); to call it explicitly or not that is the question... ;)
		return isSolved;   
	}

	/**
	 * @return the solveThreadFinished
	 */
	public boolean isSolveThreadFinished() {
		return solveThreadFinished;
	}

	/**
	 * @param solveThreadFinished the solveThreadFinished to set
	 */
	public void setSolveThreadFinished(boolean solveThreadFinished) {
		this.solveThreadFinished = solveThreadFinished;
	}


}



class ConfigurationGeneration
{
	public ArrayList<ConjunctionTuple> Pool;
	public TupleSet Initial;
	Integer Twise;
	ArrayList<Feature> productFeatures; 
	String root;
	String filename;
	String tempFileName;
	String solutionPath;
	Integer minScopeDetect;
	Integer maxScopeDetect;
	Integer minScope;
	Integer maxScope; 
	Integer maxDurationDetect;
	Integer maxDurationExp;
	ExperimentLog BinarySplitExperiment;
	ExperimentLog IncrementalGrowthExperiment;
	TestSuite testModels;
	private boolean isIncremental;

	public ConfigurationGeneration(Integer Twise, 
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
		this.Twise = Twise;
		this.productFeatures=productFeatures;
		this.root= root;
		this.filename= filename;
		this.tempFileName= tempFileName;
		this.solutionPath=solutionPath;
		this.minScopeDetect = minScopeDetect;
		this.maxScopeDetect = maxScopeDetect;
		this.minScope = minScope;
		this.maxScope = maxScope;
		this.maxDurationDetect=maxDurationDetect;
		this.maxDurationExp = maxDurationExp;
		this.BinarySplitExperiment=new ExperimentLog();
		this.IncrementalGrowthExperiment = new ExperimentLog();
		Pool = new ArrayList<ConjunctionTuple>();
		Initial = new TupleSet();
		Initial.createCreateAllTuples(productFeatures,Twise);
		Initial.getVaildTuples(root,filename,tempFileName, minScopeDetect, maxScopeDetect, maxDurationDetect);
		

			}

	public boolean isIncremental() {
		return isIncremental;
	}

	public String showTupleSet(ArrayList<Tuple> input)
	{
		String tupleString="";

		for(int i=0;i<input.size();i++)
		{
			//System.out.println(input.get(i).number);
			tupleString=tupleString + "Tuple"+input.get(i).number +",";
		}

		tupleString="{" +tupleString.substring(0,tupleString.length()-1)+"}";
		return tupleString; 
	}
	public static boolean deleteDir(File dir) {

		if (dir.isDirectory()) {
			String[] children = dir.list();
			for (int i=0; i<children.length; i++) {
				File x= new File(dir, children[i]);
				boolean success = x.delete();
				if (!success) {
					return false;
				}
			}
		}

		// The directory is now empty so delete it

		return true;
	}


	public void cleanUpSolutions(String solutionPath)
	{

		File dir = new File(solutionPath);

		Boolean success = deleteDir(dir);

		if(success==true)
		{
			System.out.println("Clean up of solution directory successful...");
		}
		else
		{
			System.out.println("Clean up of solution directory failed...");
		}

	}
	public void fillPoolIncremental(Integer solutionNumber) throws Err, IOException
	{
		isIncremental = true;
		ArrayList<Tuple> currentTupleSet=new ArrayList<Tuple>();
		A4Solution currentSolution=null;

		ArrayList<Tuple> remainingTupleSet=new ArrayList<Tuple>();
		remainingTupleSet.addAll(Initial.validTupleSet);
		Integer setNumber = 1;



		//System.out.println("Remaining tuples are...");
		//this.showTupleSet(remainingTupleSet);

		Pool.clear();
		Boolean result= true;

		while(!remainingTupleSet.isEmpty())
		{


			ConjunctionTuple temp=new ConjunctionTuple();

			temp.tuples=new ArrayList<Tuple>();
			temp.tuples.clear();
			currentTupleSet.clear();
			System.out.println("\nCreating test set number "+setNumber);
			result=false;
			do
			{
				if(temp.outputSolution!=null)
				{currentSolution=temp.outputSolution;}
				//System.out.println("Current Status:"+this.showTupleSet(currentTupleSet));
				int tupleIndex= 0;
				tupleIndex= Initial.selectNextTuple(currentTupleSet,remainingTupleSet, SelectStrategy.RANDOM);
				//System.out.println("Selected Tuple="+t.getName());
				//Randomly select a tuple and add it to the current set of tuples
				currentTupleSet.add(remainingTupleSet.get(tupleIndex));
				remainingTupleSet.remove(tupleIndex);
				int lastPosition = currentTupleSet.size()-1;
				//Create a conjunction of the tuple
				temp=new ConjunctionTuple(setNumber,Initial.baseAlloyModel,this.root,this.tempFileName,currentTupleSet);
				//productLineTestGeneration.setNumberOfconjunctions(productLineTestGeneration.getNumberOfconjunctions()+1);

				//System.out.println("Tuples added in pool=");
				//System.out.println(this.showTupleSet(temp.tuples));
				//Solve the conjuction
				result=temp.solve(this.minScope, this.maxScope, this.maxDurationExp);
				this.IncrementalGrowthExperiment.add((int)temp.timeTaken, (int)temp.scopeUsed);
				//System.out.println("Result= "+result);
				if(result==false)
				{
					//System.out.println(" Not adding "+currentTupleSet.get(lastPosition).getName());
					remainingTupleSet.add(currentTupleSet.get(lastPosition));
					currentTupleSet.remove(lastPosition);
					temp.outputSolution=currentSolution;
					temp.tuples.clear();
					temp.tuples.addAll(currentTupleSet);
					//System.out.println("Final Status:"+this.showTupleSet(temp.tuples)+" of set "+setNumber);
				}
				if(result==true)
				{
					//System.out.println("Current Status:"+this.showTupleSet(temp.tuples)+" of set "+setNumber);

				}
				if(remainingTupleSet.isEmpty())
				{

					temp.tuples.clear();
					temp.tuples.addAll(currentTupleSet);
					//	System.out.println("Final Status:"+this.showTupleSet(temp.tuples)+" of set "+setNumber);
				}


			}while(result == true && !remainingTupleSet.isEmpty());

			//System.out.println("Current tuple set is =");
			//System.out.println(this.showTupleSet(currentTupleSet));
			//Insert the current set of tuples to the Pool
			//	Product p = new Product();
			//	p.setSolution(solutionNumber, temp.outputSolution);
			//	this.testModels.addProduct(p);
			Pool.add(temp);
			//Save tuple into a file
			String solutionFileName="Set"+setNumber+"_"+this.Twise+"_wise_tuples"+".xml";
			String solDirectoy =this.root+this.solutionPath+"/Solution"+solutionNumber;
			boolean success = (new File(solDirectoy)).mkdir();
			if (success) {
				System.out.println("Solution Directory: " + solDirectoy + " created");
			}   
			temp.dumpSolution(this.root,this.solutionPath+"/Solution"+solutionNumber+"/"+solutionFileName);


			//System.out.println("Tuples added in pool=");
			//	System.out.println(this.showTupleSet(Pool.get(0).tuples));

			remainingTupleSet.removeAll(currentTupleSet);


			if(!remainingTupleSet.isEmpty())
			{
				//	System.out.println("Remaining tuples are...");
				//	System.out.println(this.showTupleSet(remainingTupleSet));
			}
			setNumber = setNumber+1;

		}
		//Compute the values in the experiment logger
		this.IncrementalGrowthExperiment.compute();
		this.IncrementalGrowthExperiment.numberOfSolutions=Pool.size();
		//System.out.println(this.IncrementalGrowthExperiment);
		this.IncrementalGrowthExperiment.solutionNumber=solutionNumber;
		String solutionResultName="Solution"+solutionNumber+"_result"+".txt";
		this.IncrementalGrowthExperiment.save(this.root+this.solutionPath+"/Solution"+solutionNumber+"/"+solutionResultName);

	}

	public ArrayList<Tuple> orderRandom(ArrayList<Tuple> tupleSet)
	{
		Random rgen = new Random(); 

		for (int i=0; i<tupleSet.size(); i++) {
			int randomPosition = rgen.nextInt(tupleSet.size());
			Tuple temp = tupleSet.get(i);
			tupleSet.set(i, tupleSet.get(randomPosition));
			tupleSet.set(randomPosition, temp);
		}
		return tupleSet;


	}
	public int getIndexLargest(ArrayList<ConjunctionTuple> current)
	{

		int index=0;
		int maxValue=0;

		for(int i=0;i<current.size();i++)
		{
			if (current.get(i).tuples.size() > maxValue)
			{
				maxValue=current.get(i).tuples.size();
				index=i;
			}
		}


		return index;
	}
	public ArrayList<ConjunctionTuple> selectAndSplit(int setNumber, ArrayList<ConjunctionTuple> setOfConjunctions, SplitSelectStrategy strategy)
	{


		if (strategy==SplitSelectStrategy.LARGEST)
		{
			// Random generator = new Random();
			int maxIndex = this.getIndexLargest(setOfConjunctions);
			ConjunctionTuple current = setOfConjunctions.get(maxIndex);


			ArrayList<Tuple> half1 = new ArrayList<Tuple>();
			ArrayList<Tuple> half2 = new ArrayList<Tuple>();
			ConjunctionTuple half1conj = new ConjunctionTuple();
			ConjunctionTuple half2conj = new ConjunctionTuple();

			if(current.tuples.size()==1)
			{
				System.out.println("Size is unity. Cannot be split further");
				return setOfConjunctions;

			}
			if(current.tuples.size()>1)
			{
				int halfPoint = (int) Math.floor(current.tuples.size()/2);
				half1.addAll(current.tuples.subList(0,halfPoint));
				half2.addAll(current.tuples.subList(halfPoint+1, current.tuples.size()-1));
				//System.out.println("Number of tuples in first half="+half1.size());
				//System.out.println("Number of tuples in second half="+half2.size());
				half1conj=new ConjunctionTuple(setNumber,Initial.baseAlloyModel,this.root,this.tempFileName,half1);			
				setNumber = setNumber+1;
				half2conj=new ConjunctionTuple(setNumber,Initial.baseAlloyModel,this.root,this.tempFileName,half2);
				//Remove the split entity
				setOfConjunctions.remove(maxIndex);
				//Add the entities after the split
				setOfConjunctions.add(half1conj);
				setOfConjunctions.add(half2conj);
			}

		}
		return setOfConjunctions;


	}

	public void fillPoolBinary(Integer solutionNumber) throws Err, IOException
	{
		isIncremental = false;

		ArrayList<Tuple> initialTupleSet=new ArrayList<Tuple>();


		initialTupleSet.addAll(Initial.validTupleSet);

		//Random ordering of initial set of tuples

		initialTupleSet = this.orderRandom(initialTupleSet);
		Integer setNumber = 1;
		Boolean result=false;
		Boolean Allresult=true;
		ArrayList<ConjunctionTuple> setOfConjunctions = new ArrayList<ConjunctionTuple>();
		ConjunctionTuple initialConjunction = new ConjunctionTuple();

		initialConjunction=new ConjunctionTuple(setNumber,Initial.baseAlloyModel,this.root,this.tempFileName,initialTupleSet);
		ConjunctionTuple temp=new ConjunctionTuple();
		setOfConjunctions.clear();
		setOfConjunctions.add(initialConjunction);
		Pool.clear();
		System.out.println("Number of valid tuples=" + initialTupleSet.size());
		//System.out.println("Number of valid conjunctions=" + setOfConjunctions.size());
		//productLineTestGeneration.setNumberOfconjunctions(setOfConjunctions.size());
		do
		{
			Allresult=true;
			for(int i=0;i<setOfConjunctions.size();i++)
			{

				temp=setOfConjunctions.get(i);
				result=temp.solve(this.minScope, this.maxScope, this.maxDurationExp);
				Allresult=Allresult && result;

			}
			if(Allresult==true)
			{
				Pool.addAll(setOfConjunctions);
				for(int i=0;i<Pool.size();i++)
				{
					//System.out.println("Element i="+i);
					temp=Pool.get(i);
					this.BinarySplitExperiment.add((int)temp.timeTaken,(int)temp.scopeUsed);
				}
			}
			//System.out.println("All result="+Allresult);
			setOfConjunctions=selectAndSplit(setNumber,setOfConjunctions,SplitSelectStrategy.LARGEST);

			if(Allresult==false)
			{
				Pool.clear();
			}
			if (Pool.size()==Initial.validTupleSet.size())
			{

				break;
			}



		}while(Allresult==false);



		for(int i=0;i<Pool.size();i++)
		{
			temp=Pool.get(i);	
			String solutionFileName="Set"+i+"_"+this.Twise+"_wise_tuples"+".xml";
			String solDirectoy =this.root+this.solutionPath+"/Solution"+solutionNumber;
			boolean success = (new File(solDirectoy)).mkdir();
			if (success) {
				System.out.println("Solution Directory: " + solDirectoy + " created");
			}   

			//Product p = new Product();
			//p.setSolution(solutionNumber, temp.outputSolution);
			//this.testModels.addProduct(p);

			temp.dumpSolution(this.root,this.solutionPath+"/Solution"+solutionNumber+"/"+solutionFileName);
		}
		//Compute experiment details and print
		this.BinarySplitExperiment.compute();
		this.BinarySplitExperiment.numberOfSolutions=Pool.size();
		this.BinarySplitExperiment.solutionNumber=solutionNumber;
		String solutionResultName="Solution"+solutionNumber+"_result"+".txt";
		this.BinarySplitExperiment.save(this.root+this.solutionPath+"/Solution"+solutionNumber+"/"+solutionResultName);
		//System.out.println(this.BinarySplitExperiment);

	}

	public String toString()
	{
		String PoolString = "{";
		System.out.println("\n Number of test sets = "+Pool.size());
		System.out.println("\n Test sets are:");

		PoolString="{";
		for(int i=0;i<Pool.size();i++)
		{
			System.out.println(this.showTupleSet(Pool.get(i).tuples));
			PoolString = PoolString + this.showTupleSet(Pool.get(i).tuples)+ ",";
		}
		PoolString = PoolString.substring(0,PoolString.length()-1);
		PoolString = PoolString + " }\n";


		return PoolString;

	}

}

public final class productLineTestGeneration {

	private static long numberOfconjunctions=0;
	private static long numberOfDiscardedConjunctions=0;

	public static TestSuite fillTestSuite(ConjunctionTuple t) {
		TestSuite ts = new TestSuite(t.name);
		//ts.setLog(log);

		A4Solution sol = t.outputSolution;
		if (sol != null) {

			SafeList<Sig> sigs = sol.getAllReachableSigs();
			if (sigs.size()==0)
				System.out.println("no sig in solution");

			for (Sig s: sigs) {

				if (s.label.contains("/Configuration")) {
					try {
						//System.out.println("found signature " + s.label);
						A4TupleSet tset = (A4TupleSet) sol.eval(s);
						SafeList<Field> fs= s.getFields();
						Iterator<A4Tuple> it = tset.iterator();

						if (tset.size()==0)
							System.out.println("it seems that tuple set have not been solved...");

						while (it.hasNext()) {
							String name = it.next().atom(0);
							//System.out.println("atom: "+ name);

							Product p = new Product(name);
							ArrayList<A4TupleSet> fieldTuples = new ArrayList<A4TupleSet>();
							for (Field f: fs) {
								fieldTuples.add((A4TupleSet)sol.eval(f));
							}
							p.setFeatures(getFeatureFromFields(name,fieldTuples));
							//prods.put(name, p);
							ts.addProduct(p);

						}
					} catch (Err e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				}



			}
		} else {
			System.out.println("Alloy crash on getting the solution...");
		}

		return ts;
	}

	private static TestSuite mergeTestSuites(ArrayList<TestSuite> lts,String name) {
		TestSuite ts = new TestSuite(name);

		for (int i=0;i<lts.size();i++) {
			ArrayList<Product> prods = lts.get(i).getProducts();

			for (Product p: prods) {
				p.setName(p.getName()+"_" + i);
			}

			ts.addAllProducts(prods);


		}

		return ts;

	}

	private static ArrayList<Feature> getFeatureFromFields(String productName, ArrayList<A4TupleSet> fieldTuples) {
		ArrayList<Feature> features = new ArrayList<Feature>();

		for (A4TupleSet tuple : fieldTuples) {
			Iterator<A4Tuple> it = tuple.iterator();
			while (it.hasNext()) {
				A4Tuple a4Tuple = it.next();
				String name = a4Tuple.atom(0);

				if (name.equals(productName)) {
					String fname = a4Tuple.atom(1).split("\\$\\d*")[0];
					//	System.out.println("adding " + fname + " to product " + productName);
					features.add(new Feature(fname));
				}
			}
		}

		return features;
	}

	public static void main(String[] args) throws Err, IOException, InterruptedException {

		//Input Alloy File
		//Change the root on a different machine
		// String sagar_root = new String("/Users/sagarsen/Documents/ProductLineTesting/ProductLineTesting");
		String sagar_root = new String("/Users/sagarsen/Desktop/AllEclipses/CartierDemo/productLineTesting/ProductLineTesting/ProductLineTesting");
		String gilles_root = new String("/Users/gilles.perrouin/gilles.perrouin/Eclipse-workspaces/yan-dev-wksp/ProductLineTesting/ProductLineTesting");
		String root = sagar_root;
		String filename = new String("/Temp/models/base.als");
		String tempFileName = new String("/Temp/models/current.als");
		String solutionPath = new String("/Temp/solutions");
		ArrayList<TestSuite> tests = new ArrayList<TestSuite>();

		//testModels1=new TestSuite("BinarySplit_5_100ms");
		//testModels2=new TestSuite("Incremental_5_100ms");

		//TupleSet test=new TupleSet();
		Integer numberOfSolutions =4;
		/*Feature f1 = new Feature(1);
        f1.fm_name = "Transaction";
        Feature f2 = new Feature(2);
        f2.fm_name ="Nested";
        Feature f3 = new Feature(3);
        f3.fm_name="Recovering";
        Feature f4 = new Feature(4);
        f4.fm_name="ConncurrencyControlStrategy";
        Feature f5 = new Feature(5);
        f5.fm_name="PhysicalLogging";
        Feature f6 = new Feature(6);
        f6.fm_name="TwoPhaseLocking";
        Feature f7 = new Feature(7);
        f7.fm_name="OptimisticValidation";
        Feature f8 = new Feature(8);
        f8.fm_name="CheckPointing";
        Feature f9 = new Feature(9);
        f9.fm_name="Deferring";
        Feature f10 = new Feature(10);
        f10.fm_name="OutcomeAware";
        Feature f11 = new Feature(11);
        f11.fm_name="Checkpointable";
        Feature f12 = new Feature(12);
        f12.fm_name="Tracing";
        Feature f13 = new Feature(13);
        f13.fm_name="Context";
        Feature f14 = new Feature(14);
        f14.fm_name="Copyable";
        Feature f15 = new Feature(15);
        f15.fm_name="Traceable";
        Feature f16 = new Feature(16);
        f16.fm_name="Shared";
        Feature f17 = new Feature(17);
        f17.fm_name="SemanticClassified";
        Feature f18 = new Feature(18);
        f18.fm_name="AccessClassified";
        Feature f19 = new Feature(19);
        f19.fm_name="Lockable";*/



		Runtime forGC= Runtime.getRuntime();

		//ArrayList<Feature> x = new ArrayList<Feature>();

		AlloyFeatureExtractor extract = new AlloyFeatureExtractor();

		ArrayList<Feature> x = extract.extractFeaturesFromALS(root+filename);


		/*x.add(f1);
        x.add(f2);
        x.add(f3);
        x.add(f4);
        x.add(f5);
        x.add(f6);
        x.add(f7);
        x.add(f8);
        x.add(f9);
        x.add(f10);
        x.add(f11);
        x.add(f12);
        x.add(f13);
        x.add(f14);
        x.add(f15);
        x.add(f16);
        x.add(f17);
        x.add(f18);
        x.add(f19);*/

		long timeBeforeGeneration = System.currentTimeMillis();
		System.out.println("\nDetecting valid tuples...");

		ConfigurationGeneration experiment1 = new ConfigurationGeneration(2,x,root,filename,tempFileName,solutionPath,1,2,4,5,50,1000);

		System.out.println("\nCleaning up solution directory...");
		experiment1.cleanUpSolutions(root+solutionPath);
		System.out.println("\nSolving and creating minimal sets...");

		// init the graph for comuting metrics over the set of solutions
		FeatureModel2JGraph fm2jg = new FeatureModel2JGraph(root+"/feature-models/cellPhoneSPL.xmi"); 
		//FeatureModel2JGraph fm2jg = new FeatureModel2JGraph(root+"/feature-models/transactionFeatureDiagram.xmi");
		fm2jg.createUGraphFromFD();
		// if you want to see the generated hierarchy graph: System.out.println(fm2jg.getUgraph().toString());

		MetricsStore ms = new MetricsStore();
		ms.initCSV(root+solutionPath);
		//Logger.getLogger("Redundancy").setLevel(Level.OFF);

		System.out.println("\nCreating Solutions");

		for(int i=0;i<numberOfSolutions;i++)
		{
			System.out.println("Solution Number "+i);
			experiment1 = new ConfigurationGeneration(2,x,root,filename,tempFileName,solutionPath,1,2,4,5,50,3000);

			//experiment1.fillPoolBinary(i+1);
			experiment1.fillPoolIncremental(i+1);

			// populating test suites 
			for (ConjunctionTuple t: experiment1.Pool) {
				//System.out.println(t);
				TestSuite ts = fillTestSuite(t);
				tests.add(ts);
				//System.out.println(ts.toString());
			}

			// forming the actual solution for one testSuite
			String suiteName;
			TestSuite t;
			if (experiment1.isIncremental())  {
				suiteName = "Incremental_scope[" + experiment1.minScope.toString() + "," + experiment1.maxScope.toString() +"]" + "_duration_" + experiment1.maxDurationExp.toString() + "_solution#_" + i;  
				t = mergeTestSuites(tests,suiteName);
			} else {
				suiteName = "Binary_scope[" + experiment1.minScope.toString() + "," + experiment1.maxScope.toString() +"]" + "_duration_" + experiment1.maxDurationExp.toString() + "_solution#_" + i;
				t = mergeTestSuites(tests,suiteName);
			}
			//System.out.println("Product is =");
			//System.out.println(t.toString());
			try {
			String solNumber;
			solNumber = new Integer(i+1).toString();
			FileWriter productTextFile = new FileWriter(root+"/Temp/solutions/products"+solNumber+".txt");
			PrintWriter out = new PrintWriter(productTextFile);
			out.println(t.toString());
			out.close();
			} catch (IOException e){
				   e.printStackTrace();
			}

			//Redundancy computation starts here
			//The redundancy computation needs to be optimized
			
			Redundancy r = new Redundancy(fm2jg,t,experiment1.Initial);


			//r.computeTupleSetRedundancy();
			//r.computeRedundancy();
			t.setNumberOfSteps(experiment1.IncrementalGrowthExperiment.numberOfSteps);
			//t.setNumberOfSteps(experiment1.BinarySplitExperiment.numberOfSteps);
			//t.setTotalTime(experiment1.BinarySplitExperiment.totalTime);
			t.setTotalTime(experiment1.IncrementalGrowthExperiment.totalTime);

			ms.addSolutionSuite(t);
			ms.addRedundancy(r);


			ms.setMaxDurationDetect(experiment1.maxDurationDetect);
			ms.setMaxDurationExp(experiment1.maxDurationExp);
			ms.setMaxScope(experiment1.maxScope);
			ms.setMaxScopeDetect(experiment1.maxScopeDetect);

			ms.setMinScope(experiment1.minScope);
			ms.setMinScopeDetect(experiment1.minScopeDetect);
			ms.setDiscardedConjunctions(getNumberOfDiscardedConjunctions());
			ms.setConjunctions(getNumberOfconjunctions());
			tests.clear();
			// ms.writeCSVincremental();
			//Garbage collection
			 
			forGC.gc();
		}
		long timeAfterGeneration = System.currentTimeMillis();

		System.out.println("Time required to generate solutions and storing them: " + new Long(timeAfterGeneration-timeBeforeGeneration));

		System.out.println("\nSolutions available in "+root+solutionPath);

		System.out.println("Metrics: ");
		long tbf = System.currentTimeMillis();

		//Thread t= Thread.currentThread();
		/*
		ms.computeThreadedMetrics();
		long taft = System.currentTimeMillis();
		System.out.println("metrics duration: " + new Long(taft-tbf).toString());
		System.out.println(ms.toString());

		ms.writeCSV(root+solutionPath);
		*/
		//ms.closeCSV();




		// print the considered TestSuite
		//System.out.println(tests.get(0).toString());





	}

	/**
	 * @return the numberOfconjunctions
	 */
	public static long getNumberOfconjunctions() {
		return numberOfconjunctions;
	}

	/**
	 * @param numberOfconjunctions the numberOfconjunctions to set
	 */
	public static void setNumberOfconjunctions(long numberOfconjunctions) {
		productLineTestGeneration.numberOfconjunctions = numberOfconjunctions;
	}

	/**
	 * @return the numberOfDiscardedConjunctions
	 */
	public static long getNumberOfDiscardedConjunctions() {
		return numberOfDiscardedConjunctions;
	}

	/**
	 * @param numberOfDiscardedConjunctions the numberOfDiscardedConjunctions to set
	 */
	public static void setNumberOfDiscardedConjunctions(
			long numberOfDiscardedConjunctions) {
		productLineTestGeneration.numberOfDiscardedConjunctions = numberOfDiscardedConjunctions;
	}
}