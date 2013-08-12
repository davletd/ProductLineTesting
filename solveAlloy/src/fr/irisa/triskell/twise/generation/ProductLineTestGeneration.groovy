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
import java.math.*;

import lu.uni.lassy.metrics.AlloyFeatureExtractor;
import lu.uni.lassy.metrics.FeatureModel2JGraph;
import lu.uni.lassy.metrics.MetricsStore;
import lu.uni.lassy.metrics.Redundancy;

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
import groovy.*;
import groovy.io.*;


//Enumeration for strategy selection
enum SelectStrategy {RANDOM, DISTANCE};
enum SplitSelectStrategy {LARGEST};




public final class ProductLineTestGeneration 
{
	private static long numberOfconjunctions_ = 0
	private static long numberOfDiscardedConjunctions_ = 0

	public static TestSuite fillTestSuite(ConjunctionTuple cTuple) 
	{
		def testSuite = new TestSuite(cTuple.name)
		def solution = cTuple.outputSolution
		
		if (solution == null) {
			println "Alloy crash on getting the solution..."
			return testSuite
		}
		
		def sigs = solution.getAllReachableSigs()
		if (sigs.empty)
			println "no sig in solution"

		for (def sig: sigs) {

			if (!sig.label.contains("/Configuration"))
				continue
				
			try {
				def tupleSet = (A4TupleSet) solution.eval(sig)
				SafeList<Field> fs = sig.getFields()
				def it = tupleSet.iterator()

				if (!tupleSet.any())
					println "it seems that tuple set have not been solved..."

				while (it.hasNext()) {
					def name = it.next().atom(0)
					def product = new Product(name)
					def fieldTuples = new ArrayList<A4TupleSet>()
					for (Field f: fs) {
						fieldTuples.add((A4TupleSet)solution.eval(f))
					}
					product.setFeatures(getFeatureFromFields(name,fieldTuples))
					testSuite.addProduct(product)
				}
			} 
			catch (Err e) {
				e.printStackTrace()
			}				
		} 

		return testSuite
	}

	private static TestSuite mergeTestSuites(ArrayList<TestSuite> testSuiteList,String name) 
	{
		def testSuite = new TestSuite(name)

		for(testSuites in testSuiteList) {
			def products = testSuites.getProducts()
			for (product in products) {
				product.setName(product.getName() + "_" + products.indexOf(product))
			}
			testSuite.addAllProducts(products)
		}
		return testSuite
	}

	private static ArrayList<Feature> getFeatureFromFields(String productName, ArrayList<A4TupleSet> fieldTuples) 
	{
		def features = new ArrayList<Feature>()

		for (def tuple in fieldTuples) {
			def it = tuple.iterator()
			while (it.hasNext()) {
				def a4Tuple = it.next()
				def name = a4Tuple.atom(0)

				if (name.equals(productName)) {
					String fname = a4Tuple.atom(1).split("\\\$\\d*")[0]
					features.add(new Feature(fname));
				}
			}
		}
		return features
	}

	public static void main(String[] args) throws Err, IOException, InterruptedException 
	{
		//Input Alloy File
		//Change the root on a different machine
		def currentRoot = "C:\\Project\\FD\\ProductLineTesting\\ProductLineTesting"
		def root = currentRoot
		def filename = "\\Temp\\models\\base.als"
		def tempFileName = "\\Temp\\models\\current.als"
		def solutionPath = "\\Temp\\solutions"
		
		def tests = new ArrayList<TestSuite>()
		def numberOfSolutions = 1

		Runtime forGC= Runtime.getRuntime()

		def extract = new AlloyFeatureExtractor();
		def features = extract.extractFeaturesFromALS(root+filename)

		long timeBeforeGeneration = System.currentTimeMillis()
		println "Detecting valid tuples..."

		def twise = 2
		def minScope = 1
		def maxScope = 2
		def experiment1 = new ConfigurationGenerator(2,features,root,filename,tempFileName,solutionPath,1,2,4,5,50,1000)

		println "Cleaning up solution directory..."
		experiment1.cleanUpSolutions(root+solutionPath)
		println "Solving and creating minimal sets..."

		// init the graph for comuting metrics over the set of solutions
		def fm2jg = new FeatureModel2JGraph(root+"/feature-models/cellPhoneSPL.xmi"); 
		fm2jg.createUGraphFromFD();
		// if you want to see the generated hierarchy graph: System.out.println(fm2jg.getUgraph().toString());

		def metricsStore = new MetricsStore();
		metricsStore.initCSV(root+solutionPath);

		println "Creating Solutions"

		for(i in 0..numberOfSolutions)
		{
			println "Solution Number ${i}"
			experiment1 = new ConfigurationGenerator(2,features,root,filename,tempFileName,solutionPath,1,2,4,5,50,3000)
			experiment1.fillPoolIncremental(i+1)

			// populating test suites 
			for (conjunctionTuple in experiment1.pool_) {
				def testSuite = fillTestSuite(conjunctionTuple)
				tests.add(testSuite)
			}

			// forming the actual solution for one testSuite
			def suiteName = experiment1.isIncremental() ? 
				"Incremental_scope[${experiment1.minScope_},${experiment1.maxScope_}]_duration_${experiment1.maxDurationExp_}_solution#_${i}"
				: "Binary_scope[${experiment1.minScope_},${experiment1.maxScope_}]_duration_${experiment1.maxDurationExp_}_solution#_${i}"
			def testSuite = mergeTestSuites(tests,suiteName)

			try {
				def solNumber = (i+1).toString()
				def productTextFileWriter = new FileWriter("${root}/Temp/solutions/products${solNumber}.txt");
				def out = new PrintWriter(productTextFileWriter);
				out.println(testSuite.toString());
				out.close();
			} 
			catch (IOException e){
				e.printStackTrace();
			}

			//Redundancy computation starts here
			//The redundancy computation needs to be optimized
			
			def redundancy = new Redundancy(fm2jg,testSuite,experiment1.initial_);
			testSuite.setNumberOfSteps(experiment1.incrementalGrowthExperiment_.numberOfSteps);
			testSuite.setTotalTime(experiment1.incrementalGrowthExperiment_.totalTime);

			metricsStore.addSolutionSuite(testSuite);
			metricsStore.addRedundancy(redundancy);


			metricsStore.setMaxDurationDetect(experiment1.maxDurationDetect_);
			metricsStore.setMaxDurationExp(experiment1.maxDurationExp_);
			metricsStore.setMaxScope(experiment1.maxScope_);
			metricsStore.setMaxScopeDetect(experiment1.maxScopeDetect_);

			metricsStore.setMinScope(experiment1.minScope_);
			metricsStore.setMinScopeDetect(experiment1.minScopeDetect_);
			metricsStore.setDiscardedConjunctions(getNumberOfDiscardedConjunctions());
			metricsStore.setConjunctions(getNumberOfconjunctions());
			tests.clear(); 
			forGC.gc();
		}
		
		long timeAfterGeneration = System.currentTimeMillis()

		println "Time required to generate solutions and storing them: " + (timeAfterGeneration-timeBeforeGeneration)
		println "\nSolutions available in ${root}${solutionPath}"
	}

	public static long getNumberOfconjunctions() 
	{
		return numberOfconjunctions_
	}

	public static void setNumberOfconjunctions(long numberOfconjunctions) 
	{
		ProductLineTestGeneration.numberOfconjunctions_ = numberOfconjunctions
	}

	public static long getNumberOfDiscardedConjunctions() 
	{
		return numberOfDiscardedConjunctions_
	}

	public static void setNumberOfDiscardedConjunctions(long numberOfDiscardedConjunctions) 
	{
		ProductLineTestGeneration.numberOfDiscardedConjunctions_ = numberOfDiscardedConjunctions
	}
}