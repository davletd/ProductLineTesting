/**
 * 
 */
package fr.irisa.triskell.twise.generation

import java.io.IOException
import java.util.ArrayList
import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors
import java.util.concurrent.ScheduledExecutorService
import java.util.concurrent.TimeUnit

import edu.mit.csail.sdg.alloy4.A4Reporter
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning
import edu.mit.csail.sdg.alloy4compiler.ast.Command
import edu.mit.csail.sdg.alloy4compiler.parser.Module
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution


class ConjunctionTuple
{
	public ArrayList<Tuple> tuples
	public String name
	public Integer number
	public String baseAlloyModel
	public String tempFile
	public A4Solution outputSolution
	public String root
	public long timeTaken
	public long scopeUsed
	private boolean solveThreadFinished = false
	private def WinSolver = A4Options.SatSolver.SAT4J
	private def UnxSolver = A4Options.SatSolver.MiniSatJNI

	public ConjunctionTuple()
	{}

	public ConjunctionTuple(Integer number, String alloyModel, String root, String tempFileName, ArrayList<Tuple> tuplesInCon)
	{
		this.number = number
		this.name = "ConjunctionTuple${number}"
		this.baseAlloyModel = alloyModel
		this.tempFile = tempFileName
		this.tuples = new ArrayList<Tuple>()
		this.tuples.addAll(tuplesInCon)
		this.root = root
		this.outputSolution = null
	}


	def getPredicate() {
		def predicate = "pred ${name}{"
		tuples.each { it -> predicate += it.getName() + " and " }
		return predicate.substring(0,predicate.length()-4) +"}"
	}

	def getCommand(Integer scope) {
		" run ${name} for ${scope}"
	}

	public void dumpSolution(String path, String solutionFileName) throws Err
	{
		if ( outputSolution == null )
			return
		
		println  "Attempting to write file ${path}${solutionFileName}"
		
		if (!outputSolution.satisfiable()) 
			return
		
		// You can query "ans" to find out the values of each set or type.
		// This can be useful for debugging.
		// You can also write the outcome to an XML file
		println "Writing file  ${path}${solutionFileName}"
		outputSolution.writeXML(path+solutionFileName)
	}

	public void deleteTemp(String fileName) 
	{
		def f = new File(fileName);

		// Make sure the file or directory exists and isn't write protected
		if (!f.exists())
			throw new IllegalArgumentException("Delete: no such file or directory: " + fileName)

		if (!f.canWrite())
			throw new IllegalArgumentException("Delete: write protected: " + fileName)

		// If it is a directory, make sure it is empty
		if (f.isDirectory()) {
			def files = f.list();
			if (files.length > 0)
				throw new IllegalArgumentException("Delete: directory not empty: " + fileName)
		}
	}
	
	public synchronized Boolean solve(Integer minScope, Integer maxScope, Integer maxDuration) throws Err, IOException
	{
		def isSolved = false

		def rep = new A4Reporter() {
			// For example, here we choose to display each "warning" by printing it to System.out
			@Override public void warning(ErrorWarning msg) {
				println "Relevance Warning:\n"+(msg.toString().trim())+"\n"
				System.out.flush();
			}
		};

		Integer scope;
		long start;
		long end;
		long duration=0;
		scope = minScope;
		String currentAlloyString ="";
		Boolean verbose = true;
		String tempFileName = root + tempFile;

		def outInitial = new BufferedWriter(new FileWriter(tempFileName));
		outInitial.write(currentAlloyString);
		outInitial.close();
		Module world = null
		// Choose some default options for how you want to execute the commands
		def options = new A4Options()
		options.solver = WinSolver
		A4Solution ans
		BufferedWriter out
		def modelCopy

		//scope<=maxScope && duration <= maxDuration 
		//Changed here
		while(scope <= maxScope && duration <= maxDuration) {
			duration=0;
			currentAlloyString = "${baseAlloyModel}\n${getPredicate()}\n${getCommand(scope)}"
			deleteTemp(tempFileName);
			//Write a new temp file
			out = new BufferedWriter(new FileWriter(tempFileName))
			out.write(currentAlloyString);
			out.close();
			// Parse+typecheck the model
			if (verbose)
				println "=========== Parsing+Typechecking ${tempFileName} ============="
			world = CompUtil.parseEverything_fromFile(rep, null, tempFileName);
			def solveInDueTime = false;
			modelCopy=0;
			ExecutorService exec = Executors.newSingleThreadExecutor();
			for (command in world.getAllCommands()) {
				if(verbose)
					println "============ Command ${command}: ============"

				//TranslateAlloyToKodkodThreadController controller = new TranslateAlloyToKodkodThreadController(rep, world.getAllReachableSigs(), command, options, duration);
				ProductLineTestGeneration.setNumberOfconjunctions(ProductLineTestGeneration.getNumberOfconjunctions()+1);
				TranslateAlloyToKodkodThread ta2kt=new TranslateAlloyToKodkodThread(rep,world.getAllReachableSigs(),command,options,maxDuration); 
				ta2kt.setPriority(Thread.MIN_PRIORITY); // or MAX_PRIORITY ??? 
				exec.execute(ta2kt); 
				println "starting Solving thread" + ta2kt.getName()
				exec.shutdown()
				start = System.currentTimeMillis()
				
				try {
					solveInDueTime= exec.awaitTermination(maxDuration, TimeUnit.MILLISECONDS);
				} catch (InterruptedException e) {
					e.printStackTrace();
				}
				
				end = System.currentTimeMillis();
				duration = end-start;

				if (!solveInDueTime) {
					println "Discarded this solution : " + duration + " >= " + maxDuration+ " ms"
					ProductLineTestGeneration.setNumberOfDiscardedConjunctions(ProductLineTestGeneration.getNumberOfDiscardedConjunctions()+1);
					ta2kt = null
					break
				}
				
				timeTaken = duration;
				scopeUsed = scope;

				if(verbose) {
					println "Answer " +modelCopy.toString()+" : "
					println "Time taken: " +duration+" ms"
				}
				modelCopy++

				// If satisfiable...
				ans = ta2kt.getAns();
				if (ans != null && ans.satisfiable()) {
					if(verbose)
						println "The Conjunction Tuple ${name} is satisfiable!"

					outputSolution=ans;
					if(outputSolution==null)
						println "Null solution!"
					//System.out.println("here!"+ans.toString());
					isSolved=true;
					ta2kt= null;
				} 
				else {
					isSolved=false
					ta2kt=null
				}
			}
			scope++;
		}
		if (verbose)
			println "end of solving..."
		//System.gc(); to call it explicitly or not that is the question... ;)
		return isSolved;   
	}

	public boolean isSolveThreadFinished() {
		return solveThreadFinished;
	}

	public void setSolveThreadFinished(boolean solveThreadFinished) {
		this.solveThreadFinished = solveThreadFinished
	}


}