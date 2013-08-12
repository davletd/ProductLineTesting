/**
 * 
 */
package fr.irisa.triskell.twise.generation;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.parser.Module;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;

/**
 * @author gperroui
 *
 */
public class Tuple {

	public ArrayList<Feature> tupleFeatures
	public Integer number
	public Boolean isValid

	public Tuple()
	{}
	
	public Tuple(Integer n, Integer tupleSize)
	{
		number = n
		tupleFeatures = new ArrayList<Feature>()
		for(i in 1..tupleSize)
			tupleFeatures.add(new Feature(i))
	}
	
	def setNumber(Integer n) {
		number = n
	}

	def setTuple(ArrayList<Feature> features) {
		tupleFeatures =  features
	}

	public String toString() 
	{
		def tuple = "["
		tupleFeatures.each { it -> tuple += it + "," }
		return tuple.substring(0,tuple.length()-1)  + "]"
	}

	def getName() {
		return "Tuple${number}"
	}

	def toPredicate() {
		def predicate = "pred ${getName()} { some c: Configuration |"
		tupleFeatures.each { it -> predicate += it + " and " }	
		return predicate.substring(0,predicate.length()-4) + " } \n";		
	}

	public String getAlloyBaseModel(String alloyFile) 
	{
		//...checks on aFile are elided
		def aFile = new File(alloyFile);
		def contents = new StringBuilder();

		try {
			//use buffering, reading one line at a time
			//FileReader always assumes default encoding is OK!
			def input =  new BufferedReader(new FileReader(aFile));
			try {
				String line = null; //not declared within while loop
				/*
				 * readLine is a bit quirky :
				 * it returns the content of a line MINUS the newline.
				 * it returns null only for the END of the stream.
				 * it returns an empty String if two newlines appear in a row.
				 */
				while (( line = input.readLine()) != null){
					contents.append(line);
					contents.append(System.getProperty("line.separator"));
				}
			}
			finally {
				input.close();
			}
		}
		catch (IOException ex){
			ex.printStackTrace();
		}
		return contents.toString()
	}

	def getCommand(Integer scope) {
		"run ${getName()} for ${scope}"
	}

	public void deleteTemp(String fileName) 
	{
		def f = new File(fileName);

		// Make sure the file or directory exists and isn't write protected
		if (!f.exists())
			throw new IllegalArgumentException("Delete: no such file or directory: " + fileName);

		if (!f.canWrite())
			throw new IllegalArgumentException("Delete: write protected: " + fileName);

		// If it is a directory, make sure it is empty
		if (f.isDirectory()) {
			String[] files = f.list();
			if (files.length > 0)
				throw new IllegalArgumentException("Delete: directory not empty: " + fileName);
		}

		// Attempt to delete it
		if (!f.delete())
			throw new IllegalArgumentException("Delete: deletion failed");
	}

	public Boolean getValidity(String root,String baseAlloyName, String tempFileName, Integer min_Scope, Integer maxScope, Integer max_Duration) throws Err, IOException
	{
		Integer scope;
		String tupleAlloyString;
		isValid=false
		long maxDuration = max_Duration;
		// Alloy4 sends diagnostic messages and progress reports to the A4Reporter.
		// By default, the A4Reporter ignores all these events (but you can extend the A4Reporter to display the event for the user)
		A4Reporter rep = new A4Reporter() {
			// For example, here we choose to display each "warning" by printing it to System.out
			@Override public void warning(ErrorWarning msg) {
				System.out.print("Relevance Warning:\n"+(msg.toString().trim())+"\n\n");
				System.out.flush();
			}
		};
		//Input Alloy File
		//Change the root on a different machine

		String filename = root+baseAlloyName;
		String tempFile = root+tempFileName;
		String currentAlloyString="";
		tupleAlloyString=this.getAlloyBaseModel(filename);
		tupleAlloyString = tupleAlloyString + "\n"+this.toPredicate() +"\n" ; 
		long start;
		long end;
		long duration;
		scope=min_Scope;
		boolean verbose=false;
		while(scope<maxScope)
		{
			duration=0;
			//System.out.println(this.toPredicate());
			//System.out.println(this.getCommand(scope));

			currentAlloyString = tupleAlloyString + this.getCommand(scope);
			//Delete temp file
			this.deleteTemp(tempFile);
			//Write a new temp file
			BufferedWriter out = new BufferedWriter(new FileWriter(tempFile));
			out.write(currentAlloyString);
			out.close();
			// Parse+typecheck the model
			if(verbose)
			{System.out.println("=========== Parsing+Typechecking "+tempFile+" =============");}
			Module world = CompUtil.parseEverything_fromFile(rep, null, tempFile);

			// Choose some default options for how you want to execute the commands
			A4Options options = new A4Options();
			options.solver = A4Options.SatSolver.SAT4J;
			
			Integer modelCopy=new Integer(0);


			for (Command command: world.getAllCommands()) {
				if(verbose) 
				{System.out.println("============ Command "+command+": ============");}

				// Now run it!

				start = System.currentTimeMillis();
				if (verbose)
					System.out.println("command passed to kodkod: " + command);
				A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), command, options);
				end=System.currentTimeMillis();
				duration = end-start;

				// Print the outcome
				if(verbose)
				{System.out.println("Answer " +modelCopy.toString()+" : ");
				System.out.println("Time taken: " +duration+"ms");}

				modelCopy=modelCopy+1;


				// If satisfiable...
				if (ans.satisfiable()) {
					if(verbose)
					{System.out.println("The tuple "+this.getName()+" is satisfiable!");}
					this.isValid = true;
					return this.isValid;
				}    

				else
				{

					this.isValid =false;
					if(verbose)
					{System.out.println("No Solution Found for Tuple Predicate "+command.toString().replace(" ", "_"));}
				}


			}

			scope++;
		}

		return this.isValid;
	}

	Boolean hasDuplicates() {
		for(i in 0..tupleFeatures.size()) {
			for(j in 0..tupleFeatures.size()) {
				if( i != j && (tupleFeatures.get(i).number == tupleFeatures.get(j).number)) {
					return true
				}
			}
		}
		return false
	}
}
