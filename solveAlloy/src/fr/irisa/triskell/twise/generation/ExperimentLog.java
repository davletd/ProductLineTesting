/**
 * 
 */
package fr.irisa.triskell.twise.generation;

import java.io.IOException;
import java.util.ArrayList;

/**
 * @author gperroui
 *
 */
/**
 * 
 * Experiment Logger
 */

public class ExperimentLog
{
	
	public ArrayList<Integer> timesTaken;
	public ArrayList<Integer> scopes;
	public int numberOfSteps;
	public int totalTime;
	public int numberOfSolutions;
	public long numberOfDiscardedConjunctions;
	public int solutionNumber;
	public ArrayList<Integer> conjunctionSizes;
	
	public ExperimentLog()
	{
		timesTaken = new ArrayList<Integer>();
		timesTaken.clear();
		scopes = new ArrayList<Integer>();
		scopes.clear();
		
		numberOfSteps=0;
		totalTime=0;
		numberOfSolutions=0;
	}
	
	public void add(Integer time,Integer scope)
	{
		timesTaken.add(time);
		scopes.add(scope);
	}
	
	public void compute()
	{
		this.totalTime=0;
		//System.out.println("Total solutions"+timesTaken.size());
		for(int i=0;i<timesTaken.size();i++)
		{
			totalTime=totalTime+timesTaken.get(i);
		}
		numberOfSteps=timesTaken.size();
		
	}
	
	public String toString()
	{
		String stringValue = "Solution Number ="+this.solutionNumber;
		
		stringValue=stringValue+"\nStep\t\tTime Taken(ms)\t\tScope \n";
		for(int i=0;i<timesTaken.size();i++)
		{
			stringValue=stringValue+i+"\t\t"+this.timesTaken.get(i) +"\t\t"+this.scopes.get(i)+"\n";
		}
		stringValue = stringValue+"\n Total Steps="+numberOfSteps;
		stringValue = stringValue+"\n Total Time="+totalTime;
		stringValue = stringValue+"\n Number of solutions="+numberOfSolutions;
		return stringValue;
	}
	
	public void save(String path) throws IOException
	{
		String experimentLog = this.toString();
		java.io.PrintWriter out = new java.io.PrintWriter(new java.io.FileWriter(path));
	    out.print(experimentLog);
	    out.close();

	}

	/**
	 * @return the numberOfDiscardedConjunctions
	 */
	public long getNumberOfDiscardedConjunctions() {
		return numberOfDiscardedConjunctions;
	}

	/**
	 * @param numberOfDiscardedConjunctions the numberOfDiscardedConjunctions to set
	 */
	public void setNumberOfDiscardedConjunctions(long numberOfDiscardedConjunctions) {
		this.numberOfDiscardedConjunctions = numberOfDiscardedConjunctions;
	}
}
