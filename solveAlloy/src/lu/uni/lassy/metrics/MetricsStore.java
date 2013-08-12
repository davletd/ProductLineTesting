/**
 * 
 */
package lu.uni.lassy.metrics;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;

import fr.irisa.triskell.twise.generation.ExperimentLog;
import fr.irisa.triskell.twise.generation.Feature;
import fr.irisa.triskell.twise.generation.TestSuite;
import com.csvreader.CsvWriter;
import fr.irisa.triskell.twise.*;


/**
 * @author gperroui
 * This class serves primarily to store the results of each experiment comprised of a number of solutions... 
 */
public class MetricsStore {

    private CsvWriter writer;
    
	public MetricsStore () {
		this.solutionSuites =  new ArrayList<TestSuite>();
		this.redundancyList = new ArrayList<Redundancy>(); 
	}

	/**
	 * store one test suite per solution
	 */
	private ArrayList<TestSuite> solutionSuites;

	/**
	 * store one redundancy per solution
	 */
	private static ArrayList<Redundancy> redundancyList;

	//private synchronized ArrayList<Redundancy> finalRedundancyList;
	
	
	Integer Twise;
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
	long   discardedConjunctions;
	long   conjunctions;
	
	

	public void addSolutionSuite(TestSuite ts) {
		solutionSuites.add(ts);
	}

	public void addRedundancy(Redundancy r) {
		this.redundancyList.add(r);
	}

	public String  toString() {

		String str = new String();

		for (int i=0;i<solutionSuites.size();i++) {
			TestSuite t = solutionSuites.get(i);
			//System.out.println("adding ");
			str =str.concat(" " + t.getName() + " product redundancy: " + redundancyList.get(i).getProductRedundancy() + " tuple redundancy: " + redundancyList.get(i).getTupleSetRedundancy()+" number of generated products: "+t.getProducts().size()+
			 "\n  number of dropped conjunctions (timeout) " + discardedConjunctions + " over " + conjunctions+ "\n");

		}


		return str;

	}

	
	public void initCSV(String path) {
		writer = new CsvWriter(path+"/metrics.csv");
		
		try {
			writer.write("SolutionNumber");
			writer.write("StepNumber");
			writer.write("TotalTime");
			writer.write("ProductRedundancy");
			writer.write("TupleSetRedundancy");
			writer.write("NumberOfProducts");
			writer.endRecord();
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		
	}
	
	public void computeThreadedMetrics() {
		ExecutorService exec = Executors.newFixedThreadPool(solutionSuites.size());

		ArrayList<RedundancyThread> threads = new ArrayList<RedundancyThread>(solutionSuites.size());
		
		for (int i=0;i<solutionSuites.size();i++) {
			
			Redundancy r = redundancyList.get(i);
			
			//Callable<RedundancyThread> p=Executors.callable(new RedundancyThread(r,i));
			//threads.set(i, new RedundancyThread(r,i));
			exec.execute(new RedundancyThread(r,i));
			//exec.
			//r.computeRedundancy();
			//r.computeTupleSetRedundancy();
			//redundancyList.set(i, r);
			//System.out.println("Computed redundancy:  " + r.toString());
		}
		exec.shutdown();
		try {
			exec.awaitTermination(Long.MAX_VALUE, TimeUnit.DAYS);
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}
	
	public void computeMetrics() {
		//ExecutorService exec = Executors.newFixedThreadPool(5);


		for (int i=0;i<solutionSuites.size();i++) {
			
			Redundancy r = redundancyList.get(i);
			
			//exec.execute(new RedundancyThread(r,i));
			//exec.
			r.computeRedundancy();
			r.computeTupleSetRedundancy();
			redundancyList.set(i, r);
			System.out.println("Computed redundancy:  " + r.toString());
		}
		//exec.shutdown();
	}
	
	public void writeCSVincremental() {

		
		int last = solutionSuites.size();
		
		
			int j = last;

			TestSuite t = solutionSuites.get(last-1);
			Redundancy r = redundancyList.get(last-1);
			
			//System.out.println(new Integer(t.getNumberOfSteps()).toString() + ","+ new Integer(t.getTotalTime()).toString());
			
			
			
			try {
				writer.write("#" + new Integer(j).toString());
				writer.write(new Integer(t.getNumberOfSteps()).toString());
				writer.write(new Integer(t.getTotalTime()).toString());
				writer.write(new Double(r.getProductRedundancy()).toString());
				writer.write(new Double(r.getTupleSetRedundancy()).toString());
				writer.write(new Integer(t.getProducts().size()).toString());
				writer.endRecord();
				writer.flush();

			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		
	}
	
	public void writeCSV(String path) {

		CsvWriter writer = new CsvWriter(path+"/metrics.csv");
		
		try {
			writer.write("SolutionNumber");
			writer.write("StepNumber");
			writer.write("TotalTime");
			writer.write("ProductRedundancy");
			writer.write("TupleSetRedundancy");
			writer.write("NumberOfProducts");
			writer.endRecord();
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		
		//System.out.println("solutionSuites siez: " + solutionSuites.size());
		for (int i=0;i<solutionSuites.size();i++) {
			int j = i+1;

			TestSuite t = solutionSuites.get(i);
			Redundancy r = redundancyList.get(i);
			
			//System.out.println(new Integer(t.getNumberOfSteps()).toString() + ","+ new Integer(t.getTotalTime()).toString());
			
			
			
			try {
				writer.write("#" + new Integer(j).toString());
				writer.write(new Integer(t.getNumberOfSteps()).toString());
				writer.write(new Integer(t.getTotalTime()).toString());
				writer.write(new Double(r.getProductRedundancy()).toString());
				writer.write(new Double(r.getTupleSetRedundancy()).toString());
				writer.write(new Integer(t.getProducts().size()).toString());
				writer.endRecord();

			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			//System.out.println("adding ");
			//str =str.concat(" " + t.getName() + " product redundancy: " + redundancyList.get(i).getProductRedundancy() + " tuple redundancy: " + redundancyList.get(i).getTupleSetRedundancy()+"\n");

		}
		writer.flush();
		writer.close();


	}

	/**
	 * @param solutionSuites the solutionSuites to set
	 */
	public void setSolutionSuites(ArrayList<TestSuite> solutionSuites) {
		this.solutionSuites = solutionSuites;
	}

	/**
	 * @param redundancyList the redundancyList to set
	 */
	public void setRedundancyList(ArrayList<Redundancy> redundancyList) {
		this.redundancyList = redundancyList;
	}

	/**
	 * @param twise the twise to set
	 */
	public void setTwise(Integer twise) {
		Twise = twise;
	}

	/**
	 * @param root the root to set
	 */
	public void setRoot(String root) {
		this.root = root;
	}

	/**
	 * @param filename the filename to set
	 */
	public void setFilename(String filename) {
		this.filename = filename;
	}

	/**
	 * @param tempFileName the tempFileName to set
	 */
	public void setTempFileName(String tempFileName) {
		this.tempFileName = tempFileName;
	}

	/**
	 * @param solutionPath the solutionPath to set
	 */
	public void setSolutionPath(String solutionPath) {
		this.solutionPath = solutionPath;
	}

	/**
	 * @param minScopeDetect the minScopeDetect to set
	 */
	public void setMinScopeDetect(Integer minScopeDetect) {
		this.minScopeDetect = minScopeDetect;
	}

	/**
	 * @param maxScopeDetect the maxScopeDetect to set
	 */
	public void setMaxScopeDetect(Integer maxScopeDetect) {
		this.maxScopeDetect = maxScopeDetect;
	}

	/**
	 * @param minScope the minScope to set
	 */
	public void setMinScope(Integer minScope) {
		this.minScope = minScope;
	}

	/**
	 * @param maxScope the maxScope to set
	 */
	public void setMaxScope(Integer maxScope) {
		this.maxScope = maxScope;
	}

	/**
	 * @param maxDurationDetect the maxDurationDetect to set
	 */
	public void setMaxDurationDetect(Integer maxDurationDetect) {
		this.maxDurationDetect = maxDurationDetect;
	}

	/**
	 * @param maxDurationExp the maxDurationExp to set
	 */
	public void setMaxDurationExp(Integer maxDurationExp) {
		this.maxDurationExp = maxDurationExp;
	}

	/**
	 * close the file when the processing is finished
	 */
	public void closeCSV() {
		writer.close();
	}
	
	public static void setRedundancyValue(int i, Redundancy r) {
		redundancyList.set(i, r);
	}

	/**
	 * @param discardedConjunctions the discardedConjunctions to set
	 */
	public void setDiscardedConjunctions(long discardedConjunctions) {
		this.discardedConjunctions = discardedConjunctions;
	}

	/**
	 * @return the conjunctions
	 */
	public long getConjunctions() {
		return conjunctions;
	}

	/**
	 * @param conjunctions the conjunctions to set
	 */
	public void setConjunctions(long conjunctions) {
		this.conjunctions = conjunctions;
	}
}
