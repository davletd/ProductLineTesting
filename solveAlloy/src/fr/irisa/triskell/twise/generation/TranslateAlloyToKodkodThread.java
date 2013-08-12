/**
 * 
 */
package fr.irisa.triskell.twise.generation;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;

/**
 * @author gilles.perrouin
 *
 */
public class TranslateAlloyToKodkodThread extends Thread {

	A4Reporter rep;
	ConstList<Sig> sigs;
	Command command;
	A4Options options;
	A4Solution ans;
    long timeTaken;
   private boolean hasFinished  = false;
   long maxDuration;
   //private ConjunctionTuple tuple;

	/**
	 * @param rep
	 * @param sigs
	 * @param commands
	 * @param options
	 */
	public TranslateAlloyToKodkodThread(A4Reporter rep, ConstList<Sig> sigs,
			Command command, A4Options options, long maxDuration) {
		//super();
		this.rep = rep;
		this.sigs = sigs;
		this.command = command;
		this.options = options;
		this.maxDuration = maxDuration; 
	}
	
	public void run() {
		try {
				
				long start = System.currentTimeMillis();
				ans = TranslateAlloyToKodkod.execute_command(rep, sigs, command, options);
				//sleep(1);
				long end = System.currentTimeMillis();
				timeTaken = end - start;
				finished();
				//throw new InterruptedException();
				
			
		} catch (Err e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	/**
	 * @return the ans
	 */
	public A4Solution getAns() {
		return ans;
	}

	/**
	 * @return the timeTaken
	 */
	public long getTimeTaken() {
		return timeTaken;
	}

	/**
	 * @return the hasFinished
	 */
	public  boolean hasFinished() {
		return hasFinished;
	}
	
	public void finished() {
		//tuple.setSolveThreadFinished(true);
		//notifyAll();
		//notifyAll();
		//System.out.println("notify sent...");
		if (getTimeTaken()>maxDuration) {
			System.out.println("Thread "  + this.getName() + " should have been discarded because of time :" + getTimeTaken());
		}else
			System.out.println(" finished time taken really: " + getTimeTaken() + "for solving thread " + this.getName());
		hasFinished = true;
	}
	
}
