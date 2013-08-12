/**
 * 
 */
package lu.uni.lassy.metrics;

import java.math.BigInteger;

import fr.irisa.triskell.twise.generation.TupleSet;

/**
 * @author root
 *
 */
public class Dummy {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
	    int i = 127; // upper limit to use double...
		byte[] bn = new byte[1];
		byte[] br = new byte[1];
		bn[0]= new Integer(i).byteValue();
		//br[0]= r.byteValue();

		
		System.out.println( i+"! = " +TupleSet.bigFactorial(new BigInteger(bn)).doubleValue());

	}

}
