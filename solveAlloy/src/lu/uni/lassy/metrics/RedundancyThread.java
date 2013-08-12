/**
 * 
 */
package lu.uni.lassy.metrics;

/**
 * @author root
 *
 */
public class RedundancyThread extends Thread {

	Redundancy r;
	int solNum;
	
	public RedundancyThread(Redundancy r, int i) {
		this.r =r;
		this.solNum = i;
		
		
	}
	
	public void run() {
		r.computeRedundancy();
		r.computeTupleSetRedundancy();
		MetricsStore.setRedundancyValue(solNum,r);
		System.out.println("Computed redundancy for solution: " + solNum);
		//System.out.println("tuple redundancy" + r.getTupleSetRedundancy());
		//System.out.println("product redundancy" + r.getProductRedundancy());
	}
	
}
