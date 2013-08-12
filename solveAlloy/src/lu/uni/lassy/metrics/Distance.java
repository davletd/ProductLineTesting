/**
 * 
 */
package lu.uni.lassy.metrics;

import org.jgrapht.UndirectedGraph;
import org.jgrapht.alg.DijkstraShortestPath;
import org.jgrapht.graph.DefaultEdge;

import fr.irisa.triskell.twise.generation.productLineTestGeneration;
import fr.irisa.triskell.twise.generation.Tuple;
import java.util.*;
/**
 * @author gperroui
 * This class allows computing distances between features of the feature
 */
public class Distance {


	public double computeDistance(UndirectedGraph<String, DefaultEdge> ugraph, String fu, String fv) {


		DijkstraShortestPath<Set<String>, DefaultEdge> shortestPath = new DijkstraShortestPath(ugraph, fu, fv);

		return shortestPath.getPathLength();

	}
	/**
	 * 
	 * @param xmiFDPath the path of the feature diagram (xmi representation)
	 * @param t1 a tuple
	 * @param t2 another tuple
	 * @return the average distance between features of the tuple
	 */
	public double computeTupleDistance(UndirectedGraph<String, DefaultEdge> ugraph, Tuple t1, Tuple t2) {
		double distance = 0.0;

		int minTupleSize = 0;
		double distanceSum = 0;

		ArrayList<String> t1List = new ArrayList<String>();
		ArrayList<String> t2List = new ArrayList<String>();



		for (int i =0; i<t1.tupleFeatures.size();i++) {
			t1List.add(t1.tupleFeatures.get(i).name);
		}

		for (int i =0; i<t2.tupleFeatures.size();i++) {
			t2List.add(t2.tupleFeatures.get(i).name);
		}

		Collections.sort(t1List);
		Collections.sort(t2List);


		if (t1.tupleFeatures.size() > t2.tupleFeatures.size()) 
			minTupleSize = t2.tupleFeatures.size();
		else
			minTupleSize = t1.tupleFeatures.size();

		for (int i =0; i<minTupleSize;i++) {
			distanceSum += computeDistance(ugraph, t1List.get(i), t2List.get(i));
		}
		// we make the simple average distance 
		distance = distanceSum / (new Integer(minTupleSize)).doubleValue();

		return distance;
	}
}
