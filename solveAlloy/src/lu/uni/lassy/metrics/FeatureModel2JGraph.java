/**
 * 
 */
package lu.uni.lassy.metrics;
import java.io.IOException;
import java.util.HashMap;
import java.util.Iterator;

import org.eclipse.emf.common.util.EList;
import org.jgrapht.*;
import org.jgrapht.ext.*;
import org.jgrapht.graph.*;
import featureDiagram.*;
/**
 * @author gperroui
 * This class allows to transform an feature model instance (xmi) to JGraph 
 * so that we can use graph algorithms of the JGraph library... 
 */
public class FeatureModel2JGraph {

	private String fmPath;
	private UndirectedGraph<String, DefaultEdge> ugraph;
	private FeatureDiagram diagram;

	public FeatureModel2JGraph(String fdPath) {
		this.fmPath = fdPath;

	}

	public void createUGraphFromFD() {
		this.ugraph = new SimpleGraph<String, DefaultEdge>(DefaultEdge.class);

		try {
			this.diagram = (FeatureDiagram)EMFHelper.loadFeatureModel(this.fmPath);


			// need to implement breadthFirst to manage multiple parents !!!!
			//buildDepthFirstGraph(root.getOutgoingEdge());

			// multiparent version 
			// 1. define all the features in the ugraph
			// 2. put all the edges following the parent relationships
			buildGraph();

		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	private void buildGraph() {
		EList<Feature> features = diagram.getFeatures();

		// adding vertices
		for (Feature f: features) {
			ugraph.addVertex(f.getName());
		}

		// adding edges (only parents)
		for (Feature f: features) {
			EList<Feature>  parents = f.getParents();
			Iterator<Feature> it = parents.iterator();

			while (it.hasNext()) {
				ugraph.addEdge(f.getName(),it.next().getName());
			}


		}
	}
	// commented only valid for single parent
	/* private void buildDepthFirstGraph(EList<Edge> edges) {

	Iterator<Edge> it = edges.iterator();

	while (it.hasNext()) {
		Edge e=it.next();
		if (e.getChild() != null) {
			ugraph.addVertex(e.getChild().getName());
			ugraph.addEdge(e.getParent().getName(), e.getChild().getName());
			buildDepthFirstGraph(e.getChild().getOutgoingEdge());
		} else
			;
	}
	}*/

	/**
	 * @return the fmPath
	 */
	public String getFmPath() {
		return fmPath;
	}

	/**
	 * @return the ugraph and compute it if null
	 */
	public UndirectedGraph<String, DefaultEdge> getUgraph() {

		if (ugraph != null)  
			return ugraph;
		else {
			createUGraphFromFD();
			return ugraph;
		}

	}

	/**
	 * 
	 * @return diagram, return the feature diagram and load it if null
	 */
	public FeatureDiagram getFeatureDiagram() {
		if (diagram != null) {
			return diagram;
		} else
			try {
				this.diagram = (FeatureDiagram)EMFHelper.loadFeatureModel(this.fmPath);
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			return diagram;
	}
	/**
	 * @param args
	 */
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		FeatureModel2JGraph fm2jg = new FeatureModel2JGraph("/home/gperroui/gilles.perrouin/Eclipse-workspaces/yan-dev-wksp/ProductLineTesting/ProductLineTesting/feature-models/transactionFeatureDiagram.xmi"); 
		fm2jg.createUGraphFromFD();
		System.out.println(fm2jg.getUgraph().toString());
		Distance d = new Distance();
		System.out.println("Distance: " + d.computeDistance(fm2jg.ugraph, "Copyable", "Traceable"));
	}

}
