/**
 * 
 */
package fr.irisa.triskell.twise.generation;

import java.util.ArrayList;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;

/**
 * @author gperroui
 * This class serves to describe a product (considered as a list of features) 
 */
public class Product implements Comparable<Product> {

	private String name;
	private ArrayList<Feature> features;
	public A4Solution solution;
	public Integer solutionNumber;

	public Product()
	{}

	public Product(String name) {
		this.name=name;
	}
	public Product(String name, ArrayList<Feature> features) {
		this.name = name;
		this.features = features;
	}
	/**
	 * @deprecated this is not needed anymore.
	 * @param solutionNumber
	 * @param sol
	 */
	public void setSolution(Integer solutionNumber, A4Solution sol)
	{
		this.solutionNumber=solutionNumber;
		this.solution = sol;
	}
	/**
	 * @return the name
	 */
	public String getName() {
		return name;
	}

	/**
	 * @param name the name to set
	 */
	public void setName(String name) {
		this.name = name;
	}

	/**
	 * @return the features
	 */
	public ArrayList<Feature> getFeatures() {
		return features;
	}

	/**
	 * @param features the features to set
	 */
	public void setFeatures(ArrayList<Feature> features) {
		this.features = features;
	}

	/* (non-Javadoc)
	 * @see java.lang.Comparable#compareTo(java.lang.Object)
	 */
	public int compareTo(Product p) {
		if (p != null)
			return getName().compareTo(p.getName());
		else
			return -1;

		//return 0;
	}
	public String toString() {
		String str;

		str = "product name: " + this.name + "\n";
		str += "Features: " + "\n";
		if (features != null) {
			for (Feature f : features)
				str += f.fm_name+"	";

		}
		return str;
	}
	
	public String toVector() {
		String str;

		str ="";
		if (features != null) {
			for (Feature f : features)
				str += f.fm_name+"	";

		}
		return str;
	}


}
