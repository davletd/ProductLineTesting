/**
 * 
 */
package fr.irisa.triskell.twise.generation;

import java.util.ArrayList;

/**
 * @author gperroui
 * This class serves to store the results of T_wise generation
 * 
 */
public class TestSuite {

	private String name;
	private ArrayList<Product> products;
	private int totalTime;
	private int numberOfSteps;
	
	public TestSuite(String name) {
		this.name = name;
		this.products = new ArrayList<Product>();
	}

	public TestSuite(String name,ArrayList<Product> products) {
		this.name = name;
		this.products = products;
	}

	/**
	 * @return the name
	 */
	public String getName() {
		return name;
	}

	/**
	 * @return the products
	 */
	public ArrayList<Product> getProducts() {
		return products;
	}

	/**
	 * @param the products to be set
	 */
	public void setProducts(ArrayList<Product> products) {
		this.products = products;
	}

	/**
	 * @param the product to be added
	 */
	public void addProduct(Product product) {
		this.products.add(product);
	}
	/**
	 * 
	 * @param prods
	 */
	public void addAllProducts(ArrayList<Product> prods) {
		this.products.addAll(prods);
	}

	@Override
	public String toString() {
		String str;

		str="TestSuite: " + this.name +"\n";
		str+="number of products in the suite: " + this.products.size() + "\n"; 
		for (Product p: products)
			str+= p.toString();

		return str;
	}
	
	
	public String toVector() {
		String str;
		int i=1;
		str ="";
		for (Product p: products)
		{
			str+="Product "+i+" =: \n";
			str+= p.toVector() +" "+"\n";
			i++;
		}
		return str;
	}

	/**
	 * @return the totalTime
	 */
	public int getTotalTime() {
		return totalTime;
	}

	/**
	 * @param totalTime the totalTime to set
	 */
	public void setTotalTime(int totalTime) {
		this.totalTime = totalTime;
	}

	/**
	 * @return the numberOfSteps
	 */
	public int getNumberOfSteps() {
		return numberOfSteps;
	}

	/**
	 * @param numberOfSteps the numberOfSteps to set
	 */
	public void setNumberOfSteps(int numberOfSteps) {
		this.numberOfSteps = numberOfSteps;
	}
	
    
	
	
	
}
