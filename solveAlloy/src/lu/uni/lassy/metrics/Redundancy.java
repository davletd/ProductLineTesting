/**
 * 
 */
package lu.uni.lassy.metrics;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashSet;

import org.eclipse.emf.common.util.EList;
import org.jgrapht.UndirectedGraph;
import org.jgrapht.graph.DefaultEdge;

import com.sun.jmx.remote.util.OrderClassLoaders;

import featureDiagram.FeatureDiagram;
import featureDiagram.ConstraintEdge;
import fr.irisa.triskell.twise.generation.ExperimentLog;
import fr.irisa.triskell.twise.generation.Feature;
import fr.irisa.triskell.twise.generation.Product;
import fr.irisa.triskell.twise.generation.TestSuite;
import fr.irisa.triskell.twise.generation.Tuple;
import fr.irisa.triskell.twise.generation.TupleSet;

import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * @author gperroui
 * This class compute redundancy ratio for T_wise-generated test suites 
 */
public class Redundancy {

	private  ArrayList<Product[]> cartp;
	private  FeatureModel2JGraph fm2gj;
	private   ArrayList<featureDiagram.Feature> mandatoryFeatures;
	private   double productRedundancy;
	private   double tupleSetRedundancy;
    private   TupleSet tuples;
	private  TestSuite ts;

	private boolean debug = false;

	public Redundancy(FeatureModel2JGraph fm2gj, TestSuite ts, TupleSet tuples) {
		this.fm2gj = fm2gj;
		this.ts = ts;
		this.tuples = tuples;
	}
	
	public Redundancy(FeatureModel2JGraph fm2gj, TestSuite ts) {
		this.fm2gj = fm2gj;
		this.ts = ts;
	}

	public double computeRedundancy() {
		// result 
		double ratio = 0.0;
		double[] pair_ratio;

		// general algo: 
		// 1) compute cartesian product of the test suite : i.e a set of pairs 
		// 2) For each pair of product in the cartesian product
		//   2.1) find the compulsory features for each product
		//   2.2) compute the redundancy for the two products 
		// 3) make the average of the ratio over all the products of cartesian products

		// 1.
		computeCartesian(ts);
		//cleanCartesian4Redundancy();
		pair_ratio = new double[cartp.size()];


		//lh.setLevel(Level.ALL);

		if (debug)
			System.out.println("computeRedundancy: Size of the computed Cartesian product, (pair of products): " + pair_ratio.length);
		// printing cartesian
		for (Product[] pair: cartp) {
			if (debug)
				System.out.println("computeRedundancy:Pair : { " + pair[0].getName() +","+  pair[1].getName() +"}");
		}


		// 2.
		for (int i=0;i<cartp.size();i++) {
			pair_ratio[i] = computePairRedundancy(fm2gj, cartp.get(i));
		}
		// 3.
		double sum =0.0;
		for (int i=0;i<pair_ratio.length;i++)
			sum += pair_ratio[i];

		ratio = sum / pair_ratio.length; 

		// store this value for further retrieval and analysis 
		this.productRedundancy = ratio;

		return ratio;
	}
	
	/**
	 * Compute basic cartesian product
	 * @param ts
	 */
	private  void  computeSlowCartesian(TestSuite ts) {
		long cartpBf = System.currentTimeMillis();
		
		ArrayList<Product> tmp1;
		ArrayList<Product> tmp2;
		cartp = new ArrayList<Product[]>();

		tmp1=tmp2=ts.getProducts();
		// ensuring that products are sorted the same way to avoid pair of the same product
		Collections.sort(tmp1);
		Collections.sort(tmp2);
		//System.out.println("There are " + tmp1.size()+ " and " + tmp2.size() + " products in this suite for cartesian computation");
		Product[][] pairs = new Product[tmp2.size()][2];
		
		for (int i = 0; i<tmp1.size();i++) {
			
			// System.out.println("Cartesian: first loop");

			for (int j=0;j<tmp2.size();j++) {
				//System.out.println("Cartesian second loop");
				//ArrayList<Product> pair = new ArrayList<Product>();
				pairs[j][0]= tmp1.get(i);
				pairs[j][1]= tmp1.get(j);
				//pair.add(tmp1.get(i));
				//pair.add(tmp2.get(j));

				//System.out.println("creating pair: {" + pair.get(0).getName() + "," + pair.get(1).getName() + "}");

				cartp.add(pairs[j]);
				//
			}
		}
        long cartpAft = System.currentTimeMillis();
        if (debug) {
        	System.out.println("Cartesian product duration: " + new Long(cartpAft-cartpBf).toString());
        }
	}

	
	
	/**
	 * Compute basic cartesian product
	 * @param ts
	 */
	private  void  computeCartesian(TestSuite ts) {
		long cartpBf = System.currentTimeMillis();
		
		ArrayList<Product> tmp1;
		ArrayList<Product> tmp2;
		cartp = new ArrayList<Product[]>();

		tmp1=tmp2=ts.getProducts();
		// ensuring that products are sorted the same way to avoid pair of the same product
		Collections.sort(tmp1);
		Collections.sort(tmp2);
		//System.out.println("There are " + tmp1.size()+ " and " + tmp2.size() + " products in this suite for cartesian computation");
		Product[][] pairs = new Product[tmp2.size()][2];
		
		for (int i = 0; i<tmp1.size();i++) {
			
			// System.out.println("Cartesian: first loop");

			for (int j=i+1;j<tmp2.size();j++) {
				//System.out.println("Cartesian second loop");
				//ArrayList<Product> pair = new ArrayList<Product>();
				pairs[j][0]= tmp1.get(i);
				pairs[j][1]= tmp1.get(j);
				//pair.add(tmp1.get(i));
				//pair.add(tmp2.get(j));

				//System.out.println("creating pair: {" + pair.get(0).getName() + "," + pair.get(1).getName() + "}");

				cartp.add(pairs[j]);
				//
			}
		}
        long cartpAft = System.currentTimeMillis();
        if (debug) {
        	System.out.println("Cartesian product duration: " + new Long(cartpAft-cartpBf).toString());
        }
	}

	/**
	 * 
	 * removes duplicates and symmetric pairs in the cartesian products
	 */
	private void cleanCartesian4Redundancy() {
        
		long cleanCartesianBf = System.currentTimeMillis();
		
		for (int i=0;i<cartp.size();i++) {

			// identical pair of products
			Product[] pair = cartp.get(i);

			if (pair[0].getName().equals(pair[1].getName())) {
				//System.out.println("Removing Pair : { " + pair.get(0).getName() +","+  pair.get(1).getName() +"}");
				cartp.remove(i);
			}

		}

		for (int i=0;i<cartp.size();i++) {

			// identical pair of products
			Product[] pair = cartp.get(i);

			if (findSymmetric(pair)) {
				//System.out.println("Removing Pair : { " + pair.get(0).getName() +","+  pair.get(1).getName() +"}");
				cartp.remove(i);
			}
			
		}
		if (debug)  {
			long cleanCartesianAft = System.currentTimeMillis();
			System.out.println("");
		}
	}

	private boolean findSymmetric(Product[] pair) {
		boolean res = false;

		for (int i=0;i<cartp.size();i++) {
			Product[] spair = cartp.get(i);
			if (spair[0].getName().equals(pair[0].getName()) &&
					spair[1].getName().equals(pair[0].getName()))
				return true;
		}

		return res;
	}

	private double computePairRedundancy(FeatureModel2JGraph fm2gj,Product[] pair) {
		// algorithm 
		// 1. compute the compulsory features
		// 2. compute the ratio according to the formula given in the paper 

		// init the the feature sets  
		ArrayList<Feature> pf1 = new ArrayList<Feature>(pair[0].getFeatures());
		ArrayList<Feature> pf2= new ArrayList<Feature>(pair[1].getFeatures());

		// print the feature to process 
		if (debug) {
			System.out.println("computePairRedundancy : pair redundancy pf1");
			for (int i =0;i<pf1.size();i++){
				System.out.print(" " + pf1.get(i).fm_name);
			}
			System.out.println("computePairRedundancy : pair redundancy pf2");
			//Logger.getLogger("Redundancy").log(Level.FINEST, "\n  pair redundancy pf2");
			for (int i =0;i<pf2.size();i++){
				System.out.print(" " + pf2.get(i).fm_name);
			}
		}
		// compulsory features
		ArrayList<Feature> cf1 = computeCompulsoryFeatures(fm2gj, pf1);
		ArrayList<Feature> cf2 = computeCompulsoryFeatures(fm2gj, pf2);

		// print complusory features:
		//Logger.getLogger("Redundancy").log(Level.FINEST, "\n pair redundancy cf1");

		if (debug) {
			System.out.println("computePairRedundancy : pair redundancy cf1");  
			for (int i =0;i<cf1.size();i++){
				System.out.print(" " + cf1.get(i).fm_name);
			}
			System.out.println("\n pair redundancy cf2");
			for (int i =0;i<cf2.size();i++){
				System.out.print(" " + cf2.get(i).fm_name);
			}

			System.out.println("number of compulsory features for product 1: " + cf1.size()+" over " +pf1.size() + " size " + "variability ratio : " + new Double(pf1.size()-cf1.size()) / new Double(pf1.size()));
			System.out.println("number of compulsory features for product 2: " + cf2.size()+" over " +pf2.size() + " size " + "variability ratio : " + new Double(pf2.size()-cf2.size()) / new Double(pf2.size()));
		}
		// "numerator" set
		ArrayList<Feature> num;
		ArrayList<Feature> deNum;

		// removing only if there is at least one non-compulsory feature
		if (cf1.size()<pf1.size())
			pf1.removeAll(cf1);
		if (cf2.size()<pf2.size())
			pf2.removeAll(cf2);

		// detecting if all features of the products are compulsory
		if (pf1.size()==0 && debug) {
			System.out.println("First product of the pair only have compulsory features");
		}
		if (pf2.size()==0 && debug)
			System.out.println("Second product of the pair only have compulsory features");

		deNum= pf2; 
		num = pf1; 

		if (debug) {
			//Logger.getLogger("Redundancy").log(Level.FINEST,"\n Before set computation pf1 Features : ");
			System.out.println("\n Before set computation pf1 Features : ");
			for (Feature f:num)
				System.out.print(", "  + f.fm_name);
			System.out.println("\n Before set computation pf2 Features : ");
			for (Feature g:deNum)
				System.out.print(", "  + g.fm_name);
		}

		num=intersect(pf1, pf2);
		deNum=union(pf1,pf2);

		if (debug){
			//Logger.getLogger("Redundancy").log(Level.FINEST,"\n Numerator Features : ");
			System.out.println("\n Numerator Features : "); 
			for (Feature f:num)
				System.out.print(", "  + f.fm_name);
			//Logger.getLogger("Redundancy").log(Level.FINEST,", "  + f.fm_name);
			//Logger.getLogger("Redundancy").log(Level.FINEST,"\n Denominator Features : ");
			for (Feature g:deNum)
				System.out.print(", "  + g.fm_name);

			// ratio computation...
		}

		double ratio = (new Double(num.size())) / (new Double(deNum.size()));
		if (debug) 
			System.out.println("\n The ratio for pair: {"+ pair[0].getName() + "," + pair[1].getName() + "} is " + ratio);
		if (ratio == 1.0 && debug) {
			System.out.println("identical products detected");
			System.out.println("\n product1 Features : ");
			for (Feature f:pf1)
				System.out.println(", "  + f.fm_name);
			System.out.println("\n product2 Features : ");
			for (Feature g:pf2)
				System.out.println(", "  + g.fm_name);
		}

		return ratio;

	}
	/**
	 * 
	 * @param p1
	 * @param p2
	 * @return
	 */
	private ArrayList<Feature> intersect(ArrayList<Feature> p1, ArrayList<Feature> p2) {
		ArrayList<Feature> cp1 = p1;
		ArrayList<Feature> cp2=p2;
		ArrayList<Feature> res = new ArrayList<Feature>();

		for (Feature f : cp1) {
			for (Feature g: cp2)
				if (f.fm_name.equals(g.fm_name))
					res.add(f);
		}
		return res;   
	}

	private ArrayList<Feature> union(ArrayList<Feature> p1, ArrayList<Feature> p2) {

		ArrayList<Feature> res= new ArrayList<Feature>(p1);

		ArrayList<Feature> dups = new ArrayList<Feature>(); 
		// compute the union
		res.addAll(p2);


		dups = findDuplicateFeatures(res);

		// debug
		if (debug) {
			System.out.println("\n union p1");
			for (int i =0;i<p1.size();i++){
				System.out.print(" " + p1.get(i).fm_name);
			}
			System.out.println("\n union p2");
			for (int i =0;i<p2.size();i++){
				System.out.print(" " + p2.get(i).fm_name);
			}

			System.out.print("\n union res with dups");
			for (int i =0;i<res.size();i++){
				System.out.print(" " + res.get(i).fm_name);
			}

			System.out.println("\n union dups");
			for (int i =0;i<dups.size();i++){
				System.out.print(" " + dups.get(i).fm_name);
			}

		}

		boolean isRemoved;
		for (int i =0;i<dups.size();i++){
			isRemoved = false;  
			for (int j=0;j<res.size();j++) {
				if ((res.get(j).fm_name.equals(dups.get(i).fm_name)) && !isRemoved) {
					//System.out.print("removed duplicate : " + res.get(j).fm_name);
					res.remove(j);
					isRemoved=true;
				}
			}
		}

		if (debug){ 
			System.out.println("\n res final union");
			for (int i =0;i<res.size();i++){
				System.out.print(" " + res.get(i).fm_name);
			} 
		}
		return res;   

	}

	private ArrayList<Feature> findDuplicateFeatures(ArrayList<Feature> set) {
		ArrayList<Feature> res = new ArrayList<Feature>(); 

		ArrayList<Feature>  tmp = new ArrayList<Feature>(set);

		String[] acc = new String[tmp.size()];
		for (int i =0; i<tmp.size();i++) {
			for (int j=0;j<acc.length;j++) {
				if (acc[j]!= null && acc[j].equals(tmp.get(i).fm_name))
					res.add(tmp.get(i));
			}
			acc[i] = tmp.get(i).fm_name;
		}



		return res;   
	}


	/**
	 * 
	 * @param fm2gj
	 * @param productFeatures
	 * @return
	 */
	private ArrayList<Feature> computeCompulsoryFeatures(FeatureModel2JGraph fm2gj, ArrayList<Feature> productFeatures) {
		ArrayList<Feature> res = new ArrayList<Feature>();

		FeatureDiagram d= fm2gj.getFeatureDiagram();
		mandatoryFeatures = new ArrayList<featureDiagram.Feature>();
		populateMandatory(d.getRoot());

		for (featureDiagram.Feature f : d.getFeatures()) {
			//  System.out.println("Feature " + f.getName() + " optional  " + f.getOptional() + " and required " + isRequired(f,d.getConstraintEdges()));

			if (isMandatory(f) || isRequired(f,d.getConstraintEdges())) {
				Feature g = findAlloyFeatureByName(productFeatures, f.getName());
				if (g != null)
					res.add(g);
				//else
				//System.out.println("feature: " + f.getName() + "not found in alloy representation");
			}	

		}



		return res;
	}

	private void populateMandatory(featureDiagram.Feature f) {
		mandatoryFeatures.add(f);
		if (f.getOperator() instanceof  featureDiagram.And) {
			EList<featureDiagram.Feature> list =  f.getChildren();
			for (featureDiagram.Feature mf : list ) {
				if (!mf.getOptional())
					populateMandatory(mf);
			}
		}

	}

	private boolean isMandatory(featureDiagram.Feature f) {
		boolean bool = false;

		for (featureDiagram.Feature g : mandatoryFeatures) {
			if (g.getName().equals(f.getName()))
				bool = true;
		}

		return bool;
	}

	private boolean isRequired(featureDiagram.Feature f,EList<ConstraintEdge> ce) {
		boolean res = false;

		Iterator<ConstraintEdge> it = ce.iterator();
		while (it.hasNext()) {
			ConstraintEdge c = it.next();

			if (c.getTarget()==f && isMandatory(c.getSource())) {
				return true;
			}
		}

		return res;
	}

	private Feature findAlloyFeatureByName(ArrayList<Feature> features,String name) {
		for (Feature f : features) {
			if (f.fm_name.equals(name))
				return f;
		}
		return null;
	}

	/**
	 * @return the fm2gj
	 */
	 public FeatureModel2JGraph getFm2gj() {
		 return fm2gj;
	 }

	 /**
	  * @return the ts
	  */
	 public TestSuite getTs() {
		 return ts;
	 }

	 public double computeTupleSetRedundancy() {
		 double res = 0.0;

		 int[] tupleOccurrence = new int[tuples.validTupleSet.size()];
		 double[] tupleRatio = new double[tupleOccurrence.length];

		 for (int i=0;i<tuples.validTupleSet.size();i++) {

			 tupleOccurrence[i]=0;

			 for (Product p :ts.getProducts()) {
				 if (productContainsTuple(tuples.validTupleSet.get(i), p)) {
					 tupleOccurrence[i]++;
				//     System.out.println("tuple " + tuples.validTupleSet.get(i).getName() + "found in product " + p.getName() );
				 }
			 }

			 tupleRatio[i]= new Double(tupleOccurrence[i]) / new Double(ts.getProducts().size());
			// System.out.println("tuple ratio: " + tupleOccurrence[i]+ "/" + ts.getProducts().size()+ "=" + tupleRatio[i]);
		 }

		 for (int i=0;i<tupleRatio.length;i++) {
			 res += tupleRatio[i];
		 }

		 res = res / new Double(tupleRatio.length);
		 // store the result for further analysis
		 this.tupleSetRedundancy = res;
		 return res;
	 }

	 private boolean productContainsTuple(Tuple t, Product p ) {

		 int count =0;

		 //showTuple(t);
		 showProduct(p);

		 for (Feature feature: t.tupleFeatures) {
			 for (Feature f: p.getFeatures()) {
				 if (feature.fm_name != null) {
					// System.out.println("tuple feature name: " + feature.fm_name + "exists " +  feature.exists + " product feature name: " + f.fm_name);
					 if (feature.fm_name.equals(f.fm_name) && feature.exists)  {
						 count = count+1;
						 //Logger.getLogger("Redundancy").log(Level.INFO, "feature " + f.fm_name + "found " + feature.fm_name);
					 } else if (!feature.exists) {
						 boolean found = false;
						 for (Feature nf: p.getFeatures()) {
							 if (feature.fm_name.equals(nf.fm_name))
								 found=true;
								 
						 }
						 if (!found) 
							 count = count +1;
					 }
				 }


			 }
		 }

		 if (count == t.tupleFeatures.size()) {
			 //Logger.getLogger("Redundancy").log(Level.INFO, "All tuple features are present in the product");
			 return true;

		 } else {
			 //Logger.getLogger("Redundancy").log(Level.INFO, "There are " + count + " tuple features are present in the product over " + t.tupleFeatures.size()+" total tuple features");
			 return false;
		 }
	 }

	 /**
	  * @param p
	  */
	 private void showProduct(Product p) {

		 System.out.println("\n product");	
		 for (Feature prod : p.getFeatures()) {
			 System.out.print(" " + prod.fm_name);
			 //Logger.getLogger("Redundancy").log(Level.INFO, "feature looked in the product for tuple redundancy " + prod.fm_name);

		 }
		 // TODO Auto-generated method stub

	 }

	 /**
	  * @param t
	  */
	 private void showTuple(Tuple t) {
		 // TODO Auto-generated method stub
		 System.out.println("\n tuple features");
		 for (Feature prod : t.tupleFeatures) {
			 //Logger.getLogger("Redundancy").log(Level.INFO, "tuple feature to be searched " + prod.fm_name + " existing status " + prod.exists);
			 System.out.print(" " + prod.fm_name + "," + prod.exists);
		 }
	 }

	 /**
	  * @return the productRedundancy
	  */
	 public double getProductRedundancy() {
		 return productRedundancy;
	 }

	 /**
	  * @return the tupleSetRedundancy
	  */
	 public double getTupleSetRedundancy() {
		 return tupleSetRedundancy;
	 }

	 /**
	  * @param debug the debug to set
	  */
	 public void setDebug(boolean debug) {
		 this.debug = debug;
	 }
	 
	 
}
