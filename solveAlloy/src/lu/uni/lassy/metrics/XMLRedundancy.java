/**
 * 
 */
package lu.uni.lassy.metrics;

import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.alloy4.XMLNode;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.A4SolutionReader;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Tuple;
import edu.mit.csail.sdg.alloy4compiler.translator.A4TupleSet;
import fr.irisa.triskell.twise.generation.Feature;
import fr.irisa.triskell.twise.generation.Product;
import fr.irisa.triskell.twise.generation.TestSuite;

/**
 * @author root
 *
 */
public class XMLRedundancy {

	/**
	 * 
	 * @param path
	 */
	public TestSuite getXMLTestSuite(String XMLFile, String suiteName) {

		TestSuite ts = new TestSuite(suiteName);

		SafeList<Sig> sigs = null;


		XMLNode node;

		//node.
		A4SolutionReader a4; // = new A4SolutionReader(null, null);


		try {
			//static A4Solution sol;
			node = new XMLNode(new File(XMLFile));
			A4Solution sol = A4SolutionReader.read(sigs, node);


			sigs = sol.getAllReachableSigs();
			if (sigs.size()==0)
				System.out.println("no sig in solution");

			for (Sig s: sigs) {
				
				if (s.label.equals("Configuration")) {

					//System.out.println("found signature " + s.label);
					A4TupleSet tset = (A4TupleSet) sol.eval(s);
					SafeList<Field> fs= s.getFields();
					Iterator<A4Tuple> it = tset.iterator();

					if (tset.size()==0)
						System.out.println("it seems that tuple set have not been solved...");

					while (it.hasNext()) {
						String name = it.next().atom(0);
						System.out.println("atom: "+ name);

						Product p = new Product(name);
						ArrayList<A4TupleSet> fieldTuples = new ArrayList<A4TupleSet>();
						for (Field f: fs) {
							fieldTuples.add((A4TupleSet)sol.eval(f));
						}
						p.setFeatures(getFeatureFromFields(name,fieldTuples));
						//prods.put(name, p);
						ts.addProduct(p);


					}
				}
			}
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return ts;
	}

	private static ArrayList<Feature> getFeatureFromFields(String productName, ArrayList<A4TupleSet> fieldTuples) {
		ArrayList<Feature> features = new ArrayList<Feature>();

		for (A4TupleSet tuple : fieldTuples) {
			Iterator<A4Tuple> it = tuple.iterator();
			while (it.hasNext()) {
				A4Tuple a4Tuple = it.next();
				String name = a4Tuple.atom(0);

				if (name.equals(productName)) {
					String fname = a4Tuple.atom(1).split("\\$\\d*")[0];
					//	System.out.println("adding " + fname + " to product " + productName);
					features.add(new Feature(fname));
				}
			}
		}

		return features;
	}



	private static TestSuite mergeTestSuites(ArrayList<TestSuite> lts,String name) {
		TestSuite ts = new TestSuite(name);

		for (int i=0;i<lts.size();i++) {
			ArrayList<Product> prods = lts.get(i).getProducts();

			for (Product p: prods) {
				p.setName(p.getName()+"_" + i);
			}

			ts.addAllProducts(prods);


		}

		return ts;

	}


	/**
	 * @param args
	 */
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		XMLRedundancy r= new XMLRedundancy();
		String gilles_root = new String("/home/gperroui/gilles.perrouin/Eclipse-workspaces/yan-dev-wksp/ProductLineTesting/ProductLineTesting");
		String root = gilles_root;
		ArrayList<TestSuite> suites = new ArrayList<TestSuite>();
		String solutionPath = new String("/Temp/solutions/");
		MetricsStore store = new MetricsStore();
		store.initCSV(root+solutionPath);

		File dir = new File(root+"/Temp/solutions");
		if (dir.isDirectory()) {
			// FileNameFilter
			String[] dirlist = dir.list(null);

			for (String solDir: dirlist) {
				System.out.println("Solution directory: " + solDir);
				if (solDir.contains("Solution")) {
					//System.out.println("parsing solution " + solDir);
					File indivdir = new File(root+"/Temp/solutions/"+solDir);

					if (indivdir.isDirectory() && !indivdir.getName().contains(".svn")) {
						System.out.println("parsing solution " + solDir);
						String[] xmlfiles;
						//try {
						xmlfiles = indivdir.list(null);

						ArrayList<TestSuite> tests = new ArrayList<TestSuite>();
						for (int i=0;i<xmlfiles.length;i++) {
							if (xmlfiles[i].contains(".xml")) {
								String indivtname =  xmlfiles[i].split(".xml")[0];
								TestSuite t = r.getXMLTestSuite(root+"/Temp/solutions/"+solDir+"/"+xmlfiles[i], indivtname); 
								System.out.println(t.toString());
								tests.add(t);
							}
						}

						TestSuite suite = r.mergeTestSuites(tests, solDir);
						FeatureModel2JGraph fm2gj = new FeatureModel2JGraph(root+"/feature-models/transactionFeatureDiagram.xmi"); 
						Redundancy red = new Redundancy(fm2gj,suite);

						red.computeRedundancy();
						store.addRedundancy(red);
						store.addSolutionSuite(suite);
						store.writeCSVincremental();
						//suites.add(suite);

						//}
						//} catch (IOException e) {
						// TODO Auto-generated catch block
						//	e.printStackTrace();
						//}
					}
				}


			}


		}

		//MetricsStore store = new MetricsStore();
		//store.

	}

}
