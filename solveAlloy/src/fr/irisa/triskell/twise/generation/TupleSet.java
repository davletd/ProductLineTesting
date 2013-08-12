/**
 * 
 */
package fr.irisa.triskell.twise.generation;

import java.io.IOException;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Random;

import edu.mit.csail.sdg.alloy4.Err;

/**
 * @author gperroui
 *
 */
public class TupleSet
{
	public ArrayList<Tuple> allTupleSet;
	public ArrayList<Tuple> validTupleSet;

	public String name;
	public String baseAlloyModel;

	public TupleSet()
	{
		this.name="TestTupleSet";

	}

	public TupleSet(String itsName)
	{
		this.name=itsName;
	}

	public void setName(String itsName)
	{
		this.name = itsName;
	}

	public static long factorial(Integer n)
	{
		if (n<=1)
			return 1;
		else
			return n*factorial(n-1);
	}
	
	public static BigInteger bigFactorial(BigInteger n)
	{
		if (n.compareTo(BigInteger.ONE)==-1 || n.compareTo(BigInteger.ONE)==0)
			return BigInteger.ONE;
		else
			return n.multiply(bigFactorial(n.subtract(BigInteger.ONE)));
	}

	public static double combination(Integer n, Integer r)
	{
		if (r<=n) {
			System.out.println("r: " + r + " n: " + n);
			byte[] bn = new byte[1];
			byte[] br = new byte[1];
			bn[0]= n.byteValue();
			br[0]= r.byteValue();
			BigInteger bd = bigFactorial(new BigInteger(bn)).divide((bigFactorial(new BigInteger(br)).multiply(bigFactorial(new BigInteger(bn).subtract(new BigInteger(br))))));
			
			System.out.println("factorial r " + (bigFactorial(new BigInteger(br))).doubleValue());
			System.out.println("factorial n " + (bigFactorial(new BigInteger(bn))).doubleValue());
			System.out.println("factorial n-r " + bigFactorial(new BigInteger(bn).subtract(new BigInteger(br))).doubleValue());
			System.out.println("fact(n)/fact(r)*fact(n-r) or binomial coefficient: " + bd.doubleValue());
			
			return bd.doubleValue();
		
		} else
			System.out.println ("The value of r =" + r.toString()+" is greater than n =" + n.toString());
		return -1;
	}

	//Create set of all tuples of size T for the features in the pro
	public void createCreateAllTuples(ArrayList<Feature> productLineFeatures, Integer T_wise) throws Err
	{

		//Number of features
		Integer numberOfFeatures = new Integer(0);
		numberOfFeatures=productLineFeatures.size();


		//Number of combinations for numberOfFeatures_C_T_wise = numberOffeatures!/T_wise! (numberOfFeatures - T_wise)!

		double numberOfCombinations = 0;
		numberOfCombinations = combination(numberOfFeatures,T_wise);

		//Number of pairs numberOfCombinations * 2^T_wise
		double numberOfPairs = 0;
		numberOfPairs = numberOfCombinations * (long)Math.pow(2,T_wise);


		//Create an initial allTuple set
		allTupleSet = new ArrayList<Tuple>();


		//Create combinations for pairs

		ArrayList<Feature> featureSelections = new ArrayList<Feature>();
		for(int i=0;i<productLineFeatures.size();i++)
		{

			Feature temp1 = new Feature(productLineFeatures.get(i).number,productLineFeatures.get(i).fm_name,true);
			Feature temp2 = new Feature(productLineFeatures.get(i).number,productLineFeatures.get(i).fm_name,false);

			featureSelections.add(temp1);
			featureSelections.add(temp2);
		}


		CombinationGenerator twise = new CombinationGenerator(featureSelections.size(),T_wise);
		ArrayList<Tuple> tempTupleSet = new ArrayList<Tuple>();

		Integer tupleNumber=new Integer(1);
		int[] indices;

		while (twise.hasMore())
		{
			Tuple tempTuple = new Tuple(tupleNumber,T_wise);
			indices=twise.getNext();
			ArrayList<Feature> tempListOfFeatures = new ArrayList<Feature>();
			for(int i=0;i<indices.length;i++)
			{
				tempListOfFeatures.add(featureSelections.get(indices[i]));	
			}


			tempTuple.setTuple(tempListOfFeatures);
			//Add only if there are no duplicates
			if(!tempTuple.hasDups())
			{
				tempTupleSet.add(tempTuple);
				tupleNumber = tupleNumber+1;
			}
		}

		Integer nC=tempTupleSet.size();
		//System.out.println("Total number of combinations="+nC);
		this.allTupleSet.clear();

		this.allTupleSet.addAll(tempTupleSet);



	}

	public void getVaildTuples(String baseAlloyPath,String baseAlloyFileName, String tempFileName, Integer min_Scope, Integer max_Scope, Integer max_Duration) throws Err, IOException
	{
		this.validTupleSet = new ArrayList<Tuple>();
		this.validTupleSet.clear();
		for(int i=0;i<this.allTupleSet.size();i++)
		{
			Tuple t = this.allTupleSet.get(i);
			Boolean valid = t.getValidity(baseAlloyPath, baseAlloyFileName,  tempFileName, min_Scope, max_Scope, max_Duration);
			if(valid)
			{
				//System.out.println("Tuple "+t.getName()+" is valid!");
				this.validTupleSet.add(t);
			}
			this.baseAlloyModel = t.getAlloyBaseModel(baseAlloyPath+baseAlloyFileName);

		}
		System.out.println("\nNumber of valid tuples = " +this.validTupleSet.size());
		for(int i=0;i<this.validTupleSet.size();i++)
		{
			this.baseAlloyModel=this.baseAlloyModel +this.validTupleSet.get(i).toPredicate()+"\n";
		}
	}
	public String toString()
	{
		String tupleSet ="";
		for(int i=0;i<this.allTupleSet.size();i++)
		{
			tupleSet = tupleSet + this.allTupleSet.get(i).toString()+"\n";
		}
		return tupleSet;

	}

	public void save(String path) throws IOException
	{
		String experimentLog = this.toString();
		java.io.PrintWriter out = new java.io.PrintWriter(new java.io.FileWriter(path));
		out.print(experimentLog);
		out.close();

	}

	public String toPredicate(ArrayList<Tuple> tupleSet) 
	{
		String predicate = new String();
		predicate = "pred "+this.name+" { ";

		for(int i=0;i<tupleSet.size();i++)
		{
			predicate = predicate + tupleSet.get(i).getName() + " and ";
		}
		predicate = predicate.substring(0,predicate.length()-4);
		predicate= predicate + " } ";
		return predicate;
	}

	//Distance between two tuples
	public Integer distanceAbout(Tuple x, Tuple y)
	{
		Integer distance=0;
		for(int i=0;i<x.tupleFeatures.size();i++)
		{
			if(y.tupleFeatures.get(i).name==x.tupleFeatures.get(i).name)
			{
				distance = distance+1;
			}
		}
		return distance;
	}

	//Tuple at farthest distance from current set of tuples
	public int distanceFromCurrentSet(ArrayList<Tuple> currentSet, ArrayList<Tuple> remainingSet)
	{

		Tuple farthest=new Tuple();
		int distance=0;
		int maxDistance=0;
		int index=0;
		for(int i=0;i<remainingSet.size();i++)
		{
			distance=0;
			for(int j=0;j<currentSet.size();j++)
			{
				distance=distance + this.distanceAbout(currentSet.get(j),remainingSet.get(i));
			}
			if(distance>maxDistance)
			{
				maxDistance=distance;
				farthest=remainingSet.get(i);
				index=i;
			}
		}
		return index;
	}

	public int selectNextTuple(ArrayList<Tuple> currentSet, ArrayList<Tuple> remainingSet,  SelectStrategy s)
	{	Tuple t =new Tuple();
	int index=0;

	if (s==SelectStrategy.RANDOM)
	{

		Random generator = new Random();

		index = generator.nextInt(remainingSet.size());
		//System.out.println("Chosen location="+rnd);
		//  System.out.println("Size="+remainingSet.size());
		//t=remainingSet.get(rnd);


	}

	if (s==SelectStrategy.DISTANCE)
	{
		index=this.distanceFromCurrentSet(currentSet, remainingSet);
	}
	return index;
	}

}
