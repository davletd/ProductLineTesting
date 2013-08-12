package fr.irisa.triskell.twise.generation;
import java.math.BigInteger;


public class CombinationGenerator {

	  private int[] a;
	  private int n;
	  private int r;
	  private BigInteger numLeft;
	  private BigInteger total;
	  private int total1;
	  private int numLeft1;
	  //------------
	  // Constructor
	  //------------

	  public CombinationGenerator (int n, int r) {
	    if (r > n) {
	      throw new IllegalArgumentException ();
	    }
	    if (n < 1) {
	      throw new IllegalArgumentException ();
	    }
	    this.n = n;
	    this.r = r;
	    a = new int[r];
	    BigInteger nFact = getFactorial (n);
	    BigInteger rFact = getFactorial (r);
	    BigInteger nminusrFact = getFactorial (n - r);
	    total = nFact.divide (rFact.multiply (nminusrFact));
	    total1 = 1;
	    for (int i=1;i<=r;i++)
	    {
	    total1 = total1*(n-r+i)/i;
	    }
	    System.out.println("Total="+total1);
	    reset ();
	  }

	  //------
	  // Reset
	  //------

	  public void reset () {
	    for (int i = 0; i < a.length; i++) {
	      a[i] = i;
	    }
	    numLeft = new BigInteger (total.toString ());
	    numLeft1=total1;
	  }

	  //------------------------------------------------
	  // Return number of combinations not yet generated
	  //------------------------------------------------

	  public BigInteger getNumLeft () {
	    return numLeft;
	  }

	  //-----------------------------
	  // Are there more combinations?
	  //-----------------------------

	  public boolean hasMoreOld () {
	    return numLeft.compareTo (BigInteger.ZERO) == 1;
	    
	  }

	  public boolean hasMore () {
		   if(numLeft1>0)
		   {
		    return true;
		   }
		   else
		   {
			   return false;
		   }
		  }
	  //------------------------------------
	  // Return total number of combinations
	  //------------------------------------

	  public BigInteger getTotal () {
	    return total;
	  }

	  public int getTotal1 () {
		    return total1;
		  }
	  //------------------
	  // Compute factorial
	  //------------------

	  private static BigInteger getFactorial (int n) {
	    BigInteger fact = BigInteger.ONE;
	    for (int i = n; i > 1; i--) {
	      fact = fact.multiply (new BigInteger (Integer.toString (i)));
	    }
	    return fact;
	  }

	  //--------------------------------------------------------
	  // Generate next combination (algorithm from Rosen p. 286)
	  //--------------------------------------------------------

	  public int[] getNext() {

	    if (numLeft1==total1) {
	      numLeft1 = numLeft1-1;
	      return a;
	    }

	    int i = r - 1;
	    while (a[i] == n - r + i) {
	      i--;
	    }
	    a[i] = a[i] + 1;
	    for (int j = i + 1; j < r; j++) {
	      a[j] = a[i] + j - i;
	    }

	    numLeft1 = numLeft1-1;
	    return a;

	  }
	  
	  public int[] getNextOld() {

		    if (numLeft.equals (total)) {
		      numLeft = numLeft.subtract (BigInteger.ONE);
		      return a;
		    }

		    int i = r - 1;
		    while (a[i] == n - r + i) {
		      i--;
		    }
		    a[i] = a[i] + 1;
		    for (int j = i + 1; j < r; j++) {
		      a[j] = a[i] + j - i;
		    }

		    numLeft = numLeft.subtract (BigInteger.ONE);
		    return a;

		  }
	}
