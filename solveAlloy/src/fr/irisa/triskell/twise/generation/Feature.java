/**
 * 
 */
package fr.irisa.triskell.twise.generation;

/**
 * @author gperroui
 *
 */
public class Feature {


	public String name;
	public Integer number;
	public Boolean exists;
	public String  fm_name;
	public Feature()
	{}

	public Feature(String fm_name) {
		this.fm_name = fm_name;
	}

	public Feature(Integer n)
	{
		this.number=n;
		this.name="f"+ this.number.toString();
		this.exists=true;
	}
	public Feature(Integer n, Boolean existsValue)
	{
		this.number=n;
		this.name="f"+ this.number.toString();
		this.exists=existsValue;

	}

	public Feature(Integer n,String fmFeatureName, Boolean existsValue)
	{
		this.number=n;
		this.name="f"+ this.number.toString();
		this.fm_name = fmFeatureName;
		this.exists=existsValue;

	}

	public String toString()
	{
		if (this.exists==true)

			return "#c."+this.name+"= 1";

		else
			return "#c."+this.name+"= 0";
	}
}


