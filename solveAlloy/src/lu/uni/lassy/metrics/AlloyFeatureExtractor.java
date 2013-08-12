/**
 * 
 */
package lu.uni.lassy.metrics;
import java.util.ArrayList;

import fr.irisa.triskell.twise.generation.Feature;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.parser.Module;


/**
 * @author root
 *
 */
public class AlloyFeatureExtractor {

	
	public ArrayList<Feature> extractFeaturesFromALS(String file) {
		 ArrayList<Feature> list = new ArrayList<Feature>();
		 
		 try {
			Module comp = CompUtil.parseEverything_fromFile(null, null, file);
			for (Sig s :comp.getAllSigs()) {
				
				
				if (s.label.equals("this/Configuration")) {
					for (int i=0; i<s.getFields().size();i++) {
						int j=i+1;
						Feature feat =  new Feature(j);
						
						
						String fm_name = s.getFields().get(i).type.toString().replace("this/Configuration->this/", "");
						fm_name=fm_name.replace('}', ' ');
						fm_name=fm_name.replace('{', ' ');
						fm_name=fm_name.trim();
						feat.fm_name=fm_name;
						list.add(feat);
						//System.out.println(fm_name);
					}
					
				}
			}
		} catch (Err e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		 
		//System.out.println(list.toString());
		 return list;
		 
		
		
	}
	
	/**
	 * @param args
	 */
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		AlloyFeatureExtractor afe = new AlloyFeatureExtractor();
		//afe.extractFeaturesFromALS("/home/gperroui/gilles.perrouin/Eclipse-workspaces/yan-dev-wksp/ProductLineTesting/ProductLineTesting/AlloyModels/CrisisManagementSystem.als");
		afe.extractFeaturesFromALS("/home/gperroui/gilles.perrouin/Eclipse-workspaces/yan-dev-wksp/ProductLineTesting/ProductLineTesting/Temp/models/base_aspectOpitma-orig.als");
	}

}
