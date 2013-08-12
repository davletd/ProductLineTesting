package lu.uni.lassy.metrics;

import java.io.IOException;
import java.util.Collections;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EPackage.Registry;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.emf.ecore.xmi.impl.XMIResourceFactoryImpl;

import featureDiagram.FeatureDiagramPackage;

public class EMFHelper {



	public static EObject loadFeatureModel(String path) throws IOException {

		Registry.INSTANCE.put(
				FeatureDiagramPackage.eNS_URI,
				FeatureDiagramPackage.eINSTANCE
		);


		URI fileURI = URI.createFileURI(path);
		ResourceSet resourceSet = new ResourceSetImpl();
		resourceSet.getResourceFactoryRegistry().getExtensionToFactoryMap().put(
				"xmi", new XMIResourceFactoryImpl());
		Resource resource = resourceSet.getResource(fileURI,true);
		resource.getContents().get(0);
		return resource.getContents().get(0);	

	}

	public static void saveFeatureModel(EObject object,String path) throws IOException{
		URI fileURI = URI.createFileURI(path);
		System.out.println("saving to: "+fileURI);
		ResourceSet resourceSet=new ResourceSetImpl();
		resourceSet.getResourceFactoryRegistry().getExtensionToFactoryMap().put(
				"xmi", new XMIResourceFactoryImpl());
		Resource resource = resourceSet.createResource(fileURI);
		resource.getContents().add(object);
		resource.save(Collections.EMPTY_MAP);
	}
}
