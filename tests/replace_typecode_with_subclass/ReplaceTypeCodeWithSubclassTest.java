package replace_typecode_with_subclass;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaModelMarker;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.Modifier;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.eclipse.ltk.core.refactoring.Change;
import org.junit.Ignore;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import gr.uom.java.ast.ASTReader;
import gr.uom.java.ast.ClassObject;
import gr.uom.java.ast.CompilationErrorDetectedException;
import gr.uom.java.ast.ConstructorObject;
import gr.uom.java.ast.CreationObject;
import gr.uom.java.ast.FieldObject;
import gr.uom.java.ast.MethodObject;
import gr.uom.java.ast.SystemObject;
import gr.uom.java.ast.TypeObject;
import gr.uom.java.jdeodorant.refactoring.manipulators.ReplaceTypeCodeWithSubclass;
import gr.uom.java.jdeodorant.refactoring.manipulators.TypeCheckElimination;

class ReplaceTypeCodeWithSubclassTest {
	
	private static final String SUBCLASS_TYPE_A = "subclass.TypeA";
	private static final String SUBCLASS_TYPE_B = "subclass.TypeB";
	private static final String TEST_PROJECT_NAME = "SIMPLE_PUSH_DOWN";
	private static final String PACKAGE_NAME = "subclass";
	private static final String TYPE_CHECKING_CLASS_NAME = "Example2";
	
	private static final String testProjectPath = "C:\\Users\\psidiropoulos\\junit-workspace\\SIMPLE_PUSH_DOWN";
	private static final String testDirPath = testProjectPath + "\\src"; 
	private static final String originalVersionsPath = testProjectPath+"\\original-versions";
	
	private static IJavaProject javaProject;
//	private static SystemObject  systemObject;
	private static ClassObject baseClass;
	private static TypeCheckElimination typeCheckElimination;
	private static Map<String, ClassObject> nameToClassObject;
	private static final List<String> subClassesNames = Arrays.asList(SUBCLASS_TYPE_A, SUBCLASS_TYPE_B);
	
	
	@BeforeAll
    static void setUp() throws OperationCanceledException, CompilationErrorDetectedException, CoreException {
		performRefactoring();
//		reParseJavaProject();
		reParseClassesIndependently(PACKAGE_NAME);
		
    }

    private static void performRefactoring() throws CompilationErrorDetectedException, OperationCanceledException, CoreException {
    	IProject project = ResourcesPlugin.getWorkspace().getRoot().getProject(TEST_PROJECT_NAME);
    	javaProject = JavaCore.create(project);
		new ASTReader(javaProject, new NullProgressMonitor());
		SystemObject systemObject = ASTReader.getSystemObject();
		baseClass = systemObject.getClassObject(PACKAGE_NAME+"."+TYPE_CHECKING_CLASS_NAME);
		
		List<TypeCheckElimination> typeCheckEliminations = baseClass.generateTypeCheckEliminations();
		typeCheckElimination = typeCheckEliminations.get(0);
		
		IFile sourceFile = typeCheckElimination.getTypeCheckIFile();
		TypeDeclaration sourceTypeDeclaration = typeCheckElimination.getTypeCheckClass();
		CompilationUnit sourceCompilationUnit = (CompilationUnit) sourceTypeDeclaration.getRoot();
		ReplaceTypeCodeWithSubclass refactoring = new ReplaceTypeCodeWithSubclass(sourceFile, sourceCompilationUnit, sourceTypeDeclaration, typeCheckElimination);
		refactoring.checkFinalConditions(new NullProgressMonitor());
		
		Change change = refactoring.createChange(new NullProgressMonitor());
		change.perform(new NullProgressMonitor());
		
		// re-build the project to reflect the changes of the refactoring
		project.refreshLocal(IResource.DEPTH_INFINITE, null);
		ResourcesPlugin.getWorkspace().build(IncrementalProjectBuilder.FULL_BUILD, null);
		
    }
    
//    private static void reParseJavaProject()  {
//		try {
//			new ASTReader(javaProject, new NullProgressMonitor());
//		} catch (CompilationErrorDetectedException e) {
//			System.out.println(e.getMarkers());
//			Assertions.fail();
//		}
//		systemObject = ASTReader.getSystemObject();
//		baseClass = nameToClassObject.get(PACKAGE_NAME+"."+TYPE_CHECKING_CLASS_NAME);
//    }
    
    public static void reParseClassesIndependently(String packageName) {
    	nameToClassObject = new HashMap<String, ClassObject>();
    	IPackageFragment workingPackageFragmanet = null;
        try {
            for (IPackageFragment packageFragment : javaProject.getPackageFragments()) {
                if (packageFragment.getElementName().equals(packageName) && packageFragment.getKind() == IPackageFragmentRoot.K_SOURCE) {
                	workingPackageFragmanet = packageFragment;
                    for (IJavaElement javaElement : packageFragment.getChildren()) {
                        if (javaElement instanceof ICompilationUnit) {
                            ICompilationUnit unit = (ICompilationUnit) javaElement;
                            ClassObject parsedClass = ASTReader2.parseAST(unit).get(0);
                            nameToClassObject.put(parsedClass.getName(), parsedClass);
                        }
                    }
                }
            }
            baseClass = nameToClassObject.get(PACKAGE_NAME+"."+TYPE_CHECKING_CLASS_NAME);
        } catch (JavaModelException e) {
            e.printStackTrace();
        }
    }
    
    @Test 
    void verifyProjectDoesNotHaveCompilationErrors() {
    	Assertions.assertFalse(hasCompilationErrors(javaProject));
    }
    
    private  static boolean hasCompilationErrors(IJavaProject javaProject) {
        try {
            IMarker[] markers = javaProject.getProject().findMarkers(IJavaModelMarker.JAVA_MODEL_PROBLEM_MARKER, true, IResource.DEPTH_INFINITE);
            for (IMarker marker : markers) {
                int severity = marker.getAttribute(IMarker.SEVERITY, -1);
                if (severity == IMarker.SEVERITY_ERROR) {
                    return true;
                }
            }
        } catch (CoreException e) {
            e.printStackTrace();
        }
        return false;
    }
	
	
	@Test
	void verifySubclassesAreCreated() {
		checkIfSubclassesAreCreated(subClassesNames);
	}
	
	public static void checkIfSubclassesAreCreated(List<String> subClassesNames) {
		for (String subClassName : subClassesNames) {
			Assertions.assertNotNull(nameToClassObject.get(subClassName));
		}
	}
	
	@Test
	void verifySubclassesExtendBaseClass() {
		checkIfSubclassesExtendBaseClass(subClassesNames, "subclass.Example2");
	}
	
	public static void checkIfSubclassesExtendBaseClass(List<String> subClassesNames, String baseClassName) {
		for (String subClassName : subClassesNames) {
			ClassObject sbClasObj = nameToClassObject.get(subClassName);
			TypeObject superClass = sbClasObj.getSuperclass();
			Assertions.assertNotNull(superClass, "Verify subclas extends a superclass");
			Assertions.assertEquals(baseClassName, superClass.getClassType(), "Verify subclass extends the correct superclass");
		}
	}
	
	@Test 
	void verifySubclassesImpementesTypeCheckingMethod() {
		checkIfSubclassHaveTypeCheckingMethod();
	}
	
	public static void checkIfSubclassHaveTypeCheckingMethod() {
		for (String subClassName : subClassesNames) {
			ClassObject cTypeA = nameToClassObject.get(subClassName);
			List<MethodObject> methods = cTypeA.getMethodList();
			MethodObject typeCheckingMethodA = null;
			for (MethodObject mo : methods) {
				if (mo.getName().equals(typeCheckElimination.getTypeCheckMethod().getName().getIdentifier())) {
					typeCheckingMethodA = mo;
					break;
				}
			}
			Assertions.assertNotNull(typeCheckingMethodA, "Verify Subclass implements typechecking method");			
		}
	}
	
	@Test
	void verifySubclassesHaveCorrectPushedDownFields() {		
		checkIfSubclassHavePushedDownField(SUBCLASS_TYPE_A, "a");
		checkIfSubclassHavePushedDownField(SUBCLASS_TYPE_B, "b");
	}
	
	public static void checkIfSubclassHavePushedDownField(String subClassName, String pushedDownFieldName) {
		ClassObject subClass = nameToClassObject.get(subClassName);
		ListIterator<FieldObject> fIter = subClass.getFieldIterator();
		boolean isFieldPushedDown = false;
		boolean isPushedDownFieldPrivate = false;
		while (fIter.hasNext()) {
			FieldObject fo = fIter.next();
			if (fo.getName().equals(pushedDownFieldName)) {
				isFieldPushedDown = true;
				VariableDeclarationFragment vdf = fo.getVariableDeclarationFragment();
				if (vdf.getParent() instanceof FieldDeclaration) {
					FieldDeclaration fieldDeclaration = (FieldDeclaration) vdf.getParent();
					for (Object obj : fieldDeclaration.modifiers()) {
						if (obj instanceof Modifier) {
							Modifier modifier = (Modifier) obj;
							if (modifier.isPrivate()) {
								isPushedDownFieldPrivate = true;
								break;
							}
						}
					}
				}
			}
			Assertions.assertTrue(isFieldPushedDown, "Verify that ["+subClassName+"] contains pushed down field ["+pushedDownFieldName+"]");
			Assertions.assertTrue(isPushedDownFieldPrivate, "Verify that ["+subClassName+"] pushed down field ["+pushedDownFieldName+"] is private");
			
		}
	}
	
	@Ignore
	@Test
	void verifySubclasesHaveNotPushedDownPublicFields(){
		Assertions.fail();
	}
	
	@Test
	void verifySubclassesHaveCorrectPushedDownMethods() {		
		checkIfSubclassHavePushedDownMethods(SUBCLASS_TYPE_A, "methodToBePushedDownForA");
	}
	
	public static void checkIfSubclassHavePushedDownMethods(String subClassName, String pushedDownFieldName) {
		ClassObject subClass = nameToClassObject.get(subClassName);
		MethodObject pushedDownMethod = null;
		for (MethodObject mo : subClass.getMethodList()) {
			if (mo.getName().equals(pushedDownFieldName)) {
				pushedDownMethod = mo;
				break;
			}
		}
		Assertions.assertNotNull(pushedDownMethod, "Verify subclass contains pushed down method");
	}
	
	
	@Test 
	void verifyBaseClassIsConvertedToAbstract() {
		Assertions.assertTrue(baseClass.isAbstract(), "Verify base class is abstract");
	}
	
	@Test 
	void verifyBaseClassTypeCheckingMethodIsAbstract() {
		MethodObject typeCheckingMethod = null;
		for (MethodObject mo : baseClass.getMethodList()) {
			if (mo.getName().equals(typeCheckElimination.getTypeCheckMethod().getName().getIdentifier())) {
				typeCheckingMethod = mo;
				break;
			}
		}
		Assertions.assertTrue(typeCheckingMethod.isAbstract(), "Verify base class typechecking method is converted to abstract");
	}
	
	@Test
	void verifyBaseClassHasDeletedPushedDownFields() {
		Set<String> pushedDownFieldNames = new HashSet<String>(Arrays.asList("a","b"));
		ListIterator<FieldObject> fIter = baseClass.getFieldIterator();
		boolean hasPushedDownFields = false;
		while (fIter.hasNext()) {
			FieldObject fo = fIter.next();
			if (pushedDownFieldNames.contains(fo.getName())) {
				hasPushedDownFields = true;
				break;
			}
		}
		Assertions.assertFalse(hasPushedDownFields, "Verify base class does not have pushed down fields");
	}
	
	@Test
	void verifyBaseClassHasDeletedPushedDownMethods() {
		Set<String> pushedDownMethodNames = new HashSet<String>(Arrays.asList("methodToBePushedDownForA","methodToBePushedDownForB"));
		for (MethodObject mo : baseClass.getMethodList()) {
			if (pushedDownMethodNames.contains(mo.getClassName())) {
				Assertions.fail(String.format("Method '%s' in base class is pushed to subclass.", mo.getName()));
			}
		}
	}
	
	@Test
	void verifyBaseClassHasConvertedToProtectedSharedMethods() {
		List<String> methodNames = Arrays.asList("methodToBePushedDownForB");
		checkIfMethodsAreProtected(methodNames);
	}

	public static void checkIfMethodsAreProtected(List<String> methodNames) {
		for (String methodName : methodNames) {
			MethodObject methodInBaseClass = getMethodOfClassObjectByName(baseClass, methodName);
			Assertions.assertTrue(methodInBaseClass.isProtected(),  String.format("Expected '%s' method in '%s' class to be protected, but it was not.", methodName, baseClass.getName()));
		}
	}
	
	private static MethodObject getMethodOfClassObjectByName(ClassObject classObj, String methodName) {
		List<MethodObject> methods = classObj.getMethodList();
		for (MethodObject mo : methods) {
			if (mo.getName().equals(methodName)) {
				return mo;
			}
		}
		return null;
	}
	
	
	@Test
	void verifyBaseClassHasSharedFields() {
		ListIterator<FieldObject> fIter = baseClass.getFieldIterator();
		Set<String> allFieldNames = new HashSet<String>();
		while (fIter.hasNext()) {
			allFieldNames.add(fIter.next().getName());
		}
		
		Set<String> sharedFieldsNames = new HashSet<String>(Arrays.asList("c"));
		for (String sharedField : sharedFieldsNames) {
			Assertions.assertTrue(allFieldNames.contains(sharedField), "Verify base class contains shared fields");			
		}
	}
	
	@Test
	void verifyBaseClassReplaceConstructorWithFactoryMethod() {
		MethodObject factoryMethod = getMethodOfClassObjectByName(baseClass, "create");
		Assertions.assertNotNull(factoryMethod);
		Assertions.assertTrue(factoryMethod.isPublic());
		Assertions.assertTrue(factoryMethod.isStatic());
		ClassObject originalBaseClass = typeCheckElimination.getClassObject();
		ConstructorObject oldConstructor = originalBaseClass.getConstructorIterator().next();
		
		// assert that the originalConstructor and the factory method have tha same exact paramters
		Assertions.assertEquals(oldConstructor.getParameterList(), factoryMethod.getParameterList());
		Assertions.assertEquals(oldConstructor.getParameterTypeList(), factoryMethod.getParameterTypeList());
		
		List<CreationObject> creationsList = factoryMethod.getMethodBody().getCreations();
		Assertions.assertEquals(typeCheckElimination.getStaticFields().size() + 1, creationsList.size()); 	// #num of subclass creations, 1 exception creation
		
	}
	
	
	
	@AfterAll
	static void tearDown() {
		FileUtils.deleteFilesInDirectory(testDirPath+"\\"+PACKAGE_NAME);
		FileUtils.restoreOriginalFile(originalVersionsPath+"\\"+PACKAGE_NAME+"\\"+TYPE_CHECKING_CLASS_NAME+".java", testDirPath+"\\"+PACKAGE_NAME);
	}
	
}
