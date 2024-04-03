package gr.uom.java.jdeodorant.refactoring.manipulators;

import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import javax.swing.tree.DefaultMutableTreeNode;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.AbstractTypeDeclaration;
import org.eclipse.jdt.core.dom.Assignment;
import org.eclipse.jdt.core.dom.Block;
import org.eclipse.jdt.core.dom.ClassInstanceCreation;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.ExpressionStatement;
import org.eclipse.jdt.core.dom.FieldAccess;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.IfStatement;
import org.eclipse.jdt.core.dom.InfixExpression;
import org.eclipse.jdt.core.dom.Javadoc;
import org.eclipse.jdt.core.dom.MemberRef;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.Modifier;
import org.eclipse.jdt.core.dom.Modifier.ModifierKeyword;
import org.eclipse.jdt.core.dom.PrimitiveType;
import org.eclipse.jdt.core.dom.ReturnStatement;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.Statement;
import org.eclipse.jdt.core.dom.StringLiteral;
import org.eclipse.jdt.core.dom.SuperConstructorInvocation;
import org.eclipse.jdt.core.dom.SwitchCase;
import org.eclipse.jdt.core.dom.SwitchStatement;
import org.eclipse.jdt.core.dom.TagElement;
import org.eclipse.jdt.core.dom.ThrowStatement;
import org.eclipse.jdt.core.dom.Type;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationExpression;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.eclipse.jdt.core.dom.VariableDeclarationStatement;
import org.eclipse.jdt.core.dom.rewrite.ASTRewrite;
import org.eclipse.jdt.core.dom.rewrite.ImportRewrite;
import org.eclipse.jdt.core.dom.rewrite.ListRewrite;
import org.eclipse.jdt.core.refactoring.CompilationUnitChange;
import org.eclipse.jdt.internal.corext.refactoring.changes.CreateCompilationUnitChange;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.ChangeDescriptor;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.eclipse.ltk.core.refactoring.RefactoringChangeDescriptor;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.text.edits.MalformedTreeException;
import org.eclipse.text.edits.MultiTextEdit;
import org.eclipse.text.edits.TextEdit;
import org.eclipse.text.edits.TextEditGroup;

import gr.uom.java.ast.ASTReader;
import gr.uom.java.ast.ClassObject;
import gr.uom.java.ast.MethodInvocationObject;
import gr.uom.java.ast.MethodObject;
import gr.uom.java.ast.decomposition.cfg.PlainVariable;
import gr.uom.java.ast.inheritance.InheritanceTree;
import gr.uom.java.ast.util.ExpressionExtractor;
import gr.uom.java.ast.util.MethodDeclarationUtility;
import gr.uom.java.ast.util.TypeVisitor;

public class ReplaceTypeCodeWithSubclass extends PolymorphismRefactoring {
	private VariableDeclaration returnedVariable;
	private Set<ITypeBinding> requiredImportDeclarationsBasedOnSignature;
	private Set<ITypeBinding> requiredImportDeclarationsForContext;
	private Set<ITypeBinding> thrownExceptions;
	private Map<String, SimpleName> subclassNameToStaticFieldMap;
	private Map<SimpleName, String> staticFieldMap;
	private Map<SimpleName, String> additionalStaticFieldMap;
	private String baseClassName;
	private Map<ICompilationUnit, CreateCompilationUnitChange> createCompilationUnitChanges;
	private TypeDeclaration baseClassTypeDecleration;
	private TypeCheckElimination typeCheckElimination;
	private Map<String, Subclass> nameToSubclassMap;
	private Set<VariableDeclarationFragment> baseClassSharedFields;
	private Map<MethodDeclaration, Set<VariableDeclarationFragment>> methodToFieldsUsed;
	private Set<MethodDeclaration> methodsUsedInSubclasses;
	private Set<VariableDeclarationFragment> fieldsUsedByPublicMethods;
	
	
	public ReplaceTypeCodeWithSubclass(IFile sourceFile, CompilationUnit sourceCompilationUnit,
			TypeDeclaration sourceTypeDeclaration, TypeCheckElimination typeCheckElimination) {
		super(sourceFile, sourceCompilationUnit, sourceTypeDeclaration, typeCheckElimination);
		this.returnedVariable = typeCheckElimination.getTypeCheckMethodReturnedVariable();
		this.requiredImportDeclarationsBasedOnSignature = new LinkedHashSet<ITypeBinding>();
		this.requiredImportDeclarationsForContext = new LinkedHashSet<ITypeBinding>();
		this.thrownExceptions = typeCheckElimination.getThrownExceptions();			
		this.subclassNameToStaticFieldMap = new LinkedHashMap<String, SimpleName>();
		this.staticFieldMap = new LinkedHashMap<SimpleName, String>();
		for(SimpleName simpleName : typeCheckElimination.getStaticFields()) {
			String subclassName = generateSubclassName(simpleName);
			this.staticFieldMap.put(simpleName, generateSubclassName(simpleName));
			this.subclassNameToStaticFieldMap.put(subclassName, simpleName);
		}
		this.additionalStaticFieldMap = new LinkedHashMap<SimpleName, String>();
		for(SimpleName simpleName : typeCheckElimination.getAdditionalStaticFields()) {
			this.additionalStaticFieldMap.put(simpleName, generateSubclassName(simpleName));
		}
		this.baseClassName = typeCheckElimination.getTypeCheckClass().getName().getIdentifier();
		this.createCompilationUnitChanges = new LinkedHashMap<ICompilationUnit, CreateCompilationUnitChange>();
		this.baseClassTypeDecleration = typeCheckElimination.getTypeCheckClass();
		this.typeCheckElimination = typeCheckElimination;
		this.baseClassSharedFields = new LinkedHashSet<VariableDeclarationFragment>(); 
		this.methodToFieldsUsed = new HashMap<MethodDeclaration, Set<VariableDeclarationFragment>>();
		
		this.methodsUsedInSubclasses = new HashSet<MethodDeclaration>();
		this.nameToSubclassMap = new HashMap<String, Subclass>();
		for(SimpleName simpleName : typeCheckElimination.getStaticFields()) {
			String subclassName = generateSubclassName(simpleName);
			this.nameToSubclassMap.put(subclassName, new Subclass(subclassName, typeCheckElimination.getTypeCheckClass(), typeCheckElimination, simpleName));
		}
		this.fieldsUsedByPublicMethods = new LinkedHashSet<VariableDeclarationFragment>();
		setBaseClassSharedFields();
		setFieldsUsedInBaseClassMethods();
		setSubclassesExclusiveFields();
		setCandidateMethodsToPushDown();
		
		
	}
	
	private class Subclass {
		private String name; 
		private TypeDeclaration baseClassTypeDecleration;
		private SimpleName staticField;
		private Set<VariableDeclarationFragment> exclusiveFields;
		private Set<VariableDeclarationFragment> allReferencedFields; // sharedFields + private fileds used in only in this methods typecheking classes
		private TypeCheckElimination typeCheckElimination;
		private Set<MethodDeclaration> candidateMethodsToPushDown;
		
		
		public Subclass(String name, TypeDeclaration baseClassTypeDecleration, TypeCheckElimination typeCheckElimination, SimpleName staticField) {
			this.name = name;
			this.baseClassTypeDecleration = baseClassTypeDecleration;
			this.typeCheckElimination = typeCheckElimination;
			this.staticField = staticField;
			this.candidateMethodsToPushDown = new LinkedHashSet<MethodDeclaration>();
			this.allReferencedFields = findAllUsedFields();
			
		}
				
		public Set<VariableDeclarationFragment> getAllReferencedFields() {
			return allReferencedFields;
		}
		
		public Set<VariableDeclarationFragment> getExclusiveFields() {
			return exclusiveFields; 
		}
		
		private void setExclusiveFields(Set<VariableDeclarationFragment> exclusiveFields) {
			this.exclusiveFields = exclusiveFields;
		}
		
		public Set<MethodDeclaration> getMethodsToPushDown() {
			Set<MethodDeclaration> methods = new LinkedHashSet<MethodDeclaration>();
			for (MethodDeclaration md : candidateMethodsToPushDown) {
				Set<VariableDeclarationFragment> fieldsUsedByMethod = methodToFieldsUsed.get(md);
				if (!areFieldsUsedByPublicMethods(fieldsUsedByMethod)) {
					methods.add(md);
				}
				// TODO: add those method to become protected !!!!!!!!
				
			}
			
			return methods;
		}
		
		private boolean areFieldsUsedByPublicMethods(Set<VariableDeclarationFragment> fieldsUsedByMethod) {
			for (VariableDeclarationFragment field : fieldsUsedByMethod) {
				if (fieldsUsedByPublicMethods.contains(field) ) {
					return true;
				}
			}
			return false;
		}

		private Set<VariableDeclarationFragment> findAllUsedFields() {
			ClassObject classObject = typeCheckElimination.getClassObject();
			Set<String> methodsToCheck = new LinkedHashSet<String> ();
			for (MethodDeclaration md : typeCheckElimination.getMethodsUsedInsideStaticFieldBranch(staticField)) {
				methodsToCheck.add(md.getName().getIdentifier());
			}
			Queue<String> methodQueue = new LinkedList<String>(methodsToCheck); 
			
			Map<String, MethodObject> methodNameToObjectMap = new HashMap<String, MethodObject>();
			for (MethodObject methodObject : classObject.getMethodList()) {
				methodNameToObjectMap.put(methodObject.getName(), methodObject);
			}
			
			Set<String> fieldNames = new HashSet<String>();
			while (!methodQueue.isEmpty()) {
			    String methodName = methodQueue.poll();
				MethodObject mo = methodNameToObjectMap.get(methodName);
				for (PlainVariable pv : mo.getUsedFieldsThroughThisReference()) {
					fieldNames.add(pv.getVariableName());
				}
				for (MethodInvocationObject invokedMethodObject:  mo.getInvokedMethodsThroughThisReference()) {
					methodQueue.add(invokedMethodObject.getMethodName());
				}
				
			}
			Set<VariableDeclarationFragment> fields = new LinkedHashSet<VariableDeclarationFragment>();
			fields.addAll(typeCheckElimination.getFieldsUsedInTypeCheckingBranches(staticField));
			fields.addAll(getVariableDeclarationFragmentsFromFieldNames(fieldNames, baseClassTypeDecleration));
			System.out.println(name +".allUsedFields : "+ fields);
			return fields;
		}
		
		private Set<VariableDeclarationFragment> getVariableDeclarationFragmentsFromFieldNames(Set<String> fieldNames, TypeDeclaration baseClassTypeDeclaration) {
			Set<VariableDeclarationFragment> fragments = new LinkedHashSet<VariableDeclarationFragment>();

	        for (FieldDeclaration field : baseClassTypeDeclaration.getFields()) {
	            for (Object fragmentObject : field.fragments()) {
	                if (fragmentObject instanceof VariableDeclarationFragment) {
	                    VariableDeclarationFragment fragment = (VariableDeclarationFragment) fragmentObject;
	                    
	                    if (fieldNames.contains(fragment.getName().getIdentifier()) && Modifier.isPrivate(field.getModifiers())) {
	                        fragments.add(fragment);
	                    }
	                }
	            }
	        }

	        return fragments;
	    }
				
		private void addMethodToPushDown(MethodDeclaration md) {
			candidateMethodsToPushDown.add(md);
		}
		
		private void getMethodsEligibleForPushDown() {
			
		}
		
		private void createSubclassConstructor(Subclass sb, AST ast, ASTRewrite rewriter, ListRewrite subclassBodyRewrite, CompilationUnit subclassCompilationUnit) {
			String constructorName = sb.name;
		    
		    MethodDeclaration subclassConstructor = ast.newMethodDeclaration();
		    rewriter.set(subclassConstructor, MethodDeclaration.CONSTRUCTOR_PROPERTY, true, null);
		    rewriter.set(subclassConstructor, MethodDeclaration.NAME_PROPERTY, ast.newSimpleName(constructorName), null);
		    ListRewrite modifiersRewrite = rewriter.getListRewrite(subclassConstructor, MethodDeclaration.MODIFIERS2_PROPERTY);
		    modifiersRewrite.insertLast(ast.newModifier(ModifierKeyword.PUBLIC_KEYWORD), null);

		    ListRewrite parametersRewrite = rewriter.getListRewrite(subclassConstructor, MethodDeclaration.PARAMETERS_PROPERTY);
		    List<SingleVariableDeclaration> sbConstructorParams = new ArrayList<SingleVariableDeclaration>();
		    for (VariableDeclarationFragment fragment : allReferencedFields) {
		        Type fieldType = ((FieldDeclaration) fragment.getParent()).getType();
		        
		        SingleVariableDeclaration parameter = ast.newSingleVariableDeclaration();
		        parameter.setType((Type) ASTNode.copySubtree(ast, fieldType)); 
		        parameter.setName(ast.newSimpleName(fragment.getName().getIdentifier()));

		        parametersRewrite.insertLast(parameter, null);
		        sbConstructorParams.add(parameter);
		    }
		    

		    Block constructorBody = ast.newBlock();

		    SuperConstructorInvocation superConstructorInvocation = ast.newSuperConstructorInvocation();
		    ListRewrite argumentRewrite = rewriter.getListRewrite(superConstructorInvocation, SuperConstructorInvocation.ARGUMENTS_PROPERTY);
			for (VariableDeclarationFragment baseClassField : baseClassSharedFields) {
				SimpleName argumentName = ast.newSimpleName(baseClassField.getName().getIdentifier());
				argumentRewrite.insertLast(argumentName, null);
			}

		    ListRewrite statementsRewrite = rewriter.getListRewrite(constructorBody, Block.STATEMENTS_PROPERTY);
		    statementsRewrite.insertFirst(superConstructorInvocation, null);

		    rewriter.set(subclassConstructor, MethodDeclaration.BODY_PROPERTY, constructorBody, null);

		    subclassBodyRewrite.insertLast(subclassConstructor, null);
		    
		    Set<ITypeBinding> requiredImportDeclarationsBasedOnBranch = getRequiredImportDeclarationsParameters(sbConstructorParams);
			for(ITypeBinding typeBinding : requiredImportDeclarationsBasedOnBranch) {
				if(!requiredImportDeclarationsBasedOnSignature.contains(typeBinding))
					addImportDeclaration(typeBinding, subclassCompilationUnit, rewriter);
			}
		}
		
	}

	@Override
	public String getName() {
		return "Replace Type Code with Subclass";
	}

	@Override
	public RefactoringStatus checkInitialConditions(IProgressMonitor pm)
			throws CoreException, OperationCanceledException {
		RefactoringStatus status= new RefactoringStatus();
		try {
			pm.beginTask("Checking preconditions...", 1);
			// ....
		} finally {
			pm.done();
		}
		return status;
	}

	@Override
	public RefactoringStatus checkFinalConditions(IProgressMonitor pm)
			throws CoreException, OperationCanceledException {
		final RefactoringStatus status= new RefactoringStatus();
		try {
			pm.beginTask("Checking preconditions...", 2);
//			searchEmployeeConstructorInvocations();
			createSubclasses();
			modifyBaseClass();
		} finally {
			pm.done();
		}
		return status;
	}
	
	
	
	private void modifyBaseClass() {
		ASTRewrite sourceRewriter = ASTRewrite.create(sourceTypeDeclaration.getAST());
		AST baseClassAST = sourceTypeDeclaration.getAST();
		makeBaseClassAbstract(baseClassAST, sourceRewriter);
		changeFieldModifiersToProtected(baseClassAST, sourceRewriter);
		changeMethodModifiersToProtected(baseClassAST, sourceRewriter);
		removeMethodsThatWillBePushedDown(sourceRewriter);
		removeFieldsThatWillBePushedDown(sourceRewriter);
		createFactoryMethod(baseClassAST, sourceRewriter);
		modifyBaseClassConstructorToSetOnlySharedFields(baseClassAST, sourceRewriter);
		
		try {
			TextEdit sourceEdit = sourceRewriter.rewriteAST();
			ICompilationUnit sourceICompilationUnit = (ICompilationUnit)sourceCompilationUnit.getJavaElement();
			CompilationUnitChange change = compilationUnitChanges.get(sourceICompilationUnit);
			change.getEdit().addChild(sourceEdit);
			change.addTextEditGroup(new TextEditGroup("Making the context class abstract and used fields form subclasses protected", new TextEdit[] {sourceEdit}));
		} catch (JavaModelException e) {
			e.printStackTrace();
		}
		
	}

	private void makeBaseClassAbstract(AST contextAST, ASTRewrite sourceRewriter) {
		TypeDeclaration typeDecl = this.baseClassTypeDecleration;
		MethodDeclaration methodDec = typeCheckElimination.getTypeCheckMethod();
		
		ListRewrite modifiersRewrite = sourceRewriter.getListRewrite(typeDecl, TypeDeclaration.MODIFIERS2_PROPERTY);
		modifiersRewrite.insertLast(contextAST.newModifier(Modifier.ModifierKeyword.ABSTRACT_KEYWORD), null);

		ListRewrite methodModifiersRewrite = sourceRewriter.getListRewrite(methodDec, MethodDeclaration.MODIFIERS2_PROPERTY);
		methodModifiersRewrite.insertLast(contextAST.newModifier(Modifier.ModifierKeyword.ABSTRACT_KEYWORD), null);

		sourceRewriter.set(methodDec, MethodDeclaration.BODY_PROPERTY, null, null);
		
	}
	
	// Replacing the modifiers of fields that are used in subclasses from private to protected
	private void changeFieldModifiersToProtected(AST contextAST, ASTRewrite sourceRewriter) {
		TypeDeclaration typeDecl = this.baseClassTypeDecleration;
		Set<VariableDeclarationFragment> fieldsToChange = baseClassSharedFields;

		for (FieldDeclaration fieldDecl : typeDecl.getFields()) {
	        for (Object obj : fieldDecl.fragments()) {
	            VariableDeclarationFragment fragment = (VariableDeclarationFragment) obj;
	            if (fieldsToChange.contains(fragment)) {
//	                ListRewrite modifiersListRewrite = sourceRewriter.getListRewrite(fieldDecl, FieldDeclaration.MODIFIERS2_PROPERTY);
	                
	                Modifier privateModifier = null;
	                for (Object mod : fieldDecl.modifiers()) {
	                    if (mod instanceof Modifier && ((Modifier) mod).isPrivate()) {
	                        privateModifier = (Modifier) mod;
	                        break;
	                    }
	                }
	                
	                if (privateModifier != null) {
	                	sourceRewriter.set(privateModifier, Modifier.KEYWORD_PROPERTY,  Modifier.ModifierKeyword.PROTECTED_KEYWORD, null);
	                }
	            }
	        }
	    }
	    
	}
	
	// Replacing the modifiers of methods that are used in subclasses from private to protected
	private void changeMethodModifiersToProtected(AST contextAST, ASTRewrite sourceRewriter) {
	    TypeDeclaration typeDecl = this.baseClassTypeDecleration;
	    Set<MethodDeclaration> methodsToChange = methodsUsedInSubclasses;
	    
	    for (MethodDeclaration methodDecl : typeDecl.getMethods()) {
	        if (methodsToChange.contains(methodDecl)) {
	            List modifiers = methodDecl.modifiers();
	            Modifier privateModifier = null;
	            for (Object mod : modifiers) {
	                if (mod instanceof Modifier && ((Modifier) mod).isPrivate()) {
	                    privateModifier = (Modifier) mod;
	                    break;
	                }
	            }

	            if (privateModifier != null) {
	                sourceRewriter.set(privateModifier, Modifier.KEYWORD_PROPERTY,  Modifier.ModifierKeyword.PROTECTED_KEYWORD, null);
	            }
	        }
	    }
	}
	
	private void removeMethodsThatWillBePushedDown(ASTRewrite sourceRewriter) {
		Set<MethodDeclaration> methodDecls = new LinkedHashSet<MethodDeclaration>();
		for (Subclass sb : nameToSubclassMap.values()) {
			methodDecls.addAll(sb.getMethodsToPushDown());
		}
		for (MethodDeclaration md: methodDecls) {
			sourceRewriter.remove(md, null);			
		}
	}
	
	private void removeFieldsThatWillBePushedDown(ASTRewrite sourceRewriter) {
		Set<FieldDeclaration> fields = new LinkedHashSet<FieldDeclaration>();
		for (Subclass sb : nameToSubclassMap.values()) {
			for (VariableDeclarationFragment vfr : sb.getExclusiveFields()) {
				ASTNode parentNode = vfr.getParent();

				if (parentNode instanceof FieldDeclaration) {
				    FieldDeclaration fieldDeclaration = (FieldDeclaration) parentNode;
				    fields.add(fieldDeclaration);
				}
			}
		}
		for (FieldDeclaration fd: fields) {
			sourceRewriter.remove(fd, null);			
		}
	}
	
	private void modifyBaseClassConstructorToSetOnlySharedFields(AST ast, ASTRewrite rewriter) {
	    Set<VariableDeclarationFragment> sharedFields = baseClassSharedFields;
	    MethodDeclaration constructor = typeCheckElimination.getTypeFieldConsturctorMethod();
	    LinkedHashSet<String> paramsToKeep = new LinkedHashSet<String>();
	    for (VariableDeclarationFragment param : sharedFields) {
	    	paramsToKeep.add(param.getName().getIdentifier());
	    }
	    
	    // remove all the parameters by name
	    ListRewrite parametersRewrite = rewriter.getListRewrite(constructor, MethodDeclaration.PARAMETERS_PROPERTY);
	    @SuppressWarnings("unchecked")
	    List<SingleVariableDeclaration> parameters = constructor.parameters();
	    for (SingleVariableDeclaration parameter : parameters) {
	        String parameterName = parameter.getName().getIdentifier();
	        if (!paramsToKeep.contains(parameterName)) {
	            parametersRewrite.remove(parameter, null);
	        }
	    }
	    
	    // replace constructors body with only the shared fields
	    Block newBlock = ast.newBlock();
	    for (String fieldName : paramsToKeep) {
	        FieldAccess fieldAccess = ast.newFieldAccess();
	        fieldAccess.setName(ast.newSimpleName(fieldName));
	        fieldAccess.setExpression(ast.newThisExpression());
	        
	        Assignment assignment = ast.newAssignment();
	        assignment.setLeftHandSide(fieldAccess);
	        assignment.setRightHandSide(ast.newSimpleName(fieldName));
	        
	        ExpressionStatement expressionStatement = ast.newExpressionStatement(assignment);
	        newBlock.statements().add(expressionStatement); // Add the statement to the new block
	    }
	    rewriter.replace(constructor.getBody(), newBlock, null);
	}

	
	private void createFactoryMethod(AST ast, ASTRewrite rewriter) {	
		MethodDeclaration factoryMethod = ast.newMethodDeclaration();
		SimpleName typeName = ast.newSimpleName(baseClassTypeDecleration.getName().getIdentifier());
		factoryMethod.setReturnType2(ast.newSimpleType(typeName));
		factoryMethod.setName(ast.newSimpleName("create"));
		factoryMethod.modifiers().add(ast.newModifier(Modifier.ModifierKeyword.PUBLIC_KEYWORD));
		factoryMethod.modifiers().add(ast.newModifier(Modifier.ModifierKeyword.STATIC_KEYWORD));
		
		
		String parameterNameOfTypeField = findParameterSettingField();
		MethodDeclaration oldConstructor = typeCheckElimination.getTypeFieldConsturctorMethod();
		if (oldConstructor != null) {
		    ListRewrite parameterRewrite = rewriter.getListRewrite(factoryMethod, MethodDeclaration.PARAMETERS_PROPERTY);
		    for (Object parameter : oldConstructor.parameters()) {
		        SingleVariableDeclaration param = (SingleVariableDeclaration) parameter;
		        parameterRewrite.insertLast(ASTNode.copySubtree(ast, param), null);		        	
		    }
		}
		
		Block methodBody = ast.newBlock();

		SwitchStatement swst = createSwitchStatement(ast, rewriter);
		
		ListRewrite bodyRewrite = rewriter.getListRewrite(methodBody, Block.STATEMENTS_PROPERTY);
		bodyRewrite.insertLast(swst, null);
		
		rewriter.set(factoryMethod, MethodDeclaration.BODY_PROPERTY, methodBody, null);

		ListRewrite baseClassListRewriter = rewriter.getListRewrite(baseClassTypeDecleration, TypeDeclaration.BODY_DECLARATIONS_PROPERTY);
		
		baseClassListRewriter.insertLast(factoryMethod, null);
		
	}

    private SwitchStatement createSwitchStatement(AST ast, ASTRewrite rewriter) {
    	String fieldName = findParameterSettingField();
        SwitchStatement switchStatement = ast.newSwitchStatement();
        SimpleName typeName = ast.newSimpleName(fieldName);
        switchStatement.setExpression(typeName);
        
        ListRewrite switchStatementsRewrite = rewriter.getListRewrite(switchStatement, SwitchStatement.STATEMENTS_PROPERTY);

        for (Map.Entry<SimpleName, String> entry : staticFieldMap.entrySet()) {
            SimpleName caseField = entry.getKey();
            String className = entry.getValue();

            SwitchCase switchCase = ast.newSwitchCase();
            switchCase.expressions().add(ast.newSimpleName(caseField.getIdentifier()));

            ReturnStatement returnStatement = ast.newReturnStatement();
            ClassInstanceCreation creation = ast.newClassInstanceCreation();
            creation.setType(ast.newSimpleType(ast.newSimpleName(className)));
            
            Subclass sb = nameToSubclassMap.get(className);
		    ListRewrite argumentRewrite = rewriter.getListRewrite(creation, ClassInstanceCreation.ARGUMENTS_PROPERTY);
			for (VariableDeclarationFragment baseClassField : sb.getAllReferencedFields()) {
				SimpleName argumentName = ast.newSimpleName(baseClassField.getName().getIdentifier());
				argumentRewrite.insertLast(argumentName, null);
			}
			
            returnStatement.setExpression(creation);

            switchStatementsRewrite.insertLast(switchCase, null);
            switchStatementsRewrite.insertLast(returnStatement, null);
        }

        SwitchCase defaultCase = ast.newSwitchCase();
        defaultCase.setExpression(null); // Indicates the default case
        ThrowStatement throwStatement = ast.newThrowStatement();
        ClassInstanceCreation exceptionCreation = ast.newClassInstanceCreation();
        exceptionCreation.setType(ast.newSimpleType(ast.newSimpleName("IllegalArgumentException")));
        StringLiteral message = ast.newStringLiteral();
        message.setLiteralValue("Incorrect type code value");
        exceptionCreation.arguments().add(message);
        throwStatement.setExpression(exceptionCreation);

        switchStatementsRewrite.insertLast(defaultCase, null);
        switchStatementsRewrite.insertLast(throwStatement, null);


        return switchStatement;
    }
    
	
	private String findParameterSettingField() {
		MethodDeclaration constructor = typeCheckElimination.getTypeFieldConsturctorMethod();
		String fieldName = typeCheckElimination.getTypeField().getName().getIdentifier();

	    Block body = constructor.getBody();
	    for (Object stObj : body.statements()) {
	    	Statement statement = (Statement) stObj;
	        if (statement instanceof ExpressionStatement) {
	            Expression expression = ((ExpressionStatement) statement).getExpression();
	            
	            if (expression instanceof Assignment) {
	                Assignment assignment = (Assignment) expression;
	                
	                if (assignment.getLeftHandSide() instanceof FieldAccess) {
	                    FieldAccess fieldAccess = (FieldAccess) assignment.getLeftHandSide();
	                    if (fieldAccess.getName().getIdentifier().equals(fieldName)) {
	                        if (assignment.getRightHandSide() instanceof SimpleName) {
	                            SimpleName rightHandSideName = (SimpleName) assignment.getRightHandSide();
	                            return rightHandSideName.getIdentifier();
	                        }
	                    }
	                }
	                else if (assignment.getLeftHandSide() instanceof SimpleName) {
	                    SimpleName leftHandSideName = (SimpleName) assignment.getLeftHandSide();
	                    if (leftHandSideName.getIdentifier().equals(fieldName)) {
	                        if (assignment.getRightHandSide() instanceof SimpleName) {
	                            SimpleName rightHandSideName = (SimpleName) assignment.getRightHandSide();
	                            return rightHandSideName.getIdentifier();
	                        }
	                    }
	                }
	            }
	        }
	    }
	    return null;
	}
	

	
	private void createSubclasses() {
		List<String> subclassNames = new ArrayList<String>(staticFieldMap.values());
		List<ArrayList<Statement>> typeCheckStatements = typeCheckElimination.getTypeCheckStatements();
		subclassNames.addAll(additionalStaticFieldMap.values());
		IContainer contextContainer = (IContainer)sourceFile.getParent();
		List<SimpleName> staticFields = new ArrayList<SimpleName>(staticFieldMap.keySet());
		for(SimpleName simpleName : additionalStaticFieldMap.keySet())
			staticFields.add(simpleName);
		
		String abstractClassName = baseClassName;
		for(int i=0; i<subclassNames.size(); i++) {
			ArrayList<Statement> statements = null;
			DefaultMutableTreeNode remainingIfStatementExpression = null;
			if(i < typeCheckStatements.size()) {
				statements = typeCheckStatements.get(i);
				Expression expression = typeCheckElimination.getExpressionCorrespondingToTypeCheckStatementList(statements);
				remainingIfStatementExpression = typeCheckElimination.getRemainingIfStatementExpression(expression);
			}
			else {
				statements = typeCheckElimination.getDefaultCaseStatements();
			}
			InheritanceTree tree = typeCheckElimination.getInheritanceTreeMatchingWithStaticTypes();
			IFile subclassFile = null;
			if(tree != null) {
				DefaultMutableTreeNode rootNode = tree.getRootNode();
				DefaultMutableTreeNode leaf = rootNode.getFirstLeaf();
				while(leaf != null) {
					String qualifiedSubclassName = (String)leaf.getUserObject();
					if((qualifiedSubclassName.contains(".") && qualifiedSubclassName.endsWith("." + subclassNames.get(i))) || qualifiedSubclassName.equals(subclassNames.get(i))) {
						subclassFile = getFile(qualifiedSubclassName);
						break;
					}
					leaf = leaf.getNextLeaf();
				}
			}
			else {
				if(contextContainer instanceof IProject) {
					IProject contextProject = (IProject)contextContainer;
					subclassFile = contextProject.getFile(subclassNames.get(i) + ".java");
				}
				else if(contextContainer instanceof IFolder) {
					IFolder contextFolder = (IFolder)contextContainer;
					subclassFile = contextFolder.getFile(subclassNames.get(i) + ".java");
				}
			}
			boolean subclassAlreadyExists = false;
			ICompilationUnit subclassICompilationUnit = JavaCore.createCompilationUnitFrom(subclassFile);
			javaElementsToOpenInEditor.add(subclassICompilationUnit);
			ASTParser subclassParser = ASTParser.newParser(ASTReader.JLS);
			subclassParser.setKind(ASTParser.K_COMPILATION_UNIT);
			Document subclassDocument = null;
			if(subclassFile.exists()) {
				subclassAlreadyExists = true;
				subclassParser.setSource(subclassICompilationUnit);
				subclassParser.setResolveBindings(true); // we need bindings later on
			}
			else {
				subclassDocument = new Document();
				subclassParser.setSource(subclassDocument.get().toCharArray());
			}
			
	        CompilationUnit subclassCompilationUnit = (CompilationUnit)subclassParser.createAST(null);
	        AST subclassAST = subclassCompilationUnit.getAST();
	        ASTRewrite subclassRewriter = ASTRewrite.create(subclassAST);
	        ListRewrite subclassTypesRewrite = subclassRewriter.getListRewrite(subclassCompilationUnit, CompilationUnit.TYPES_PROPERTY);
			
			TypeDeclaration subclassTypeDeclaration = null;
			if(subclassAlreadyExists) {
				List<AbstractTypeDeclaration> abstractTypeDeclarations = subclassCompilationUnit.types();
				for(AbstractTypeDeclaration abstractTypeDeclaration : abstractTypeDeclarations) {
					if(abstractTypeDeclaration instanceof TypeDeclaration) {
						TypeDeclaration typeDeclaration = (TypeDeclaration)abstractTypeDeclaration;
						if(typeDeclaration.getName().getIdentifier().equals(subclassNames.get(i))) {
							subclassTypeDeclaration = typeDeclaration;
							requiredImportDeclarationsForContext.add(subclassTypeDeclaration.resolveBinding());
							break;
						}
					}
				}
			}
			else {
				if(sourceCompilationUnit.getPackage() != null) {
					subclassRewriter.set(subclassCompilationUnit, CompilationUnit.PACKAGE_PROPERTY, sourceCompilationUnit.getPackage(), null);
				}
				Javadoc subclassJavaDoc = subclassAST.newJavadoc();
				TagElement subclassTagElement = subclassAST.newTagElement();
				subclassRewriter.set(subclassTagElement, TagElement.TAG_NAME_PROPERTY, TagElement.TAG_SEE, null);
				
				MemberRef subclassMemberRef = subclassAST.newMemberRef();
				IBinding staticFieldNameBinding = staticFields.get(i).resolveBinding();
				ITypeBinding staticFieldNameDeclaringClass = null;
				if(staticFieldNameBinding != null && staticFieldNameBinding.getKind() == IBinding.VARIABLE) {
					IVariableBinding staticFieldNameVariableBinding = (IVariableBinding)staticFieldNameBinding;
					staticFieldNameDeclaringClass = staticFieldNameVariableBinding.getDeclaringClass();
				}
				subclassRewriter.set(subclassMemberRef, MemberRef.NAME_PROPERTY, subclassAST.newSimpleName(staticFieldNameBinding.getName()), null);
				subclassRewriter.set(subclassMemberRef, MemberRef.QUALIFIER_PROPERTY, subclassAST.newName(staticFieldNameDeclaringClass.getQualifiedName()), null);
				
				ListRewrite subclassTagElementFragmentsRewrite = subclassRewriter.getListRewrite(subclassTagElement, TagElement.FRAGMENTS_PROPERTY);
				subclassTagElementFragmentsRewrite.insertLast(subclassMemberRef, null);
				
				ListRewrite subclassJavaDocTagsRewrite = subclassRewriter.getListRewrite(subclassJavaDoc, Javadoc.TAGS_PROPERTY);
				subclassJavaDocTagsRewrite.insertLast(subclassTagElement, null);
				
				subclassTypeDeclaration = subclassAST.newTypeDeclaration();
				SimpleName subclassName = subclassAST.newSimpleName(subclassNames.get(i));
				subclassRewriter.set(subclassTypeDeclaration, TypeDeclaration.NAME_PROPERTY, subclassName, null);
				subclassRewriter.set(subclassTypeDeclaration, TypeDeclaration.SUPERCLASS_TYPE_PROPERTY, subclassAST.newSimpleType(subclassAST.newSimpleName(abstractClassName)), null);
				ListRewrite subclassModifiersRewrite = subclassRewriter.getListRewrite(subclassTypeDeclaration, TypeDeclaration.MODIFIERS2_PROPERTY);
				subclassModifiersRewrite.insertLast(subclassAST.newModifier(Modifier.ModifierKeyword.PUBLIC_KEYWORD), null);
				subclassRewriter.set(subclassTypeDeclaration, TypeDeclaration.JAVADOC_PROPERTY, subclassJavaDoc, null);
			}
			ListRewrite subclassBodyRewrite = subclassRewriter.getListRewrite(subclassTypeDeclaration, TypeDeclaration.BODY_DECLARATIONS_PROPERTY);
					
			String subclassName = subclassNames.get(i);
			Subclass sb = nameToSubclassMap.get(subclassName);
			
			Set<VariableDeclarationFragment> pushedDownFields =  pushDownSubclassSpecificFields(subclassNames.get(i), subclassRewriter, subclassAST, subclassTypeDeclaration);
			sb.createSubclassConstructor(sb, subclassAST, subclassRewriter, subclassBodyRewrite, subclassCompilationUnit);
//			createSubclassConstructor(sb, subclassAST, subclassRewriter, subclassBodyRewrite, subclassCompilationUnit);
			pushDownMethods(subclassNames.get(i), subclassAST, subclassRewriter, subclassBodyRewrite, subclassCompilationUnit);
/*
			
			if(typeCheckElimination.getTypeField() != null) {
				if(getterMethod != null) {
					MethodDeclaration concreteGetterMethodDeclaration = subclassAST.newMethodDeclaration();
					subclassRewriter.set(concreteGetterMethodDeclaration, MethodDeclaration.NAME_PROPERTY, getterMethod.getName(), null);
					subclassRewriter.set(concreteGetterMethodDeclaration, MethodDeclaration.RETURN_TYPE2_PROPERTY, getterMethod.getReturnType2(), null);
					ListRewrite concreteGetterMethodModifiersRewrite = subclassRewriter.getListRewrite(concreteGetterMethodDeclaration, MethodDeclaration.MODIFIERS2_PROPERTY);
					concreteGetterMethodModifiersRewrite.insertLast(subclassAST.newModifier(Modifier.ModifierKeyword.PUBLIC_KEYWORD), null);
					Block concreteGetterMethodBody = subclassAST.newBlock();
					ListRewrite concreteGetterMethodBodyRewrite = subclassRewriter.getListRewrite(concreteGetterMethodBody, Block.STATEMENTS_PROPERTY);
					ReturnStatement returnStatement = subclassAST.newReturnStatement();
					IBinding staticFieldNameBinding = staticFields.get(i).resolveBinding();
					String staticFieldNameDeclaringClass = null;
					if(staticFieldNameBinding != null && staticFieldNameBinding.getKind() == IBinding.VARIABLE) {
						IVariableBinding staticFieldNameVariableBinding = (IVariableBinding)staticFieldNameBinding;
						ITypeBinding staticFieldDeclaringClass = staticFieldNameVariableBinding.getDeclaringClass();
						String staticFieldDeclaringClassQualifiedName = staticFieldDeclaringClass.getQualifiedName();
						IPackageBinding packageBinding = staticFieldDeclaringClass.getPackage();
						if(packageBinding != null && !packageBinding.getName().equals("")) {
							String packageBindingQualifiedName = packageBinding.getName();
							staticFieldNameDeclaringClass = staticFieldDeclaringClassQualifiedName.substring(
									packageBindingQualifiedName.length() + 1, staticFieldDeclaringClassQualifiedName.length());
						}
						else {
							staticFieldNameDeclaringClass = staticFieldDeclaringClassQualifiedName;
						}
					}
					FieldAccess fieldAccess = subclassAST.newFieldAccess();
					subclassRewriter.set(fieldAccess, FieldAccess.NAME_PROPERTY, staticFields.get(i), null);
					if(!staticFieldNameDeclaringClass.contains(".")) {
						subclassRewriter.set(fieldAccess, FieldAccess.EXPRESSION_PROPERTY, subclassAST.newSimpleName(staticFieldNameDeclaringClass), null);
					}
					else {
						QualifiedName qualifiedName = subclassAST.newQualifiedName(
								subclassAST.newName(staticFieldNameDeclaringClass.substring(0, staticFieldNameDeclaringClass.lastIndexOf("."))),
								subclassAST.newSimpleName(staticFieldNameDeclaringClass.substring(staticFieldNameDeclaringClass.lastIndexOf(".") + 1,
								staticFieldNameDeclaringClass.length())));
						subclassRewriter.set(fieldAccess, FieldAccess.EXPRESSION_PROPERTY, qualifiedName, null);
					}
					subclassRewriter.set(returnStatement, ReturnStatement.EXPRESSION_PROPERTY, fieldAccess, null);
					concreteGetterMethodBodyRewrite.insertLast(returnStatement, null);
					subclassRewriter.set(concreteGetterMethodDeclaration, MethodDeclaration.BODY_PROPERTY, concreteGetterMethodBody, null);
					subclassBodyRewrite.insertLast(concreteGetterMethodDeclaration, null);
				}
				else {
					MethodDeclaration concreteGetterMethodDeclaration = subclassAST.newMethodDeclaration();
					subclassRewriter.set(concreteGetterMethodDeclaration, MethodDeclaration.NAME_PROPERTY, subclassAST.newSimpleName("get" + abstractClassName), null);
					VariableDeclarationFragment typeField = typeCheckElimination.getTypeField();
					Type returnType = ((FieldDeclaration)typeField.getParent()).getType();
					subclassRewriter.set(concreteGetterMethodDeclaration, MethodDeclaration.RETURN_TYPE2_PROPERTY, returnType, null);
					ListRewrite concreteGetterMethodModifiersRewrite = subclassRewriter.getListRewrite(concreteGetterMethodDeclaration, MethodDeclaration.MODIFIERS2_PROPERTY);
					concreteGetterMethodModifiersRewrite.insertLast(subclassAST.newModifier(Modifier.ModifierKeyword.PUBLIC_KEYWORD), null);
					Block concreteGetterMethodBody = subclassAST.newBlock();
					ListRewrite concreteGetterMethodBodyRewrite = subclassRewriter.getListRewrite(concreteGetterMethodBody, Block.STATEMENTS_PROPERTY);
					ReturnStatement returnStatement = subclassAST.newReturnStatement();
					IBinding staticFieldNameBinding = staticFields.get(i).resolveBinding();
					String staticFieldNameDeclaringClass = null;
					if(staticFieldNameBinding != null && staticFieldNameBinding.getKind() == IBinding.VARIABLE) {
						IVariableBinding staticFieldNameVariableBinding = (IVariableBinding)staticFieldNameBinding;
						staticFieldNameDeclaringClass = staticFieldNameVariableBinding.getDeclaringClass().getName();
					}
					FieldAccess fieldAccess = subclassAST.newFieldAccess();
					subclassRewriter.set(fieldAccess, FieldAccess.NAME_PROPERTY, staticFields.get(i), null);
					subclassRewriter.set(fieldAccess, FieldAccess.EXPRESSION_PROPERTY, subclassAST.newSimpleName(staticFieldNameDeclaringClass), null);
					subclassRewriter.set(returnStatement, ReturnStatement.EXPRESSION_PROPERTY, fieldAccess, null);
					concreteGetterMethodBodyRewrite.insertLast(returnStatement, null);
					subclassRewriter.set(concreteGetterMethodDeclaration, MethodDeclaration.BODY_PROPERTY, concreteGetterMethodBody, null);
					subclassBodyRewrite.insertLast(concreteGetterMethodDeclaration, null);
				}
			}
*/			

			
			MethodDeclaration concreteMethodDeclaration = subclassAST.newMethodDeclaration();
			subclassRewriter.set(concreteMethodDeclaration, MethodDeclaration.NAME_PROPERTY, subclassAST.newSimpleName(typeCheckElimination.getAbstractMethodName()), null);
			if(returnedVariable == null && !typeCheckElimination.typeCheckCodeFragmentContainsReturnStatement()) {
				subclassRewriter.set(concreteMethodDeclaration, MethodDeclaration.RETURN_TYPE2_PROPERTY, subclassAST.newPrimitiveType(PrimitiveType.VOID), null);
			}
			else {
				if(returnedVariable != null) {
					Type returnType = null;
					if(returnedVariable instanceof SingleVariableDeclaration) {
						SingleVariableDeclaration singleVariableDeclaration = (SingleVariableDeclaration)returnedVariable;
						returnType = singleVariableDeclaration.getType();
					}
					else if(returnedVariable instanceof VariableDeclarationFragment) {
						VariableDeclarationFragment variableDeclarationFragment = (VariableDeclarationFragment)returnedVariable;
						if(variableDeclarationFragment.getParent() instanceof VariableDeclarationStatement) {
							VariableDeclarationStatement variableDeclarationStatement = (VariableDeclarationStatement)variableDeclarationFragment.getParent();
							returnType = variableDeclarationStatement.getType();
						}
						else if(variableDeclarationFragment.getParent() instanceof VariableDeclarationExpression) {
							VariableDeclarationExpression variableDeclarationExpression = (VariableDeclarationExpression)variableDeclarationFragment.getParent();
							returnType = variableDeclarationExpression.getType();
						}
						else if(variableDeclarationFragment.getParent() instanceof FieldDeclaration) {
							FieldDeclaration fieldDeclaration = (FieldDeclaration)variableDeclarationFragment.getParent();
							returnType = fieldDeclaration.getType();
						}
					}
					subclassRewriter.set(concreteMethodDeclaration, MethodDeclaration.RETURN_TYPE2_PROPERTY, returnType, null);
				}
				else {
					subclassRewriter.set(concreteMethodDeclaration, MethodDeclaration.RETURN_TYPE2_PROPERTY, typeCheckElimination.getTypeCheckMethodReturnType(), null);
				}
			}
			ListRewrite concreteMethodModifiersRewrite = subclassRewriter.getListRewrite(concreteMethodDeclaration, MethodDeclaration.MODIFIERS2_PROPERTY);
			concreteMethodModifiersRewrite.insertLast(subclassAST.newModifier(Modifier.ModifierKeyword.PUBLIC_KEYWORD), null);
			ListRewrite concreteMethodParametersRewrite = subclassRewriter.getListRewrite(concreteMethodDeclaration, MethodDeclaration.PARAMETERS_PROPERTY);

			if(returnedVariable != null) {
				if(returnedVariable instanceof SingleVariableDeclaration) {
					SingleVariableDeclaration singleVariableDeclaration = (SingleVariableDeclaration)returnedVariable;
					concreteMethodParametersRewrite.insertLast(singleVariableDeclaration, null);
				}
				else if(returnedVariable instanceof VariableDeclarationFragment) {
					SingleVariableDeclaration parameter = subclassAST.newSingleVariableDeclaration();
					VariableDeclarationFragment variableDeclarationFragment = (VariableDeclarationFragment)returnedVariable;
					Type type = null;
					if(variableDeclarationFragment.getParent() instanceof VariableDeclarationStatement) {
						VariableDeclarationStatement variableDeclarationStatement = (VariableDeclarationStatement)variableDeclarationFragment.getParent();
						type = variableDeclarationStatement.getType();
					}
					else if(variableDeclarationFragment.getParent() instanceof VariableDeclarationExpression) {
						VariableDeclarationExpression variableDeclarationExpression = (VariableDeclarationExpression)variableDeclarationFragment.getParent();
						type = variableDeclarationExpression.getType();
					}
					else if(variableDeclarationFragment.getParent() instanceof FieldDeclaration) {
						FieldDeclaration fieldDeclaration = (FieldDeclaration)variableDeclarationFragment.getParent();
						type = fieldDeclaration.getType();
					}
					subclassRewriter.set(parameter, SingleVariableDeclaration.TYPE_PROPERTY, type, null);
					subclassRewriter.set(parameter, SingleVariableDeclaration.NAME_PROPERTY, variableDeclarationFragment.getName(), null);
					concreteMethodParametersRewrite.insertLast(parameter, null);
				}
			}

			for(SingleVariableDeclaration abstractMethodParameter : typeCheckElimination.getAccessedParameters()) {
				if(!abstractMethodParameter.equals(returnedVariable)) {
					concreteMethodParametersRewrite.insertLast(abstractMethodParameter, null);
				}
			}
			for(VariableDeclaration fragment : typeCheckElimination.getAccessedLocalVariables()) {
				if(!fragment.equals(returnedVariable)) {
					if(fragment instanceof SingleVariableDeclaration) {
						SingleVariableDeclaration singleVariableDeclaration = (SingleVariableDeclaration)fragment;
						concreteMethodParametersRewrite.insertLast(singleVariableDeclaration, null);
					}
					else if(fragment instanceof VariableDeclarationFragment) {
						SingleVariableDeclaration parameter = subclassAST.newSingleVariableDeclaration();
						VariableDeclarationFragment variableDeclarationFragment = (VariableDeclarationFragment)fragment;
						Type type = null;
						if(variableDeclarationFragment.getParent() instanceof VariableDeclarationStatement) {
							VariableDeclarationStatement variableDeclarationStatement = (VariableDeclarationStatement)variableDeclarationFragment.getParent();
							type = variableDeclarationStatement.getType();
						}
						else if(variableDeclarationFragment.getParent() instanceof VariableDeclarationExpression) {
							VariableDeclarationExpression variableDeclarationExpression = (VariableDeclarationExpression)variableDeclarationFragment.getParent();
							type = variableDeclarationExpression.getType();
						}
						else if(variableDeclarationFragment.getParent() instanceof FieldDeclaration) {
							FieldDeclaration fieldDeclaration = (FieldDeclaration)variableDeclarationFragment.getParent();
							type = fieldDeclaration.getType();
						}
						subclassRewriter.set(parameter, SingleVariableDeclaration.TYPE_PROPERTY, type, null);
						subclassRewriter.set(parameter, SingleVariableDeclaration.NAME_PROPERTY, variableDeclarationFragment.getName(), null);
						concreteMethodParametersRewrite.insertLast(parameter, null);
					}
				}
			}
			
			Set<VariableDeclarationFragment> accessedFields = typeCheckElimination.getAccessedFields();
			Set<VariableDeclarationFragment> assignedFields = typeCheckElimination.getAssignedFields();
			Set<MethodDeclaration> accessedMethods = typeCheckElimination.getAccessedMethods();
			Set<IMethodBinding> superAccessedMethods = typeCheckElimination.getSuperAccessedMethods();
			Set<IVariableBinding> superAccessedFields = typeCheckElimination.getSuperAccessedFieldBindings();
			Set<IVariableBinding> superAssignedFields = typeCheckElimination.getSuperAssignedFieldBindings();
//			if(sourceTypeRequiredForExtraction()) {
//				SingleVariableDeclaration parameter = subclassAST.newSingleVariableDeclaration();
//				SimpleName parameterType = subclassAST.newSimpleName(sourceTypeDeclaration.getName().getIdentifier());
//				subclassRewriter.set(parameter, SingleVariableDeclaration.TYPE_PROPERTY, subclassAST.newSimpleType(parameterType), null);
//				String parameterName = sourceTypeDeclaration.getName().getIdentifier();
//				parameterName = parameterName.substring(0,1).toLowerCase() + parameterName.substring(1,parameterName.length());
//				subclassRewriter.set(parameter, SingleVariableDeclaration.NAME_PROPERTY, subclassAST.newSimpleName(parameterName), null);
//				concreteMethodParametersRewrite.insertLast(parameter, null);
//			}
			
			ListRewrite concreteMethodThrownExceptionsRewrite = subclassRewriter.getListRewrite(concreteMethodDeclaration, MethodDeclaration.THROWN_EXCEPTION_TYPES_PROPERTY);
			for(ITypeBinding typeBinding : thrownExceptions) {
				concreteMethodThrownExceptionsRewrite.insertLast(RefactoringUtility.generateTypeFromTypeBinding(typeBinding, subclassAST, subclassRewriter), null);
			}
			
			Block concreteMethodBody = subclassAST.newBlock();
			ListRewrite concreteMethodBodyRewrite = subclassRewriter.getListRewrite(concreteMethodBody, Block.STATEMENTS_PROPERTY);
			ExpressionExtractor expressionExtractor = new ExpressionExtractor();
			ListRewrite ifStatementBodyRewrite = null;
			if(remainingIfStatementExpression != null) {
				IfStatement enclosingIfStatement = subclassAST.newIfStatement();
				Expression enclosingIfStatementExpression = constructExpression(subclassAST, remainingIfStatementExpression);
				Expression newEnclosingIfStatementExpression = (Expression)ASTNode.copySubtree(subclassAST, enclosingIfStatementExpression);
				List<Expression> oldVariableInstructions = expressionExtractor.getVariableInstructions(enclosingIfStatementExpression);
				List<Expression> newVariableInstructions = expressionExtractor.getVariableInstructions(newEnclosingIfStatementExpression);
				modifySourceVariableInstructionsInSubclass(oldVariableInstructions, newVariableInstructions, subclassAST, subclassRewriter, accessedFields, assignedFields, superAccessedFields, superAssignedFields);
				List<Expression> oldMethodInvocations = expressionExtractor.getMethodInvocations(enclosingIfStatementExpression);
				List<Expression> newMethodInvocations = expressionExtractor.getMethodInvocations(newEnclosingIfStatementExpression);
				modifySourceMethodInvocationsInSubclass(oldMethodInvocations, newMethodInvocations, subclassAST, subclassRewriter, accessedMethods, superAccessedMethods);
				replaceThisExpressionWithContextParameterInMethodInvocationArguments(newMethodInvocations, subclassAST, subclassRewriter);
				subclassRewriter.set(enclosingIfStatement, IfStatement.EXPRESSION_PROPERTY, newEnclosingIfStatementExpression, null);
				Block ifStatementBody = subclassAST.newBlock();
				ifStatementBodyRewrite = subclassRewriter.getListRewrite(ifStatementBody, Block.STATEMENTS_PROPERTY);
				subclassRewriter.set(enclosingIfStatement, IfStatement.THEN_STATEMENT_PROPERTY, ifStatementBody, null);
				concreteMethodBodyRewrite.insertLast(enclosingIfStatement, null);
			}
			for(Statement statement : statements) {
				Statement newStatement = (Statement)ASTNode.copySubtree(subclassAST, statement);
//				List<Expression> oldVariableInstructions = expressionExtractor.getVariableInstructions(statement);
//				List<Expression> newVariableInstructions = expressionExtractor.getVariableInstructions(newStatement);
//				modifySourceVariableInstructionsInSubclass(oldVariableInstructions, newVariableInstructions, subclassAST, subclassRewriter, accessedFields, assignedFields, superAccessedFields, superAssignedFields);
				List<Expression> oldMethodInvocations = expressionExtractor.getMethodInvocations(statement);
				List<Expression> newMethodInvocations = expressionExtractor.getMethodInvocations(newStatement);
//				modifySourceMethodInvocationsInSubclass(oldMethodInvocations, newMethodInvocations, subclassAST, subclassRewriter, accessedMethods, superAccessedMethods);
				replaceThisExpressionWithContextParameterInMethodInvocationArguments(newMethodInvocations, subclassAST, subclassRewriter);
				replaceThisExpressionWithContextParameterInClassInstanceCreationArguments(newStatement, subclassAST, subclassRewriter);
				if(ifStatementBodyRewrite != null)
					ifStatementBodyRewrite.insertLast(newStatement, null);
				else
					concreteMethodBodyRewrite.insertLast(newStatement, null);
			}
			if(returnedVariable != null) {
				ReturnStatement returnStatement = subclassAST.newReturnStatement();
				subclassRewriter.set(returnStatement, ReturnStatement.EXPRESSION_PROPERTY, returnedVariable.getName(), null);
				concreteMethodBodyRewrite.insertLast(returnStatement, null);
			}
			subclassRewriter.set(concreteMethodDeclaration, MethodDeclaration.BODY_PROPERTY, concreteMethodBody, null);
			

//			// temp
//			Block concreteMethodBody = subclassAST.newBlock();
//			subclassRewriter.set(concreteMethodDeclaration, MethodDeclaration.BODY_PROPERTY, concreteMethodBody, null);
//			// temp
			subclassBodyRewrite.insertLast(concreteMethodDeclaration, null);
			
			if(!subclassAlreadyExists)
				subclassTypesRewrite.insertLast(subclassTypeDeclaration, null);
			
			if(subclassDocument != null) {
				try {
//					for(ITypeBinding typeBinding : requiredImportDeclarationsBasedOnSignature) {
//						addImportDeclaration(typeBinding, subclassCompilationUnit, subclassRewriter);
//					}
//					Set<ITypeBinding> requiredImportDeclarationsBasedOnBranch = getRequiredImportDeclarationsBasedOnBranch(statements);
//					for(ITypeBinding typeBinding : requiredImportDeclarationsBasedOnBranch) {
//						if(!requiredImportDeclarationsBasedOnSignature.contains(typeBinding))
//							addImportDeclaration(typeBinding, subclassCompilationUnit, subclassRewriter);
//					}
					TextEdit subclassEdit = subclassRewriter.rewriteAST(subclassDocument, null);
					subclassEdit.apply(subclassDocument);
					CreateCompilationUnitChange createCompilationUnitChange =
						new CreateCompilationUnitChange(subclassICompilationUnit, subclassDocument.get(), subclassFile.getCharset());
					createCompilationUnitChanges.put(subclassICompilationUnit, createCompilationUnitChange);
				} catch (CoreException e) {
					e.printStackTrace();
				} catch (MalformedTreeException e) {
					e.printStackTrace();
				} catch (BadLocationException e) {
					e.printStackTrace();
				}
			}
			else {
				try {
					MultiTextEdit subclassMultiTextEdit = new MultiTextEdit();
					CompilationUnitChange subclassCompilationUnitChange = new CompilationUnitChange("", subclassICompilationUnit);
					subclassCompilationUnitChange.setEdit(subclassMultiTextEdit);
					compilationUnitChanges.put(subclassICompilationUnit, subclassCompilationUnitChange);
					
					ImportRewrite subclassImportRewrite = ImportRewrite.create(subclassCompilationUnit, true);
					for(ITypeBinding typeBinding : requiredImportDeclarationsBasedOnSignature) {
						if(!typeBinding.isNested())
							subclassImportRewrite.addImport(typeBinding);
					}
//					Set<ITypeBinding> requiredImportDeclarationsBasedOnBranch = getRequiredImportDeclarationsBasedOnBranch(statements);
//					for(ITypeBinding typeBinding : requiredImportDeclarationsBasedOnBranch) {
//						if(!typeBinding.isNested())
//							subclassImportRewrite.addImport(typeBinding);
//					}
					
					TextEdit subclassImportEdit = subclassImportRewrite.rewriteImports(null);
					if(subclassImportRewrite.getCreatedImports().length > 0) {
						subclassMultiTextEdit.addChild(subclassImportEdit);
						subclassCompilationUnitChange.addTextEditGroup(new TextEditGroup("Add required import declarations", new TextEdit[] {subclassImportEdit}));
					}
					
					TextEdit subclassEdit = subclassRewriter.rewriteAST();
					subclassMultiTextEdit.addChild(subclassEdit);
					subclassCompilationUnitChange.addTextEditGroup(new TextEditGroup("Create concrete State/Strategy", new TextEdit[] {subclassEdit}));
				} catch (JavaModelException e) {
					e.printStackTrace();
				} catch (CoreException e) {
					e.printStackTrace();
				}
			}
		}
	}
	
//	private void createSubclassConstructor(Subclass sb, AST ast, ASTRewrite rewriter, ListRewrite subclassBodyRewrite, CompilationUnit subclassCompilationUnit) {
//		String constructorName = sb.name;
//	    MethodDeclaration baseClassConstructor = typeCheckElimination.getTypeFieldConsturctorMethod();
//	    List<SingleVariableDeclaration> baseClassConstructorParams = baseClassConstructor.parameters();
//	    
//	    MethodDeclaration subclassConstructor = ast.newMethodDeclaration();
//	    // Set the constructor flag, name, and modifiers
//	    rewriter.set(subclassConstructor, MethodDeclaration.CONSTRUCTOR_PROPERTY, true, null);
//	    rewriter.set(subclassConstructor, MethodDeclaration.NAME_PROPERTY, ast.newSimpleName(constructorName), null);
//	    ListRewrite modifiersRewrite = rewriter.getListRewrite(subclassConstructor, MethodDeclaration.MODIFIERS2_PROPERTY);
//	    modifiersRewrite.insertLast(ast.newModifier(ModifierKeyword.PUBLIC_KEYWORD), null);
//
//	    ListRewrite parametersRewrite = rewriter.getListRewrite(subclassConstructor, MethodDeclaration.PARAMETERS_PROPERTY);
//	    for (SingleVariableDeclaration originalParam : baseClassConstructorParams) {
//	        SingleVariableDeclaration newParam = (SingleVariableDeclaration) ASTNode.copySubtree(ast, originalParam);
//	        parametersRewrite.insertLast(newParam, null);
//	    }
//	    
//	    for (VariableDeclarationFragment fragment : ) {
//	        Type fieldType = ((FieldDeclaration) fragment.getParent()).getType();
//	        
//	        SingleVariableDeclaration parameter = ast.newSingleVariableDeclaration();
//	        parameter.setType((Type) ASTNode.copySubtree(ast, fieldType)); 
//	        parameter.setName(ast.newSimpleName(fragment.getName().getIdentifier()));
//
//	        parametersRewrite.insertLast(parameter, null);
//	    }
//
//	    Block constructorBody = ast.newBlock();
//
//	    SuperConstructorInvocation superConstructorInvocation = ast.newSuperConstructorInvocation();
//	    ListRewrite argumentRewrite = rewriter.getListRewrite(superConstructorInvocation, SuperConstructorInvocation.ARGUMENTS_PROPERTY);
//	    for (SingleVariableDeclaration param : baseClassConstructorParams) {
//	        SimpleName argumentName = (SimpleName) ASTNode.copySubtree(ast, param.getName());
//	        argumentRewrite.insertLast(argumentName, null);
//	    }
//
//	    ListRewrite statementsRewrite = rewriter.getListRewrite(constructorBody, Block.STATEMENTS_PROPERTY);
//	    statementsRewrite.insertFirst(superConstructorInvocation, null);
//
//	    rewriter.set(subclassConstructor, MethodDeclaration.BODY_PROPERTY, constructorBody, null);
//
//	    subclassBodyRewrite.insertLast(subclassConstructor, null);
//	    
//	    Set<ITypeBinding> requiredImportDeclarationsBasedOnBranch = getRequiredImportDeclarationsParameters((List<SingleVariableDeclaration>) baseClassConstructorParams);
//		for(ITypeBinding typeBinding : requiredImportDeclarationsBasedOnBranch) {
//			if(!requiredImportDeclarationsBasedOnSignature.contains(typeBinding))
//				addImportDeclaration(typeBinding, subclassCompilationUnit, rewriter);
//		}
//	}
	
	private Set<ITypeBinding> getRequiredImportDeclarationsParameters(List<SingleVariableDeclaration> nodes) {
		Set<ITypeBinding> typeBindings = new LinkedHashSet<ITypeBinding>();
		for(ASTNode node : nodes) {
			TypeVisitor typeVisitor = new TypeVisitor();
			node.accept(typeVisitor);
			typeBindings.addAll(typeVisitor.getTypeBindings());
		}
		Set<ITypeBinding> finalTypeBindings = new LinkedHashSet<ITypeBinding>();
		RefactoringUtility.getSimpleTypeBindings(typeBindings, finalTypeBindings);
        return finalTypeBindings;
	}
	
	private void pushDownMethods(String subclassName, AST ast, ASTRewrite rewriter, ListRewrite subclassBodyRewrite, CompilationUnit subclassCompilationUnit) {
		Subclass sc = nameToSubclassMap.get(subclassName);
		Set<MethodDeclaration> methodDecls = sc.getMethodsToPushDown();
		for (MethodDeclaration md: methodDecls) {
			MethodDeclaration newMethodDeclaration = (MethodDeclaration) ASTNode.copySubtree(ast, md);
			subclassBodyRewrite.insertLast(newMethodDeclaration, null);			
		}
		
	}
	
	private Set<VariableDeclarationFragment> pushDownSubclassSpecificFields(String subclassName, ASTRewrite rewriter, AST ast, TypeDeclaration typeDecleartion) {
		Subclass sc = nameToSubclassMap.get(subclassName);
		Set<VariableDeclarationFragment> subclassSpecificFields = sc.getExclusiveFields();
		
		for (VariableDeclarationFragment fragment : subclassSpecificFields) {
	        FieldDeclaration field = (FieldDeclaration) fragment.getParent();
			FieldDeclaration newField = (FieldDeclaration) ASTNode.copySubtree(ast, field);
			ListRewrite targetListRewrite = rewriter.getListRewrite(typeDecleartion, typeDecleartion.getBodyDeclarationsProperty());
			targetListRewrite.insertLast(newField, null);
			
		}
		return subclassSpecificFields;
	}
	
	private void setFieldsUsedInBaseClassMethods() {
		ClassObject classObject = typeCheckElimination.getClassObject();
		for (MethodObject methodObject : classObject.getMethodList()) {
			if (methodObject.getMethodDeclaration() == typeCheckElimination.getTypeCheckMethod()) {
				continue;
			}
			Set<String> fieldNames = new LinkedHashSet<String>();
			for (PlainVariable pv : methodObject.getUsedFieldsThroughThisReference()) {
				fieldNames.add(pv.getVariableName());
			}
			Set<VariableDeclarationFragment> fieldsAsVdf = getVariableDeclarationFragmentsFromFieldNames(fieldNames, baseClassTypeDecleration);
			methodToFieldsUsed.put(methodObject.getMethodDeclaration(), fieldsAsVdf);
			if (MethodDeclarationUtility.isPublic(methodObject.getMethodDeclaration())) {
				fieldsUsedByPublicMethods.addAll(fieldsAsVdf);
			}
		}
		
	}
	
	private Set<VariableDeclarationFragment> getVariableDeclarationFragmentsFromFieldNames(Set<String> fieldNames, TypeDeclaration baseClassTypeDeclaration) {
		Set<VariableDeclarationFragment> fragments = new LinkedHashSet<VariableDeclarationFragment>();

        for (FieldDeclaration field : baseClassTypeDeclaration.getFields()) {
            for (Object fragmentObject : field.fragments()) {
                if (fragmentObject instanceof VariableDeclarationFragment) {
                    VariableDeclarationFragment fragment = (VariableDeclarationFragment) fragmentObject;
                    
                    if (fieldNames.contains(fragment.getName().getIdentifier())) {
                        fragments.add(fragment);
                    }
                }
            }
        }

        return fragments;
    }
	
	private void setBaseClassSharedFields(){
		Set<VariableDeclarationFragment> sharedFields = null;
		for (Subclass sb : nameToSubclassMap.values()) {
			Set<VariableDeclarationFragment> fields = sb.getAllReferencedFields();
            if (sharedFields == null) {
            	sharedFields = new LinkedHashSet<VariableDeclarationFragment>(fields);
            } else {
            	sharedFields.retainAll(fields);
            }
        }
        baseClassSharedFields = sharedFields;
	}
	
	private void setSubclassesExclusiveFields() {
		for (Subclass sb : nameToSubclassMap.values()) {
			Set<VariableDeclarationFragment> sbFields = new LinkedHashSet<VariableDeclarationFragment>(sb.getAllReferencedFields());
			sbFields.removeAll(baseClassSharedFields);
			sb.setExclusiveFields(sbFields);
        }
	}
	
	private void setCandidateMethodsToPushDown() {
		for (MethodDeclaration md : methodToFieldsUsed.keySet()) {
			Set<VariableDeclarationFragment> fieldsUsedInMethod = methodToFieldsUsed.get(md);
			if (!MethodDeclarationUtility.isPrivate(md) || fieldsUsedInMethod.size() == 0) {
				continue;
			}
			for (Subclass sb : nameToSubclassMap.values()) {
				if (sb.getAllReferencedFields().containsAll(fieldsUsedInMethod)) {
					if (sb.getExclusiveFields().containsAll(fieldsUsedInMethod)) {
						sb.addMethodToPushDown(md);
					} else {
						methodsUsedInSubclasses.add(md);
					}
				}
			}
		}
	}


	@Override
	public Change createChange(IProgressMonitor pm) throws CoreException,
			OperationCanceledException {
		try {
			pm.beginTask("Creating change...", 1);
			final Collection<Change> changes = new ArrayList<Change>();
			changes.addAll(compilationUnitChanges.values());
			changes.addAll(createCompilationUnitChanges.values());
			CompositeChange change = new CompositeChange(getName(), changes.toArray(new Change[changes.size()])) {
				@Override
				public ChangeDescriptor getDescriptor() {
					ICompilationUnit sourceICompilationUnit = (ICompilationUnit)sourceCompilationUnit.getJavaElement();
					String project = sourceICompilationUnit.getJavaProject().getElementName();
					String description = MessageFormat.format("Replace Type Code with Subclass in method ''{0}''", new Object[] { typeCheckElimination.getTypeCheckMethod().getName().getIdentifier()});
					String comment = null;
					return new RefactoringChangeDescriptor(new ReplaceTypeCodeWithStateStrategyDescriptor(project, description, comment,
							sourceFile, sourceCompilationUnit, sourceTypeDeclaration, typeCheckElimination));
				}
			};
			return change;
		} finally {
			pm.done();
		}
	}
	
	public CompilationUnit getSourceCompilationUnit() {
		return sourceCompilationUnit;
	}
	
	public String getAbstractClassName() {
		return baseClassName;
	}

	public SimpleName getTypeVariableSimpleName() {
		return typeCheckElimination.getTypeVariableSimpleName();
	}

	public Set<Map.Entry<SimpleName, String>> getStaticFieldMapEntrySet() {
		return staticFieldMap.entrySet();
	}

	public Set<Map.Entry<SimpleName, String>> getAdditionalStaticFieldMapEntrySet() {
		return additionalStaticFieldMap.entrySet();
	}
	
	public void setTypeNameForNamedConstant(SimpleName namedConstant, String typeName) {
		if(staticFieldMap.containsKey(namedConstant)) {
			staticFieldMap.put(namedConstant, typeName);
		}
		else if(additionalStaticFieldMap.containsKey(namedConstant)) {
			additionalStaticFieldMap.put(namedConstant, typeName);
		}
		else {
			baseClassName = typeName;
		}
	}

}
