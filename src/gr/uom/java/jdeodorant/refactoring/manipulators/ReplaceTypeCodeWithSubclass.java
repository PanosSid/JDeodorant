package gr.uom.java.jdeodorant.refactoring.manipulators;

import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
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
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.AbstractTypeDeclaration;
import org.eclipse.jdt.core.dom.Block;
import org.eclipse.jdt.core.dom.ClassInstanceCreation;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.IfStatement;
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
import org.eclipse.jdt.core.dom.SuperConstructorInvocation;
import org.eclipse.jdt.core.dom.TagElement;
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
import org.eclipse.jdt.core.search.IJavaSearchConstants;
import org.eclipse.jdt.core.search.IJavaSearchScope;
import org.eclipse.jdt.core.search.SearchEngine;
import org.eclipse.jdt.core.search.SearchMatch;
import org.eclipse.jdt.core.search.SearchParticipant;
import org.eclipse.jdt.core.search.SearchRequestor;
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
import gr.uom.java.ast.inheritance.InheritanceTree;
import gr.uom.java.ast.util.ExpressionExtractor;
import gr.uom.java.ast.util.TypeVisitor;

public class ReplaceTypeCodeWithSubclass extends PolymorphismRefactoring {
	private VariableDeclaration returnedVariable;
	private Set<ITypeBinding> requiredImportDeclarationsBasedOnSignature;
	private Set<ITypeBinding> requiredImportDeclarationsForContext;
	private Set<ITypeBinding> thrownExceptions;
	private Map<SimpleName, String> staticFieldMap;
	private Map<SimpleName, String> additionalStaticFieldMap;
	private String baseClassName;
	private Map<ICompilationUnit, CreateCompilationUnitChange> createCompilationUnitChanges;
	private TypeDeclaration contextClassTypeDecleration;
	
	public ReplaceTypeCodeWithSubclass(IFile sourceFile, CompilationUnit sourceCompilationUnit,
			TypeDeclaration sourceTypeDeclaration, TypeCheckElimination typeCheckElimination) {
		super(sourceFile, sourceCompilationUnit, sourceTypeDeclaration, typeCheckElimination);
		this.returnedVariable = typeCheckElimination.getTypeCheckMethodReturnedVariable();
		this.requiredImportDeclarationsBasedOnSignature = new LinkedHashSet<ITypeBinding>();
		this.requiredImportDeclarationsForContext = new LinkedHashSet<ITypeBinding>();
		this.thrownExceptions = typeCheckElimination.getThrownExceptions();
		this.staticFieldMap = new LinkedHashMap<SimpleName, String>();
		for(SimpleName simpleName : typeCheckElimination.getStaticFields()) {
			this.staticFieldMap.put(simpleName, generateSubclassName(simpleName));
		}
		this.additionalStaticFieldMap = new LinkedHashMap<SimpleName, String>();
		for(SimpleName simpleName : typeCheckElimination.getAdditionalStaticFields()) {
			this.additionalStaticFieldMap.put(simpleName, generateSubclassName(simpleName));
		}
		this.baseClassName = typeCheckElimination.getTypeCheckClass().getName().getIdentifier();
		this.createCompilationUnitChanges = new LinkedHashMap<ICompilationUnit, CreateCompilationUnitChange>();
		this.contextClassTypeDecleration = typeCheckElimination.getTypeCheckClass();
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
			modifyContext();
			createSubclasses();
		} finally {
			pm.done();
		}
		return status;
	}
	
	private void modifyContext() {
		ASTRewrite sourceRewriter = ASTRewrite.create(sourceTypeDeclaration.getAST());
		AST contextAST = sourceTypeDeclaration.getAST();
		makeContextAbstract(contextAST, sourceRewriter);
		changeFieldModifierToProtected(contextAST, sourceRewriter);
		
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
	
	private void makeContextAbstract(AST contextAST, ASTRewrite sourceRewriter) {
		TypeDeclaration typeDecl = this.contextClassTypeDecleration;
		MethodDeclaration methodDec = typeCheckElimination.getTypeCheckMethod();
		
		ListRewrite modifiersRewrite = sourceRewriter.getListRewrite(typeDecl, TypeDeclaration.MODIFIERS2_PROPERTY);
		modifiersRewrite.insertLast(contextAST.newModifier(Modifier.ModifierKeyword.ABSTRACT_KEYWORD), null);

		ListRewrite methodModifiersRewrite = sourceRewriter.getListRewrite(methodDec, MethodDeclaration.MODIFIERS2_PROPERTY);
		methodModifiersRewrite.insertLast(contextAST.newModifier(Modifier.ModifierKeyword.ABSTRACT_KEYWORD), null);

		sourceRewriter.set(methodDec, MethodDeclaration.BODY_PROPERTY, null, null);
		
	}
	
	// Replacing the modifiers of fields that are used in subclasses from private to protected
	private void changeFieldModifierToProtected(AST contextAST, ASTRewrite sourceRewriter) {
		TypeDeclaration typeDecl = this.contextClassTypeDecleration;
		Set<VariableDeclarationFragment> fieldsToChange = typeCheckElimination.getFieldsUsedInTypeCheckingBranches();

		for (FieldDeclaration fieldDecl : typeDecl.getFields()) {
	        for (Object obj : fieldDecl.fragments()) {
	            VariableDeclarationFragment fragment = (VariableDeclarationFragment) obj;
	            if (fieldsToChange.contains(fragment)) {
	                ListRewrite modifiersListRewrite = sourceRewriter.getListRewrite(fieldDecl, FieldDeclaration.MODIFIERS2_PROPERTY);
	                
	                Modifier privateModifier = null;
	                for (Object mod : fieldDecl.modifiers()) {
	                    if (mod instanceof Modifier && ((Modifier) mod).isPrivate()) {
	                        privateModifier = (Modifier) mod;
	                        break;
	                    }
	                }
	                
	                if (privateModifier != null) {
	                    sourceRewriter.remove(privateModifier, null);
	                }
	                
	                Modifier protectedModifier = contextAST.newModifier(Modifier.ModifierKeyword.PROTECTED_KEYWORD);
	                modifiersListRewrite.insertLast(protectedModifier, null);
	            }
	        }
	    }
	    
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
			
			createSubclassConstructor(subclassNames.get(i), subclassAST, subclassRewriter, subclassBodyRewrite, subclassCompilationUnit);
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
	
	private void createSubclassConstructor(String constructorName, AST ast, ASTRewrite rewriter, ListRewrite subclassBodyRewrite, CompilationUnit subclassCompilationUnit) {
	    MethodDeclaration baseClassConstructor = typeCheckElimination.getTypeFieldConsturctorMethod();
	    List<SingleVariableDeclaration> baseClassConstructorParams = baseClassConstructor.parameters();

	    MethodDeclaration subclassConstructor = ast.newMethodDeclaration();
	    // Set the constructor flag, name, and modifiers
	    rewriter.set(subclassConstructor, MethodDeclaration.CONSTRUCTOR_PROPERTY, true, null);
	    rewriter.set(subclassConstructor, MethodDeclaration.NAME_PROPERTY, ast.newSimpleName(constructorName), null);
	    ListRewrite modifiersRewrite = rewriter.getListRewrite(subclassConstructor, MethodDeclaration.MODIFIERS2_PROPERTY);
	    modifiersRewrite.insertLast(ast.newModifier(ModifierKeyword.PUBLIC_KEYWORD), null);

	    ListRewrite parametersRewrite = rewriter.getListRewrite(subclassConstructor, MethodDeclaration.PARAMETERS_PROPERTY);
	    for (SingleVariableDeclaration originalParam : baseClassConstructorParams) {
	        SingleVariableDeclaration newParam = (SingleVariableDeclaration) ASTNode.copySubtree(ast, originalParam);
	        parametersRewrite.insertLast(newParam, null);
	    }

	    Block constructorBody = ast.newBlock();

	    SuperConstructorInvocation superConstructorInvocation = ast.newSuperConstructorInvocation();
	    ListRewrite argumentRewrite = rewriter.getListRewrite(superConstructorInvocation, SuperConstructorInvocation.ARGUMENTS_PROPERTY);
	    for (SingleVariableDeclaration param : baseClassConstructorParams) {
	        SimpleName argumentName = (SimpleName) ASTNode.copySubtree(ast, param.getName());
	        argumentRewrite.insertLast(argumentName, null);
	    }

	    ListRewrite statementsRewrite = rewriter.getListRewrite(constructorBody, Block.STATEMENTS_PROPERTY);
	    statementsRewrite.insertFirst(superConstructorInvocation, null);

	    rewriter.set(subclassConstructor, MethodDeclaration.BODY_PROPERTY, constructorBody, null);

	    subclassBodyRewrite.insertLast(subclassConstructor, null);
	    
	    Set<ITypeBinding> requiredImportDeclarationsBasedOnBranch = getRequiredImportDeclarationsParameters((List<SingleVariableDeclaration>) baseClassConstructorParams);
		for(ITypeBinding typeBinding : requiredImportDeclarationsBasedOnBranch) {
			if(!requiredImportDeclarationsBasedOnSignature.contains(typeBinding))
				addImportDeclaration(typeBinding, subclassCompilationUnit, rewriter);
		}
	}
	
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
