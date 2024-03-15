package gr.uom.java.jdeodorant.refactoring.manipulators;

import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
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
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.Modifier;
import org.eclipse.jdt.core.dom.PackageDeclaration;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.SimpleType;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclaration;
import org.eclipse.jdt.core.dom.rewrite.ASTRewrite;
import org.eclipse.jdt.core.dom.rewrite.ListRewrite;
import org.eclipse.jdt.internal.corext.refactoring.changes.CreateCompilationUnitChange;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.ChangeDescriptor;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.eclipse.ltk.core.refactoring.RefactoringChangeDescriptor;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.text.edits.MalformedTreeException;
import org.eclipse.text.edits.TextEdit;

import gr.uom.java.ast.ASTReader;
import gr.uom.java.ast.inheritance.InheritanceTree;

public class ReplaceTypeCodeWithSubclass extends PolymorphismRefactoring {
	private VariableDeclaration returnedVariable;
	private Set<ITypeBinding> requiredImportDeclarationsBasedOnSignature;
	private Set<ITypeBinding> requiredImportDeclarationsForContext;
	private Set<ITypeBinding> thrownExceptions;
	private Map<SimpleName, String> staticFieldMap;
	private Map<SimpleName, String> additionalStaticFieldMap;
	private String baseClassName;
	private Map<ICompilationUnit, CreateCompilationUnitChange> createCompilationUnitChanges;
	
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
			if(typeCheckElimination.getTypeField() != null) {
//				modifyTypeFieldAssignmentsInContextClass(false);
//				modifyTypeFieldAccessesInContextClass(false);
			}
			else if(typeCheckElimination.getTypeLocalVariable() != null) {
//				identifyTypeLocalVariableAssignmentsInTypeCheckMethod();
//				identifyTypeLocalVariableAccessesInTypeCheckMethod();
			}
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
			createSubclasHierarchy("PanosSubclass");
//			apply();
		} finally {
			pm.done();
		}
		return status;
	}
	
	@SuppressWarnings("restriction")
	private void createSubclasHierarchy(String newClassName) {
		IContainer contextContainer = (IContainer)sourceFile.getParent();
		PackageDeclaration contextPackageDeclaration = sourceCompilationUnit.getPackage();
		IContainer rootContainer = contextContainer;
		ASTParser stateStrategyParser = ASTParser.newParser(ASTReader.JLS);
		stateStrategyParser.setKind(ASTParser.K_COMPILATION_UNIT);
		Document stateStrategyDocument = null;
		stateStrategyDocument = new Document();
		stateStrategyParser.setSource(stateStrategyDocument.get().toCharArray());
		
		InheritanceTree tree = typeCheckElimination.getInheritanceTreeMatchingWithStaticTypes();
		IFile stateStrategyFile = null;
		if(tree != null) {
			DefaultMutableTreeNode rootNode = tree.getRootNode();
			stateStrategyFile = getFile((String)rootNode.getUserObject());
		}
		else {
			if(contextContainer instanceof IProject) {
				IProject contextProject = (IProject)contextContainer;
				stateStrategyFile = contextProject.getFile(baseClassName + ".java");
			}
			else if(contextContainer instanceof IFolder) {
				IFolder contextFolder = (IFolder)contextContainer;
				stateStrategyFile = contextFolder.getFile(baseClassName + ".java");
			}
		}
		
		ICompilationUnit stateStrategyICompilationUnit = JavaCore.createCompilationUnitFrom(stateStrategyFile);
		javaElementsToOpenInEditor.add(stateStrategyICompilationUnit);
		CompilationUnit stateStrategyCompilationUnit = (CompilationUnit)stateStrategyParser.createAST(null);
        AST stateStrategyAST = stateStrategyCompilationUnit.getAST();
        ASTRewrite stateStrategyRewriter = ASTRewrite.create(stateStrategyAST);
		// Create a new TypeDeclaration (class) node
        TypeDeclaration newClassDeclaration = stateStrategyAST.newTypeDeclaration();
        
        // Set the name of the new class
        SimpleName newClassNameNode = stateStrategyAST.newSimpleName(newClassName);
        stateStrategyRewriter.set(newClassDeclaration, TypeDeclaration.NAME_PROPERTY, newClassNameNode, null);
        
        // Set the class to be public
        ListRewrite modifiersRewrite = stateStrategyRewriter.getListRewrite(newClassDeclaration, TypeDeclaration.MODIFIERS2_PROPERTY);
        modifiersRewrite.insertLast(stateStrategyAST.newModifier(Modifier.ModifierKeyword.PUBLIC_KEYWORD), null);
        
        // Set the name of the base class to extend
        SimpleType baseClassType = stateStrategyAST.newSimpleType(stateStrategyAST.newSimpleName(baseClassName));
        stateStrategyRewriter.set(newClassDeclaration, TypeDeclaration.SUPERCLASS_TYPE_PROPERTY, baseClassType, null);
        
        
        if(stateStrategyDocument != null) {
			try {
//				for(ITypeBinding typeBinding : requiredImportDeclarationsBasedOnSignature) {
//					addImportDeclaration(typeBinding, stateStrategyCompilationUnit, stateStrategyRewriter);
//				}
				TextEdit stateStrategyEdit = stateStrategyRewriter.rewriteAST(stateStrategyDocument, null);
				stateStrategyEdit.apply(stateStrategyDocument);
				CreateCompilationUnitChange createCompilationUnitChange =
					new CreateCompilationUnitChange(stateStrategyICompilationUnit, stateStrategyDocument.get(), stateStrategyFile.getCharset());
				createCompilationUnitChanges.put(stateStrategyICompilationUnit, createCompilationUnitChange);
			} catch (CoreException e) {
				e.printStackTrace();
			} catch (MalformedTreeException e) {
				e.printStackTrace();
			} catch (BadLocationException e) {
				e.printStackTrace();
			}
		}
        
        // Assuming there is a way to insert this newClassDeclaration into your AST
        // For example, adding this class declaration to the list of types in a CompilationUnit
        // (This part depends on the context of how you're using the AST and ASTRewriter)
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
