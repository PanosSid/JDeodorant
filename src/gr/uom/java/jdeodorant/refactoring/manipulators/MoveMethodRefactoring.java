package gr.uom.java.jdeodorant.refactoring.manipulators;

import gr.uom.java.ast.util.ExpressionExtractor;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.filebuffers.FileBuffers;
import org.eclipse.core.filebuffers.ITextFileBuffer;
import org.eclipse.core.filebuffers.ITextFileBufferManager;
import org.eclipse.core.filebuffers.LocationKind;
import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.Block;
import org.eclipse.jdt.core.dom.ClassInstanceCreation;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.FieldAccess;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.ImportDeclaration;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.Modifier;
import org.eclipse.jdt.core.dom.PackageDeclaration;
import org.eclipse.jdt.core.dom.QualifiedName;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.Statement;
import org.eclipse.jdt.core.dom.Type;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.eclipse.jdt.core.dom.rewrite.ASTRewrite;
import org.eclipse.jdt.core.dom.rewrite.ListRewrite;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.text.edits.MalformedTreeException;
import org.eclipse.text.edits.TextEdit;
import org.eclipse.text.edits.UndoEdit;

public class MoveMethodRefactoring {
	private IFile sourceFile;
	private IFile targetFile;
	private CompilationUnit sourceCompilationUnit;
	private CompilationUnit targetCompilationUnit;
	private TypeDeclaration sourceTypeDeclaration;
	private TypeDeclaration targetTypeDeclaration;
	private MethodDeclaration sourceMethod;
	private ASTRewrite sourceRewriter;
	private ASTRewrite targetRewriter;
	private Map<IDocument, UndoEdit> undoEditMap;
	private Map<IFile, IDocument> documentMap;
	private Set<ITypeBinding> requiredTargetImportDeclarationSet;
	private List<String> targetClassVariableNames;
	
	public MoveMethodRefactoring(IFile sourceFile, IFile targetFile, CompilationUnit sourceCompilationUnit, CompilationUnit targetCompilationUnit, 
			TypeDeclaration sourceTypeDeclaration, TypeDeclaration targetTypeDeclaration, MethodDeclaration sourceMethod) {
		this.sourceFile = sourceFile;
		this.targetFile = targetFile;
		this.sourceCompilationUnit = sourceCompilationUnit;
		this.targetCompilationUnit = targetCompilationUnit;
		this.sourceTypeDeclaration = sourceTypeDeclaration;
		this.targetTypeDeclaration = targetTypeDeclaration;
		this.sourceMethod = sourceMethod;
		this.undoEditMap = new LinkedHashMap<IDocument, UndoEdit>();
		this.documentMap = new LinkedHashMap<IFile, IDocument>();
		this.requiredTargetImportDeclarationSet = new LinkedHashSet<ITypeBinding>();
		this.targetRewriter = ASTRewrite.create(targetCompilationUnit.getAST());
		this.targetClassVariableNames = getTargetClassVariableNames();
	}

	public Map<IDocument, UndoEdit> getUndoEditMap() {
		return this.undoEditMap;
	}
	
	public IDocument getDocument(IFile file) {
		return documentMap.get(file);
	}
	
	private List<String> getTargetClassVariableNames() {
		List<SingleVariableDeclaration> sourceMethodParameters = sourceMethod.parameters();
		
		List<String> targetClassVariableNames = new ArrayList<String>();
		for(SingleVariableDeclaration parameter : sourceMethodParameters) {
			ITypeBinding parameterTypeBinding = parameter.getType().resolveBinding();
			if(parameterTypeBinding.getQualifiedName().equals(targetTypeDeclaration.resolveBinding().getQualifiedName())){
				targetClassVariableNames.add(parameter.getName().getIdentifier());
			}
		}
		if(targetClassVariableNames.isEmpty()) {
			FieldDeclaration[] fields = sourceTypeDeclaration.getFields();
			for(FieldDeclaration field : fields) {
				ITypeBinding fieldTypeBinding = field.getType().resolveBinding();
				List<VariableDeclarationFragment> fragments = field.fragments();
				for(VariableDeclarationFragment fragment : fragments){
					if(fieldTypeBinding.getQualifiedName().equals(targetTypeDeclaration.resolveBinding().getQualifiedName())){
						targetClassVariableNames.add(fragment.getName().getIdentifier());
					}
				}
			}
		}
		return targetClassVariableNames;
	}
	
	public void apply() {
		addRequiredTargetImportDeclarations();
		createMovedMethod();
		ITextFileBufferManager bufferManager = FileBuffers.getTextFileBufferManager();
		ITextFileBuffer targetTextFileBuffer = bufferManager.getTextFileBuffer(targetFile.getFullPath(), LocationKind.IFILE);
		IDocument targetDocument = targetTextFileBuffer.getDocument();
		TextEdit targetEdit = targetRewriter.rewriteAST(targetDocument, null);
		try {
			UndoEdit undoEdit = targetEdit.apply(targetDocument, UndoEdit.CREATE_UNDO);
			undoEditMap.put(targetDocument, undoEdit);
			documentMap.put(targetFile, targetDocument);
		} catch (MalformedTreeException e) {
			e.printStackTrace();
		} catch (BadLocationException e) {
			e.printStackTrace();
		}
		
		removeSourceMethod();
		modifyMovedMethodInvocationInSourceClass();
		ITextFileBuffer sourceTextFileBuffer = bufferManager.getTextFileBuffer(sourceFile.getFullPath(), LocationKind.IFILE);
		IDocument sourceDocument = sourceTextFileBuffer.getDocument();
		TextEdit sourceEdit = sourceRewriter.rewriteAST(sourceDocument, null);
		try {
			UndoEdit undoEdit = sourceEdit.apply(sourceDocument, UndoEdit.CREATE_UNDO);
			undoEditMap.put(sourceDocument, undoEdit);
			documentMap.put(sourceFile, sourceDocument);
		} catch (MalformedTreeException e) {
			e.printStackTrace();
		} catch (BadLocationException e) {
			e.printStackTrace();
		}
	}

	private void addRequiredTargetImportDeclarations() {
		List<ITypeBinding> typeBindings = new ArrayList<ITypeBinding>();
		Type returnType = sourceMethod.getReturnType2();
		ITypeBinding returnTypeBinding = returnType.resolveBinding();
		if(!typeBindings.contains(returnTypeBinding))
			typeBindings.add(returnTypeBinding);
		
		List<SingleVariableDeclaration> parameters = sourceMethod.parameters();
		for(SingleVariableDeclaration parameter : parameters) {
			Type parameterType = parameter.getType();
			ITypeBinding parameterTypeBinding = parameterType.resolveBinding();
			if(!typeBindings.contains(parameterTypeBinding))
				typeBindings.add(parameterTypeBinding);			
		}
		
		ExpressionExtractor expressionExtractor = new ExpressionExtractor();
		List<Expression> variableInstructions = expressionExtractor.getVariableInstructions(sourceMethod.getBody());
		for(Expression variableInstruction : variableInstructions) {
			SimpleName simpleName = (SimpleName)variableInstruction;
			IBinding binding = simpleName.resolveBinding();
			if(binding.getKind() == IBinding.VARIABLE) {
				IVariableBinding variableBinding = (IVariableBinding)binding;
				ITypeBinding variableTypeBinding = variableBinding.getType();
				if(!typeBindings.contains(variableTypeBinding))
					typeBindings.add(variableTypeBinding);
				ITypeBinding declaringClassTypeBinding = variableBinding.getDeclaringClass();
				if(declaringClassTypeBinding != null && !typeBindings.contains(declaringClassTypeBinding) && !targetClassVariableNames.contains(simpleName.getIdentifier()))
					typeBindings.add(declaringClassTypeBinding);
			}
		}
		
		List<Expression> methodInvocations = expressionExtractor.getMethodInvocations(sourceMethod.getBody());
		for(Expression expression : methodInvocations) {
			if(expression instanceof MethodInvocation) {
				MethodInvocation methodInvocation = (MethodInvocation)expression;
				IMethodBinding methodBinding = methodInvocation.resolveMethodBinding();
				ITypeBinding declaringClassTypeBinding = methodBinding.getDeclaringClass();
				if(declaringClassTypeBinding != null && !typeBindings.contains(declaringClassTypeBinding))
					typeBindings.add(declaringClassTypeBinding);
			}
		}
		
		List<Expression> classInstanceCreations = expressionExtractor.getClassInstanceCreations(sourceMethod.getBody());
		for(Expression expression : classInstanceCreations) {
			ClassInstanceCreation classInstanceCreation = (ClassInstanceCreation)expression;
			Type classInstanceCreationType = classInstanceCreation.getType();
			ITypeBinding classInstanceCreationTypeBinding = classInstanceCreationType.resolveBinding();
			if(!typeBindings.contains(classInstanceCreationTypeBinding))
				typeBindings.add(classInstanceCreationTypeBinding);
		}
		getSimpleTypeBindings(typeBindings);
		for(ITypeBinding typeBinding : requiredTargetImportDeclarationSet)
			addImportDeclaration(typeBinding);
	}

	private void getSimpleTypeBindings(List<ITypeBinding> typeBindings) {
		for(ITypeBinding typeBinding : typeBindings) {
			if(typeBinding.isPrimitive()) {
				
			}
			else if(typeBinding.isArray()) {
				ITypeBinding elementTypeBinding = typeBinding.getElementType();
				List<ITypeBinding> typeBindingList = new ArrayList<ITypeBinding>();
				typeBindingList.add(elementTypeBinding);
				getSimpleTypeBindings(typeBindingList);
			}
			else if(typeBinding.isParameterizedType()) {
				List<ITypeBinding> typeBindingList = new ArrayList<ITypeBinding>();
				typeBindingList.add(typeBinding.getTypeDeclaration());
				ITypeBinding[] typeArgumentBindings = typeBinding.getTypeArguments();
				for(ITypeBinding typeArgumentBinding : typeArgumentBindings)
					typeBindingList.add(typeArgumentBinding);
				getSimpleTypeBindings(typeBindingList);
			}
			else if(typeBinding.isWildcardType()) {
				List<ITypeBinding> typeBindingList = new ArrayList<ITypeBinding>();
				typeBindingList.add(typeBinding.getBound());
				getSimpleTypeBindings(typeBindingList);
			}
			else {
				requiredTargetImportDeclarationSet.add(typeBinding);
			}
		}
	}

	private void addImportDeclaration(ITypeBinding typeBinding) {
		String qualifiedName = typeBinding.getQualifiedName();
		String qualifiedPackageName = "";
		if(qualifiedName.contains("."))
			qualifiedPackageName = qualifiedName.substring(0,qualifiedName.lastIndexOf("."));
		PackageDeclaration targetPackageDeclaration = targetCompilationUnit.getPackage();
		String targetPackageDeclarationName = "";
		if(targetPackageDeclaration != null)
			targetPackageDeclarationName = targetPackageDeclaration.getName().getFullyQualifiedName();	
		if(!qualifiedPackageName.equals("") && !qualifiedPackageName.equals("java.lang") && !qualifiedPackageName.equals(targetPackageDeclarationName)) {
			List<ImportDeclaration> importDeclarationList = targetCompilationUnit.imports();
			boolean found = false;
			for(ImportDeclaration importDeclaration : importDeclarationList) {
				if(!importDeclaration.isOnDemand()) {
					if(qualifiedName.equals(importDeclaration.getName().getFullyQualifiedName())) {
						found = true;
						break;
					}
				}
				else {
					if(qualifiedPackageName.equals(importDeclaration.getName().getFullyQualifiedName())) {
						found = true;
						break;
					}
				}
			}
			if(!found) {
				AST ast = targetCompilationUnit.getAST();
				ImportDeclaration importDeclaration = ast.newImportDeclaration();
				targetRewriter.set(importDeclaration, ImportDeclaration.NAME_PROPERTY, ast.newName(qualifiedName), null);
				ListRewrite importRewrite = targetRewriter.getListRewrite(targetCompilationUnit, CompilationUnit.IMPORTS_PROPERTY);
				importRewrite.insertLast(importDeclaration, null);
			}
		}
	}

	private void createMovedMethod() {
		AST ast = targetTypeDeclaration.getAST();
		MethodDeclaration newMethodDeclaration = (MethodDeclaration)ASTNode.copySubtree(ast, sourceMethod);
		
		ListRewrite modifierRewrite = targetRewriter.getListRewrite(newMethodDeclaration, MethodDeclaration.MODIFIERS2_PROPERTY);
		Modifier publicModifier = newMethodDeclaration.getAST().newModifier(Modifier.ModifierKeyword.PUBLIC_KEYWORD);
		boolean modifierFound = false;
		List<Modifier> modifiers = newMethodDeclaration.modifiers();
		for(Modifier modifier : modifiers){
			if(modifier.getKeyword().equals(Modifier.ModifierKeyword.PUBLIC_KEYWORD)){
				modifierFound = true;
			}
			else if(modifier.getKeyword().equals(Modifier.ModifierKeyword.PRIVATE_KEYWORD) ||
					modifier.getKeyword().equals(Modifier.ModifierKeyword.PROTECTED_KEYWORD)){
				modifierFound = true;
				modifierRewrite.replace(modifier, publicModifier, null);
			}
		}
		if(!modifierFound){
			modifierRewrite.insertFirst(publicModifier, null);
		}
		
		ListRewrite parametersRewrite = targetRewriter.getListRewrite(newMethodDeclaration, MethodDeclaration.PARAMETERS_PROPERTY);
		List<SingleVariableDeclaration> sourceMethodParameters = sourceMethod.parameters();
		List<SingleVariableDeclaration> newMethodParameters = newMethodDeclaration.parameters();
		
		int i = 0;
		for(SingleVariableDeclaration parameter : sourceMethodParameters) {
			ITypeBinding parameterTypeBinding = parameter.getType().resolveBinding();
			if(parameterTypeBinding.getQualifiedName().equals(targetTypeDeclaration.resolveBinding().getQualifiedName())){
				parametersRewrite.remove(newMethodParameters.get(i), null);
			}
			i++;
		}
		
		modifySourceMethodInvocationsInTargetClass(newMethodDeclaration);

		List<Statement> oldMethodStatements = newMethodDeclaration.getBody().statements();
		for(Statement statement : oldMethodStatements){
			modifyTargetMethodInvocations(statement, targetClassVariableNames);
			modifyTargetPublicFieldInstructions(statement, targetClassVariableNames);
			modifyTargetStaticFieldInstructions(statement);
		}
		
		ListRewrite methodDeclarationRewrite = targetRewriter.getListRewrite(targetTypeDeclaration, TypeDeclaration.BODY_DECLARATIONS_PROPERTY);
		methodDeclarationRewrite.insertLast(newMethodDeclaration, null);
	}

	private void removeSourceMethod() {
		if(sourceRewriter == null) {
			AST ast = sourceTypeDeclaration.getAST();
			sourceRewriter = ASTRewrite.create(ast);
		}
		ListRewrite bodyRewrite = sourceRewriter.getListRewrite(sourceTypeDeclaration, TypeDeclaration.BODY_DECLARATIONS_PROPERTY);
		bodyRewrite.remove(sourceMethod, null);
	}

	private void modifyMovedMethodInvocationInSourceClass() {
		ExpressionExtractor expressionExtractor = new ExpressionExtractor();
		MethodDeclaration[] methodDeclarations = sourceTypeDeclaration.getMethods();
    	for(MethodDeclaration methodDeclaration : methodDeclarations) {
    		Block methodBody = methodDeclaration.getBody();
    		List<Statement> statements = methodBody.statements();
    		for(Statement statement : statements) {
    			List<Expression> methodInvocations = expressionExtractor.getMethodInvocations(statement);
    			for(Expression expression : methodInvocations) {
    				if(expression instanceof MethodInvocation) {
    					MethodInvocation methodInvocation = (MethodInvocation)expression;
    					if(identicalSignatureWithSourceMethod(methodInvocation)) {
    						List<Expression> arguments = methodInvocation.arguments();
    						boolean foundInArguments = false;
    						for(Expression argument : arguments) {
    							if(argument.resolveTypeBinding().getQualifiedName().equals(targetTypeDeclaration.resolveBinding().getQualifiedName())) {
    								foundInArguments = true;
    								ListRewrite argumentRewrite = sourceRewriter.getListRewrite(methodInvocation, MethodInvocation.ARGUMENTS_PROPERTY);
    								argumentRewrite.remove(argument, null);
    								sourceRewriter.set(methodInvocation, MethodInvocation.EXPRESSION_PROPERTY, argument, null);
    							}
    						}
    						if(!foundInArguments) {
    							//we suppose that there is only one FieldDeclaration (with only one fragment) matching the Type of the TargetClass
    							FieldDeclaration[] fieldDeclarations = sourceTypeDeclaration.getFields();
    				        	for(FieldDeclaration fieldDeclaration : fieldDeclarations) {
    				        		if(fieldDeclaration.getType().resolveBinding().getQualifiedName().equals(targetTypeDeclaration.resolveBinding().getQualifiedName())) {
    				        			VariableDeclarationFragment fragment = (VariableDeclarationFragment)fieldDeclaration.fragments().get(0);
    				        			sourceRewriter.set(methodInvocation, MethodInvocation.EXPRESSION_PROPERTY, fragment.getName(), null);
    				        		}
    				        	}
    						}
    					}
    				}
    			}
    		}
    	}
	}

	private boolean identicalSignatureWithSourceMethod(MethodInvocation methodInvocation) {
		if(!methodInvocation.getName().getIdentifier().equals(sourceMethod.getName().getIdentifier()))
			return false;
		List<SingleVariableDeclaration> parameters = sourceMethod.parameters();
		List<Expression> arguments = methodInvocation.arguments();
		if(arguments.size() != parameters.size()) {
			return false;
		}
		else {
			for(int i=0; i<arguments.size(); i++) {
				SingleVariableDeclaration parameter = parameters.get(i);
				Expression argument = arguments.get(i);
				ITypeBinding argumentTypeBinding = argument.resolveTypeBinding();
				ITypeBinding parameterTypeBinding = parameter.getType().resolveBinding();
				if(!argumentTypeBinding.getQualifiedName().equals(parameterTypeBinding.getQualifiedName()))
					return false;
			}
		}
		
		return true;
	}

	private void modifyTargetMethodInvocations(Statement statement, List<String> targetClassVariableNames) {
		ExpressionExtractor extractor = new ExpressionExtractor();
		List<Expression> methodInvocations = extractor.getMethodInvocations(statement);
		for(Expression expression : methodInvocations) {
			if(expression instanceof MethodInvocation) {
				MethodInvocation methodInvocation = (MethodInvocation)expression;
				Expression methodInvocationExpression = methodInvocation.getExpression();
				if(methodInvocationExpression instanceof SimpleName){
					SimpleName methodInvocationExpressionSimpleName = (SimpleName)methodInvocationExpression;
					if(targetClassVariableNames.contains(methodInvocationExpressionSimpleName.getIdentifier())){
						targetRewriter.remove(methodInvocationExpressionSimpleName, null);
					}
				}
			}
		}
	}

	private void modifyTargetPublicFieldInstructions(Statement statement, List<String> targetClassVariableNames) {
		ExpressionExtractor extractor = new ExpressionExtractor();
		List<Expression> variableInstructions = extractor.getVariableInstructions(statement);
		FieldDeclaration[] fields = targetTypeDeclaration.getFields();
		for(FieldDeclaration field : fields) {
			List<VariableDeclarationFragment> fragments = field.fragments();
			for(VariableDeclarationFragment fragment : fragments) {
				SimpleName fragmentName = fragment.getName();
				for(Expression expression : variableInstructions) {
					SimpleName simpleName = (SimpleName)expression;
					if(simpleName.getParent() instanceof QualifiedName && fragmentName.getIdentifier().equals(simpleName.getIdentifier())) {
						QualifiedName qualifiedName = (QualifiedName)simpleName.getParent();
						if(targetClassVariableNames.contains(qualifiedName.getQualifier().getFullyQualifiedName())) {
							targetRewriter.replace(qualifiedName, simpleName, null);
						}
					}
				}
			}
		}
	}
	
	private void modifyTargetStaticFieldInstructions(Statement statement) {
		ExpressionExtractor extractor = new ExpressionExtractor();
		List<Expression> variableInstructions = extractor.getVariableInstructions(statement);
		FieldDeclaration[] fields = sourceTypeDeclaration.getFields();
		AST ast = statement.getAST();
		for(FieldDeclaration field : fields) {
			if((field.getModifiers() & Modifier.STATIC) != 0){
				List<VariableDeclarationFragment> fragments = field.fragments();
				for(VariableDeclarationFragment fragment : fragments) {
					SimpleName fragmentName = fragment.getName();
					for(Expression expression : variableInstructions) {
						SimpleName expressionName = (SimpleName)expression;
						if(!(expressionName.getParent() instanceof QualifiedName) && fragmentName.getIdentifier().equals(expressionName.getIdentifier())){
							SimpleName newSimpleName = ast.newSimpleName(expressionName.getIdentifier());
							SimpleName qualifier = ast.newSimpleName(sourceTypeDeclaration.getName().getIdentifier());
							QualifiedName newQualifiedName = ast.newQualifiedName(qualifier, newSimpleName);
							targetRewriter.replace(expressionName, newQualifiedName, null);
						}
					}
				}
			}
		}
	}
	
	private void modifySourceMethodInvocationsInTargetClass(MethodDeclaration newMethodDeclaration) {
		ExpressionExtractor extractor = new ExpressionExtractor();	
		List<Expression> sourceMethodInvocations = extractor.getMethodInvocations(sourceMethod.getBody());
		List<Expression> newMethodInvocations = extractor.getMethodInvocations(newMethodDeclaration.getBody());
		List<Expression> sourceFieldInstructions = extractor.getVariableInstructions(sourceMethod.getBody());
		List<Expression> newFieldInstructions = extractor.getVariableInstructions(newMethodDeclaration.getBody());
		SimpleName parameterName = null;
		int numberOfOccurences = 0;
		int i = 0;
		for(Expression expression : sourceMethodInvocations) {
			if(expression instanceof MethodInvocation) {
				MethodInvocation methodInvocation = (MethodInvocation)expression;
				IMethodBinding methodBinding = methodInvocation.resolveMethodBinding();
				if(methodBinding.getDeclaringClass().equals(sourceTypeDeclaration.resolveBinding())) {
					numberOfOccurences++;
					if(numberOfOccurences == 1) {
						parameterName = addSourceClassParameter(newMethodDeclaration);
					}
					MethodInvocation newMethodInvocation = (MethodInvocation)newMethodInvocations.get(i);
					targetRewriter.set(newMethodInvocation, MethodInvocation.EXPRESSION_PROPERTY, parameterName, null);
				}
			}
			i++;
		}
		int j = 0;
		for(Expression expression : sourceFieldInstructions) {
			SimpleName simpleName = (SimpleName)expression;
			IBinding binding = simpleName.resolveBinding();
			if(binding.getKind() == IBinding.VARIABLE) {
				IVariableBinding variableBinding = (IVariableBinding)binding;
				if(variableBinding.isField() && variableBinding.getDeclaringClass().equals(sourceTypeDeclaration.resolveBinding()) && (variableBinding.getModifiers() & Modifier.STATIC) == 0) {
					numberOfOccurences++;
					if(numberOfOccurences == 1) {
						parameterName = addSourceClassParameter(newMethodDeclaration);
					}
					SimpleName expressionName = (SimpleName)newFieldInstructions.get(j);
					AST ast = newMethodDeclaration.getAST();
					if(expressionName.getParent() instanceof FieldAccess) {
						SimpleName qualifier = ast.newSimpleName(parameterName.getIdentifier());
						targetRewriter.set(expressionName.getParent(), FieldAccess.EXPRESSION_PROPERTY, qualifier, null);
					}
					else {
						SimpleName newSimpleName = ast.newSimpleName(expressionName.getIdentifier());
						SimpleName qualifier = ast.newSimpleName(parameterName.getIdentifier());
						QualifiedName newQualifiedName = ast.newQualifiedName(qualifier, newSimpleName);
						targetRewriter.replace(expressionName, newQualifiedName, null);
					}
				}
			}
			j++;
		}
	}

	private SimpleName addSourceClassParameter(MethodDeclaration newMethodDeclaration) {
		AST ast = newMethodDeclaration.getAST();
		SingleVariableDeclaration parameter = ast.newSingleVariableDeclaration();
		SimpleName typeName = ast.newSimpleName(sourceTypeDeclaration.getName().getIdentifier());
		Type parameterType = ast.newSimpleType(typeName);
		targetRewriter.set(parameter, SingleVariableDeclaration.TYPE_PROPERTY, parameterType, null);
		String sourceTypeName = sourceTypeDeclaration.getName().getIdentifier();
		SimpleName parameterName = ast.newSimpleName(sourceTypeName.replace(sourceTypeName.charAt(0), Character.toLowerCase(sourceTypeName.charAt(0))));
		targetRewriter.set(parameter, SingleVariableDeclaration.NAME_PROPERTY, parameterName, null);
		ListRewrite parametersRewrite = targetRewriter.getListRewrite(newMethodDeclaration, MethodDeclaration.PARAMETERS_PROPERTY);
		parametersRewrite.insertLast(parameter, null);
		return parameterName;
	}
}