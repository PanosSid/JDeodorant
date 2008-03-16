package gr.uom.java.jdeodorant.refactoring.manipulators;

import gr.uom.java.ast.inheritance.InheritanceTree;
import gr.uom.java.ast.util.ExpressionExtractor;
import gr.uom.java.ast.util.MethodDeclarationUtility;
import gr.uom.java.ast.util.StatementExtractor;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.StringTokenizer;

import javax.swing.tree.DefaultMutableTreeNode;

import org.eclipse.jdt.core.dom.Block;
import org.eclipse.jdt.core.dom.BreakStatement;
import org.eclipse.jdt.core.dom.CastExpression;
import org.eclipse.jdt.core.dom.CatchClause;
import org.eclipse.jdt.core.dom.ClassInstanceCreation;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.FieldAccess;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.ReturnStatement;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.Statement;
import org.eclipse.jdt.core.dom.SwitchCase;
import org.eclipse.jdt.core.dom.SwitchStatement;
import org.eclipse.jdt.core.dom.TryStatement;
import org.eclipse.jdt.core.dom.Type;
import org.eclipse.jdt.core.dom.VariableDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.eclipse.jdt.core.dom.VariableDeclarationStatement;

public class TypeCheckElimination {
	private Map<Expression, ArrayList<Statement>> typeCheckMap;
	private ArrayList<Statement> defaultCaseStatements;
	private Map<Expression, SimpleName> staticFieldMap;
	private Map<Expression, Type> subclassTypeMap;
	private VariableDeclarationFragment typeField;
	private MethodDeclaration typeFieldGetterMethod;
	private MethodDeclaration typeFieldSetterMethod;
	private Statement typeCheckCodeFragment;
	private MethodDeclaration typeCheckMethod;
	private LinkedHashSet<VariableDeclarationFragment> accessedFields;
	private LinkedHashSet<VariableDeclarationFragment> assignedFields;
	private LinkedHashSet<SingleVariableDeclaration> accessedParameters;
	private LinkedHashSet<VariableDeclarationFragment> accessedLocalVariables;
	private LinkedHashSet<MethodDeclaration> accessedMethods;
	private SimpleName typeLocalVariable;
	private InheritanceTree existingInheritanceTree;
	private InheritanceTree inheritanceTreeMatchingWithStaticTypes;
	private Map<Expression, DefaultMutableTreeNode> remainingIfStatementExpressionMap;
	
	public TypeCheckElimination() {
		this.typeCheckMap = new LinkedHashMap<Expression, ArrayList<Statement>>();
		this.defaultCaseStatements = new ArrayList<Statement>();
		this.staticFieldMap = new LinkedHashMap<Expression, SimpleName>();
		this.subclassTypeMap = new LinkedHashMap<Expression, Type>();
		this.typeField = null;
		this.typeFieldGetterMethod = null;
		this.typeFieldSetterMethod = null;
		this.typeCheckCodeFragment = null;
		this.typeCheckMethod = null;
		this.accessedFields = new LinkedHashSet<VariableDeclarationFragment>();
		this.assignedFields = new LinkedHashSet<VariableDeclarationFragment>();
		this.accessedParameters = new LinkedHashSet<SingleVariableDeclaration>();
		this.accessedLocalVariables = new LinkedHashSet<VariableDeclarationFragment>();
		this.accessedMethods = new LinkedHashSet<MethodDeclaration>();
		this.typeLocalVariable = null;
		this.existingInheritanceTree = null;
		this.remainingIfStatementExpressionMap = new LinkedHashMap<Expression, DefaultMutableTreeNode>();
	}
	
	public void addTypeCheck(Expression expression, Statement statement) {
		if(typeCheckMap.containsKey(expression)) {
			ArrayList<Statement> statements = typeCheckMap.get(expression);
			statements.add(statement);
		}
		else {
			ArrayList<Statement> statements = new ArrayList<Statement>();
			statements.add(statement);
			typeCheckMap.put(expression, statements);
		}
	}
	
	public void addDefaultCaseStatement(Statement statement) {
		defaultCaseStatements.add(statement);
	}
	
	public void addStaticType(Expression expression, SimpleName simpleName) {
		staticFieldMap.put(expression, simpleName);
	}
	
	public void addSubclassType(Expression expression, Type subclassType) {
		subclassTypeMap.put(expression, subclassType);
	}
	
	public void addRemainingIfStatementExpression(Expression expression, DefaultMutableTreeNode root) {
		remainingIfStatementExpressionMap.put(expression, root);
	}
	
	public void addAccessedField(VariableDeclarationFragment fragment) {
		accessedFields.add(fragment);
	}
	
	public void addAssignedField(VariableDeclarationFragment fragment) {
		assignedFields.add(fragment);
	}
	
	public void addAccessedLocalVariable(VariableDeclarationFragment fragment){
		accessedLocalVariables.add(fragment);
	}
	
	public void addAccessedParameter(SingleVariableDeclaration parameter) {
		accessedParameters.add(parameter);
	}
	
	public void addAccessedMethod(MethodDeclaration method) {
		accessedMethods.add(method);
	}
	
	public LinkedHashSet<VariableDeclarationFragment> getAccessedLocalVariables() {
		return accessedLocalVariables;
	}

	public Set<VariableDeclarationFragment> getAccessedFields() {
		return accessedFields;
	}
	
	public Set<VariableDeclarationFragment> getAssignedFields() {
		return assignedFields;
	}
	
	public Set<SingleVariableDeclaration> getAccessedParameters() {
		return accessedParameters;
	}
	
	public Set<MethodDeclaration> getAccessedMethods() {
		return accessedMethods;
	}
	
	public Set<Expression> getTypeCheckExpressions() {
		return typeCheckMap.keySet();
	}
	
	public List<ArrayList<Statement>> getTypeCheckStatements() {
		return new ArrayList<ArrayList<Statement>>(typeCheckMap.values());
	}
	
	public ArrayList<Statement> getDefaultCaseStatements() {
		return defaultCaseStatements;
	}
	
	public List<SimpleName> getStaticFields() {
		ArrayList<SimpleName> staticFields = new ArrayList<SimpleName>();
		for(Expression expression : typeCheckMap.keySet()) {
			SimpleName simpleName = staticFieldMap.get(expression);
			staticFields.add(simpleName);
		}
		return staticFields;
	}
	
	public DefaultMutableTreeNode getRemainingIfStatementExpression(Expression expression) {
		return remainingIfStatementExpressionMap.get(expression);
	}
	
	public Expression getExpressionCorrespondingToTypeCheckStatementList(ArrayList<Statement> statements) {
		for(Expression expression : typeCheckMap.keySet()) {
			if(statements.equals(typeCheckMap.get(expression)))
				return expression;
		}
		return null;
	}
	
	public List<String> getStaticFieldNames() {
		List<String> staticFieldNames = new ArrayList<String>();
		for(Expression expression : typeCheckMap.keySet()) {
			SimpleName simpleName = staticFieldMap.get(expression);
			staticFieldNames.add(simpleName.getIdentifier());
		}
		return staticFieldNames;
	}
	
	public VariableDeclarationFragment getTypeField() {
		return typeField;
	}
	
	public void setTypeField(VariableDeclarationFragment typeField) {
		this.typeField = typeField;
	}
	
	public MethodDeclaration getTypeFieldGetterMethod() {
		return typeFieldGetterMethod;
	}

	public void setTypeFieldGetterMethod(MethodDeclaration typeFieldGetterMethod) {
		this.typeFieldGetterMethod = typeFieldGetterMethod;
	}

	public MethodDeclaration getTypeFieldSetterMethod() {
		return typeFieldSetterMethod;
	}

	public void setTypeFieldSetterMethod(MethodDeclaration typeFieldSetterMethod) {
		this.typeFieldSetterMethod = typeFieldSetterMethod;
	}

	public Statement getTypeCheckCodeFragment() {
		return typeCheckCodeFragment;
	}

	public void setTypeCheckCodeFragment(Statement typeCheckCodeFragment) {
		this.typeCheckCodeFragment = typeCheckCodeFragment;
	}

	public MethodDeclaration getTypeCheckMethod() {
		return typeCheckMethod;
	}

	public void setTypeCheckMethod(MethodDeclaration typeCheckMethod) {
		this.typeCheckMethod = typeCheckMethod;
	}

	public SimpleName getTypeLocalVariable() {
		return typeLocalVariable;
	}

	public void setTypeLocalVariable(SimpleName typeLocalVariable) {
		this.typeLocalVariable = typeLocalVariable;
	}

	public InheritanceTree getExistingInheritanceTree() {
		return existingInheritanceTree;
	}

	public void setExistingInheritanceTree(InheritanceTree existingInheritanceTree) {
		this.existingInheritanceTree = existingInheritanceTree;
	}

	public InheritanceTree getInheritanceTreeMatchingWithStaticTypes() {
		return inheritanceTreeMatchingWithStaticTypes;
	}

	public void setInheritanceTreeMatchingWithStaticTypes(InheritanceTree inheritanceTree) {
		this.inheritanceTreeMatchingWithStaticTypes = inheritanceTree;
	}

	public boolean allTypeCheckingsContainStaticFieldOrSubclassType() {
		return (typeCheckMap.keySet().size() > 1) && 
			(typeCheckMap.keySet().size() == (staticFieldMap.keySet().size() + subclassTypeMap.keySet().size()));
	}
	
	public boolean isSuperClassTypeInterfaceOrObject() {
		if(typeField != null) {
			ITypeBinding typeFieldTypeBinding = typeField.resolveBinding().getType();
			if(typeFieldTypeBinding.isInterface() || typeFieldTypeBinding.getQualifiedName().equals("java.lang.Object"))
				return true;
		}
		else if(typeLocalVariable != null) {
			ITypeBinding typeLocalVariableTypeBinding = typeLocalVariable.resolveTypeBinding();
			if(typeLocalVariableTypeBinding.isInterface() || typeLocalVariableTypeBinding.getQualifiedName().equals("java.lang.Object"))
				return true;
		}
		return false;
	}
	
	public Type getTypeCheckMethodReturnType() {
		return typeCheckMethod.getReturnType2();
	}
	
	public String getTypeCheckMethodName() {
		return typeCheckMethod.getName().getIdentifier();
	}
	
	public List<SingleVariableDeclaration> getTypeCheckMethodParameters() {
		return typeCheckMethod.parameters();
	}
	
	public VariableDeclaration getTypeCheckMethodReturnedVariable() {
		StatementExtractor statementExtractor = new StatementExtractor();
		List<Statement> returnStatements = statementExtractor.getReturnStatements(typeCheckMethod.getBody());
		if(returnStatements.size() > 0) {
			ReturnStatement lastReturnStatement = (ReturnStatement)returnStatements.get(returnStatements.size()-1);
			if(lastReturnStatement.getExpression() instanceof SimpleName) {
				SimpleName returnExpression = (SimpleName)lastReturnStatement.getExpression();
				List<SingleVariableDeclaration> parameters = typeCheckMethod.parameters();
				for(SingleVariableDeclaration parameter : parameters) {
					if(parameter.resolveBinding().isEqualTo(returnExpression.resolveBinding()))
						return parameter;
				}
				List<Statement> variableDeclarationStatements = statementExtractor.getVariableDeclarations(typeCheckMethod.getBody());
				for(Statement statement : variableDeclarationStatements) {
					VariableDeclarationStatement variableDeclarationStatement = (VariableDeclarationStatement)statement;
					List<VariableDeclarationFragment> fragments = variableDeclarationStatement.fragments();
					for(VariableDeclarationFragment fragment : fragments) {
						if(fragment.resolveBinding().isEqualTo(returnExpression.resolveBinding()))
							return fragment;
					}
				}
			}
		}
		return null;
	}
	
	public String getAbstractClassName() {
		if(typeField != null && existingInheritanceTree == null) {
			String typeFieldName = typeField.getName().getIdentifier().replaceAll("_", "");
			return typeFieldName.substring(0, 1).toUpperCase() + typeFieldName.substring(1, typeFieldName.length());
		}
		else if(typeLocalVariable != null && existingInheritanceTree == null) {
			String typeLocalVariableName = typeLocalVariable.getIdentifier().replaceAll("_", "");
			return typeLocalVariableName.substring(0, 1).toUpperCase() + typeLocalVariableName.substring(1, typeLocalVariableName.length());
		}
		else if(existingInheritanceTree != null) {
			DefaultMutableTreeNode root = existingInheritanceTree.getRootNode();
			return (String)root.getUserObject();
		}
		return null;
	}
	
	public List<String> getSubclassNames() {
		List<String> subclassNames = new ArrayList<String>();
		for(Expression expression : typeCheckMap.keySet()) {
			SimpleName simpleName = staticFieldMap.get(expression);
			if(simpleName != null) {
				String staticFieldName = simpleName.getIdentifier();
				Type castingType = getCastingType(typeCheckMap.get(expression));
				String subclassName = null;
				if(!staticFieldName.contains("_")) {
					subclassName = staticFieldName.substring(0, 1).toUpperCase() + 
					staticFieldName.substring(1, staticFieldName.length()).toLowerCase();
				}
				else {
					subclassName = "";
					StringTokenizer tokenizer = new StringTokenizer(staticFieldName,"_");
					while(tokenizer.hasMoreTokens()) {
						String tempName = tokenizer.nextToken().toLowerCase().toString();
						subclassName += tempName.subSequence(0, 1).toString().toUpperCase() + 
						tempName.subSequence(1, tempName.length()).toString();
					}
				}
				if(existingInheritanceTree != null) {
					DefaultMutableTreeNode root = existingInheritanceTree.getRootNode();
					Enumeration<DefaultMutableTreeNode> enumeration = root.children();
					boolean found = false;
					while(enumeration.hasMoreElements()) {
						DefaultMutableTreeNode child = enumeration.nextElement();
						String childClassName = (String)child.getUserObject();
						if(childClassName.endsWith(subclassName)) {
							subclassNames.add(childClassName);
							found = true;
							break;
						}
						else if(castingType != null && castingType.resolveBinding().getQualifiedName().equals(childClassName)) {
							subclassNames.add(childClassName);
							found = true;
							break;
						}
					}
					if(!found)
						subclassNames.add(null);
				}
				else {
					subclassNames.add(subclassName);
				}
			}
			Type type = subclassTypeMap.get(expression);
			if(type != null) {
				subclassNames.add(type.resolveBinding().getQualifiedName());
			}
		}
		return subclassNames;
	}
	
	private Type getCastingType(ArrayList<Statement> typeCheckCodeFragment) {
		List<Expression> castExpressions = new ArrayList<Expression>();
		ExpressionExtractor expressionExtractor = new ExpressionExtractor();
		for(Statement statement : typeCheckCodeFragment) {
			castExpressions.addAll(expressionExtractor.getCastExpressions(statement));
		}
		for(Expression expression : castExpressions) {
			CastExpression castExpression = (CastExpression)expression;
			Expression expressionOfCastExpression = castExpression.getExpression();
			SimpleName superTypeSimpleName = null;
			if(expressionOfCastExpression instanceof SimpleName) {
				superTypeSimpleName = (SimpleName)expressionOfCastExpression;
			}
			else if(expressionOfCastExpression instanceof FieldAccess) {
				FieldAccess fieldAccess = (FieldAccess)expressionOfCastExpression;
				superTypeSimpleName = fieldAccess.getName();
			}
			else if(expressionOfCastExpression instanceof MethodInvocation) {
				MethodInvocation methodInvocation = (MethodInvocation)expressionOfCastExpression;
				if(typeFieldGetterMethod != null && typeFieldGetterMethod.resolveBinding().isEqualTo(methodInvocation.resolveMethodBinding())) {
					superTypeSimpleName = MethodDeclarationUtility.isGetter(typeFieldGetterMethod);
				}
			}
			if(superTypeSimpleName != null) {
				if(	(typeField != null && typeField.resolveBinding().isEqualTo(superTypeSimpleName.resolveBinding())) ||
					(typeLocalVariable != null && typeLocalVariable.resolveBinding().isEqualTo(superTypeSimpleName.resolveBinding())) )
					return castExpression.getType();
			}
		}
		return null;
	}
	
	public Set<ITypeBinding> getThrownExceptions() {
		ExpressionExtractor expressionExtractor = new ExpressionExtractor();
		StatementExtractor statementExtractor = new StatementExtractor();
		Set<ITypeBinding> thrownExceptions = new LinkedHashSet<ITypeBinding>();
		for(Expression key : typeCheckMap.keySet()) {
			ArrayList<Statement> statements = typeCheckMap.get(key);
			for(Statement typeCheckStatement : statements) {
				List<Expression> methodInvocations = expressionExtractor.getMethodInvocations(typeCheckStatement);
				List<Expression> classInstanceCreations = expressionExtractor.getClassInstanceCreations(typeCheckStatement);
				List<Statement> tryStatements = statementExtractor.getTryStatements(typeCheckStatement);
				Set<ITypeBinding> catchClauseExceptions = new LinkedHashSet<ITypeBinding>();
				for(Statement statement : tryStatements) {
					TryStatement tryStatement = (TryStatement)statement;
					List<CatchClause> catchClauses = tryStatement.catchClauses();
					for(CatchClause catchClause : catchClauses) {
						SingleVariableDeclaration exception = catchClause.getException();
						Type exceptionType = exception.getType();
						catchClauseExceptions.add(exceptionType.resolveBinding());
					}
				}
				for(Expression expression : methodInvocations) {
					if(expression instanceof MethodInvocation) {
						MethodInvocation methodInvocation = (MethodInvocation)expression;
						IMethodBinding methodBinding = methodInvocation.resolveMethodBinding();
						ITypeBinding[] typeBindings = methodBinding.getExceptionTypes();
						for(ITypeBinding typeBinding : typeBindings) {
							if(!catchClauseExceptions.contains(typeBinding))
								thrownExceptions.add(typeBinding);
						}
					}
				}
				for(Expression expression : classInstanceCreations) {
					ClassInstanceCreation classInstanceCreation = (ClassInstanceCreation)expression;
					IMethodBinding methodBinding = classInstanceCreation.resolveConstructorBinding();
					ITypeBinding[] typeBindings = methodBinding.getExceptionTypes();
					for(ITypeBinding typeBinding : typeBindings) {
						if(!catchClauseExceptions.contains(typeBinding))
							thrownExceptions.add(typeBinding);
					}
				}
			}
		}
		return thrownExceptions;
	}
	
	public boolean allTypeCheckBranchesAreEmpty() {
		for(Expression key : typeCheckMap.keySet()) {
			ArrayList<Statement> statements = typeCheckMap.get(key);
			if(!statements.isEmpty())
				return false;
		}
		return true;
	}
	
	public boolean isTypeCheckMethodStateSetter() {
		InheritanceTree tree = null;
		if(existingInheritanceTree != null)
			tree = existingInheritanceTree;
		else if(inheritanceTreeMatchingWithStaticTypes != null)
			tree = inheritanceTreeMatchingWithStaticTypes;
		if(tree != null) {
			DefaultMutableTreeNode root = tree.getRootNode();
			Enumeration<DefaultMutableTreeNode> children = root.children();
			List<String> subclassNames = new ArrayList<String>();
			while(children.hasMoreElements()) {
				DefaultMutableTreeNode node = children.nextElement();
				subclassNames.add((String)node.getUserObject());
			}
			Block typeCheckMethodBody = typeCheckMethod.getBody();
			List<Statement> statements = typeCheckMethodBody.statements();
			if(statements.size() > 0 && statements.get(0) instanceof SwitchStatement) {
				SwitchStatement switchStatement = (SwitchStatement)statements.get(0);
				List<Statement> statements2 = switchStatement.statements();
				ExpressionExtractor expressionExtractor = new ExpressionExtractor();
				int matchCounter = 0;
				for(Statement statement2 : statements2) {
					if(!(statement2 instanceof SwitchCase) && !(statement2 instanceof BreakStatement)) {
						List<Expression> classInstanceCreations = expressionExtractor.getClassInstanceCreations(statement2);
						if(classInstanceCreations.size() == 1) {
							ClassInstanceCreation classInstanceCreation = (ClassInstanceCreation)classInstanceCreations.get(0);
							Type classInstanceCreationType = classInstanceCreation.getType();
							if(subclassNames.contains(classInstanceCreationType.resolveBinding().getQualifiedName())) {
								matchCounter++;
							}
						}
					}
				}
				if(matchCounter == subclassNames.size())
					return true;
			}
		}
		return false;
	}
}
