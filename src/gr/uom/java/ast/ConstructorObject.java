package gr.uom.java.ast;

import gr.uom.java.ast.decomposition.MethodBodyObject;

import java.util.List;
import java.util.ArrayList;
import java.util.ListIterator;

import org.eclipse.jdt.core.dom.MethodDeclaration;

public class ConstructorObject {

    protected String name;
	protected List<ParameterObject> parameterList;
    protected Access access;
    protected MethodBodyObject methodBody;
    protected MethodDeclaration methodDeclaration;

    public ConstructorObject() {
		this.parameterList = new ArrayList<ParameterObject>();
        this.access = Access.NONE;
    }

    public void setMethodDeclaration(MethodDeclaration methodDeclaration) {
    	this.methodDeclaration = methodDeclaration;
    }

    public MethodDeclaration getMethodDeclaration() {
    	return this.methodDeclaration;
    }

    public void setMethodBody(MethodBodyObject methodBody) {
    	this.methodBody = methodBody;
    }

    public MethodBodyObject getMethodBody() {
    	return this.methodBody;
    }

    public void setAccess(Access access) {
        this.access = access;
    }

    public Access getAccess() {
        return access;
    }

    public void setName(String name) {
		this.name = name;
	}
	
	public String getName() {
		return name;
	}
	
	public boolean addParameter(ParameterObject parameter) {
		return parameterList.add(parameter);
	}

    public ListIterator<ParameterObject> getParameterListIterator() {
		return parameterList.listIterator();
	}
	
	public ListIterator<MethodInvocationObject> getMethodInvocationIterator() {
		return methodBody.getMethodInvocations().listIterator();
	}

    public ListIterator<FieldInstructionObject> getFieldInstructionIterator() {
        return methodBody.getFieldInstructions().listIterator();
    }

    public ListIterator<LocalVariableDeclarationObject> getLocalVariableDeclarationIterator() {
        return methodBody.getLocalVariableDeclarations().listIterator();
    }
    
    public ListIterator<LocalVariableInstructionObject> getLocalVariableInstructionIterator() {
        return methodBody.getLocalVariableInstructions().listIterator();
    }

    public List<TypeObject> getParameterTypeList() {
    	List<TypeObject> list = new ArrayList<TypeObject>();
    	for(ParameterObject parameterObject : parameterList)
    		list.add(parameterObject.getType());
    	return list;
    }

    public List<String> getParameterList() {
    	List<String> list = new ArrayList<String>();
    	for(ParameterObject parameterObject : parameterList)
    		list.add(parameterObject.getType().toString());
    	return list;
    }

    public boolean equals(Object o) {
        if(this == o) {
			return true;
		}

		if (o instanceof ConstructorObject) {
			ConstructorObject constructorObject = (ConstructorObject)o;

			return this.name.equals(constructorObject.name) &&
				this.parameterList.equals(constructorObject.parameterList);
		}
		return false;
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();
        if(!access.equals(Access.NONE))
            sb.append(access.toString()).append(" ");
        sb.append(name);
        sb.append("(");
        if(!parameterList.isEmpty()) {
            for(int i=0; i<parameterList.size()-1; i++)
                sb.append(parameterList.get(i).toString()).append(", ");
            sb.append(parameterList.get(parameterList.size()-1).toString());
        }
        sb.append(")");
        sb.append("\n").append(methodBody.toString());
        return sb.toString();
    }
}