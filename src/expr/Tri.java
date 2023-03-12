package expr;

public class Tri implements Cloneable {
    private int index;

    private final String name;

    private Expression expr;

    public Tri(String name) {
        this.name = name;
        this.index = 1;
    }

    public Expression getExpression() {
        expr.simplify();
        return expr;
    }

    public void setExpression(Expression expression) {
        this.expr = expression;
    }

    public void setIndex(int c) {
        this.index = c;
    }

    public int getIndex() {
        return this.index;
    }

    public String getName() {
        return name;
    }

    public Variable derive(String var) throws CloneNotSupportedException {
        Variable v = new Variable();
        if (index == 0) {
            return v;
        }
        v.addExpression(expr.derive(var));
        Tri tri;
        if (getName().equals("cos")) {
            v.setSign("-");
            tri = new Tri("sin");
        }
        else {
            tri = new Tri("cos");
        }
        tri.setExpression(getExpression().clone());
        v.addTri(tri);
        if (index > 1) {
            Tri tricopy = this.clone();
            v.mulCoe(String.valueOf(index),1);
            tricopy.setIndex(index - 1);
            v.addTri(tricopy);
        }
        return v;
    }

    public boolean isZero() {
        return expr.isZero() && name.equals("sin");
    }

    @Override
    public String toString() {
        if (index == 0) {
            return "1";
        }
        expr.simplify();
        if (expr.isZero()) {
            if (name.equals("sin")) {
                return "0";
            }
            else {
                return "1";
            }
        }
        if (index > 1) {
            return name + "((" + expr.toString() + "))" + "**" + index;
        }
        return name + "((" + expr.toString() + "))";
    }

    @Override
    public Tri clone() throws CloneNotSupportedException {
        Tri clone = (Tri) super.clone();
        clone.expr = expr.clone();
        return clone;
    }

}
