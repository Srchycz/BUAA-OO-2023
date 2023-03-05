package expr;

public class Tri {
    private int index;

    private final String name;

    private Expression expr;

    public Tri(String name) {
        this.name = name;
        this.index = 1;
    }

    public Expression getExpression() {
        return expr;
    }

    public void setExpression(Expression expression) {
        this.expr = expression;
    }

    public void setIndex(int c){
        this.index = c;
    }

    public int getIndex() {
        return this.index;
    }

    @Override
    public String toString() {
        if (index == 0) {
            return "1";
        }
        if (index > 1) {
            return name + "((" + expr.toString() + "))" + "**" + index;
        }
        return name + "((" + expr.toString() + "))";
    }

}
