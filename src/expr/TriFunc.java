package expr;

public class TriFunc implements Factor, Cloneable {
    private int index;

    private final String name;

    private Expr expr;

    public TriFunc(String name) {
        this.name = name;
        this.index = 1;
    }

    public Expr getExpr() {
        return expr;
    }

    public void setExpr(Expr expr) {
        this.expr = expr;
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

    @Override
    public TriFunc clone() throws CloneNotSupportedException {
        TriFunc triFunc = (TriFunc) super.clone();
        triFunc.expr = expr.clone();
        return triFunc;
    }

}
