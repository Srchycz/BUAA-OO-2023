package expr;

public class Var implements Factor{

    private final String var;

    private final int index;

    public Var(String x, int c){
        this.var = x;
        this.index = c;
    }
}
