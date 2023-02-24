package expr;

public class Var implements Factor{

    private final String var;

    private int index;

    public Var(String x){
        this.var = x;
    }

    public void setIndex(int c){
        this.index = c;
    }
}
