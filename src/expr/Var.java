package expr;

public class Var implements Factor{

    private final String var;

    private int index;

    public Var(String x){
        this.var = x;
        this.index = 1;
    }

    public void setIndex(int c){
        this.index = c;
    }

    @Override
    public String toString(){
        StringBuilder sb = new StringBuilder();
        sb.append(var);
        if(index != 1){
            sb.append("**");
            sb.append(index);
        }
        return sb.toString();
    }
}
