package expr;

import java.util.ArrayList;
import java.util.Iterator;

public class Expr implements Factor{

    public ArrayList<Term> terms;

    private int index;

    public Expr(){
        this.terms = new ArrayList<Term>();
        this.index = 1;
    }

    public Expr(Expr src){
        this.terms = new ArrayList<>();
        this.terms.addAll(src.terms);
        this.index = 1;
    }

    public void addTerm(Term x){
        terms.add(x);
    }

    public void setIndex(int c){
        this.index = c;
    }

    public int getIndex() {return index;}

    @Override
    public String toString(){
        if(index == 0){
            return String.valueOf(1);
        }
        Iterator<Term> iter = terms.iterator();
        StringBuilder sb = new StringBuilder();
        sb.append(iter.next().toString());
        while (iter.hasNext()) {
            //sb.append(" + ");
            sb.append(iter.next().toString());
        }
        if(index != 1){
            sb.append("**");
            sb.append(index);
        }
        return sb.toString();
    }

}
