package expr;

import java.util.ArrayList;
import java.util.Iterator;

public class Expr implements Factor{

    private ArrayList<Term> terms;

    private int index;

    public Expr(){
        this.terms = new ArrayList<Term>();
        this.index = 1;
    }

    public void addTerm(Term x){
        terms.add(x);
    }

    public void setIndex(int c){
        this.index = c;
    }

    @Override
    public String toString(){
        Iterator<Term> iter = terms.iterator();
        StringBuilder sb = new StringBuilder();
        sb.append(iter.next().toString());
        if (iter.hasNext()) {
            sb.append(" ");
            sb.append(iter.next().toString());
            sb.append(" +");
            while (iter.hasNext()) {
                sb.append(" ");
                sb.append(iter.next().toString());
                sb.append(" +");
            }
        }
        return sb.toString();
    }

}
