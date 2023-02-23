package expr;

public class Expr implements Factor{

    private ArrayList<Term> terms;

    private int index;

    public Expr(){this.terms = new ArrayList<Term>();}

    public addTerm(Term x){
        terms.add(x);
    }

    public setIndex(int c){
        this.index = c;
    }

    @Override
    public String toString(){

    }

}
