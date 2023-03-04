package expr;

import java.util.ArrayList;
import java.util.Iterator;

public class Expr implements Factor, Cloneable
{

    private ArrayList<Term> terms;

    private int index;

    public Expr()
    {
        this.terms = new ArrayList<>();
        this.index = 1;
    }

    public Expr(Expr src)
    {
        this.terms = new ArrayList<>();
        this.terms.addAll(src.getTerms());
        this.index = 1;
    }

    public void addTerm(Term x)
    {
        terms.add(x);
    }

    public void setIndex(int c)
    {
        this.index = c;
    }

    public int getIndex()
    {
        return index;
    }

    public ArrayList<Term> getTerms() {
        return terms;
    }

    @Override
    public String toString()
    {
        if (index == 0)
        {
            return String.valueOf(1);
        }
        Iterator<Term> iter = terms.iterator();
        StringBuilder sb = new StringBuilder();
        sb.append(iter.next().toString());
        while (iter.hasNext()) {
            sb.append(iter.next().toString());
        }
        if (index != 1)
        {
            sb.append("**");
            sb.append(index);
        }
        return sb.toString();
    }

    @Override
    public Expr clone() throws CloneNotSupportedException {
        Expr clone = (Expr) super.clone();
        clone.terms = new ArrayList<>();
        for (Term term : terms) {
            clone.terms.add(term.clone());
        }
        return clone;
    }
}
