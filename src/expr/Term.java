package expr;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Iterator;

public class Term {

    private ArrayList<Factor> factors;

    private String sign;

    public Term() {
        this.factors = new ArrayList<>();
        this.sign = "+";
    }

    public Term(Term src) {
        this.factors = new ArrayList<>();
        factors.addAll(src.factors);
        this.sign = src.sign;
    }

    public void addFactor(Factor x) {
        this.factors.add(x);
    }

    public void mergeTerm(Term t) {
        this.factors.addAll(t.getFactors());
        mergeSign(t.getSign());
    }

    public void removeFactor(Factor x) {
        this.factors.remove(x);
    }

    public void setSign(String f) {
        this.sign = f;
    }

    public String getSign() {
        return this.sign;
    }

    public void mergeSign(String f) {
        if (f.equals("-")) {
            this.sign = (this.sign.equals("-")) ? "+" : "-";
        }
    }

    public ArrayList<Factor> getFactors() {
        return factors;
    }

    private void unfold() {
        ArrayList<Expr> facs = new ArrayList<>();
        Iterator<Factor> factorIterator = factors.iterator();
        while (factorIterator.hasNext()) {
            Factor factor = factorIterator.next();
            if (factor instanceof Expr) {
                int idx = factor.getIndex();
                if (idx > 1) {
                    factor.setIndex(1);
                    Expr factorCopy = new Expr(((Expr) factor));
                    factorCopy.setIndex(idx - 1);
                    facs.add(factorCopy);
                }
            }
        }
        if (!facs.isEmpty()) {
            for (Expr fac : facs) {
                int idx = fac.getIndex();
                while (idx > 0) {
                    --idx;
                    Expr facCopy = new Expr(fac);
                    this.addFactor(facCopy);
                }
            }
        }
    }

    @Override
    public String toString()
    {
        unfold();
        StringBuilder sb = new StringBuilder();
        Iterator<Factor> factorIterator = factors.iterator();
        while (factorIterator.hasNext()) {
            Factor factor = factorIterator.next();
            int idx = factor.getIndex();
            if (idx == 0) {
                factorIterator.remove();
                continue;
            }
            if (factor instanceof Expr) {
                Iterator<Term> iter = ((Expr) factor).getTerms().iterator();
                Term temp = new Term(this);
                temp.mergeTerm(iter.next());
                temp.removeFactor(factor);
                sb.append(temp);
                while (iter.hasNext()) {
                    //sb.append(" + ");
                    Term a = new Term(this);
                    a.mergeTerm(iter.next());
                    a.removeFactor(factor);
                    sb.append(a);
                }
                return sb.toString();
            }
        }

        if (factors.isEmpty()) {
            Number one = new Number(BigInteger.ONE);
            this.addFactor(one);
        }

        Iterator<Factor> iter = factors.iterator();
        sb.append(sign);
        sb.append(iter.next().toString());
        while (iter.hasNext()) {
            sb.append("*");
            sb.append(iter.next().toString());
        }
        return sb.toString();
    }

}
