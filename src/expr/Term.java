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
        if (f.equals("-"))
        {
            this.sign = (this.sign.equals("-")) ? "+" : "-";
        }
    }

    public ArrayList<Factor> getFactors() {
        return factors;
    }

    @Override
    public String toString()
    {
        StringBuilder sb = new StringBuilder();
        for (Factor factor : factors) {
            if (factor instanceof Expr) {
                int idx = ((Expr) factor).getIndex();
                if (idx == 0) {
                    this.removeFactor(factor);
                    Number one = new Number(BigInteger.ONE);
                    this.addFactor(one);
                    continue;
                }
                while (idx > 1) {
                    --idx;
                    Expr factorCopy = new Expr(((Expr) factor));
                    this.addFactor(factorCopy);
                }
                factor.setIndex(idx);

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
