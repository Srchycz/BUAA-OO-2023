package expr;

import java.util.ArrayList;
import java.util.Iterator;

public class Term {

    public ArrayList<Factor> factors;

    private String sign;

    public Term(){
        this.factors = new ArrayList<Factor>();
        this.sign = "+";
    }

    public Term(Term src){
        this.factors = new ArrayList<>();
        factors.addAll(src.factors);
        this.sign = src.sign;
    }

    public void addFactor(Factor x){
        this.factors.add(x);
    }

    public void addFactor(ArrayList<Factor> factors){
        this.factors.addAll(factors);
    }

    public void removeFactor(Factor x){
        this.factors.remove(x);
    }


    public void setSign(String f){
        this.sign = f;
    }

    public String getSign(){
        return this.sign;
    }

    @Override
    public String toString(){
        StringBuilder sb = new StringBuilder();
        for(Factor factor : factors){
            if(factor instanceof Expr){
                int idx = ((Expr) factor).getIndex();
                while(idx > 1){
                    --idx;
                    Expr factorCopy = new Expr(((Expr) factor));
                    this.factors.add(factorCopy);
                }
                factor.setIndex(idx);
                Iterator<Term> iter = ((Expr) factor).terms.iterator();
                Term temp = new Term(this);
                temp.addFactor(iter.next().factors);
                temp.removeFactor(factor);
                sb.append(temp);
                while (iter.hasNext()){
                    sb.append(" + ");
                    Term a = new Term(this);
                    a.addFactor(iter.next().factors);
                    a.removeFactor(factor);
                    sb.append(a);
                }
                return sb.toString();
            }
        }

        Iterator<Factor> iter = factors.iterator();
        sb.append(sign);
        sb.append(iter.next().toString());
        if (iter.hasNext()) {
            sb.append(" * ");
            sb.append(iter.next().toString());
            while (iter.hasNext()) {
                sb.append(" * ");
                sb.append(iter.next().toString());
            }
        }
        return sb.toString();
    }

}
