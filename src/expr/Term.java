package expr;

import java.util.ArrayList;
import java.util.Iterator;

public class Term {

    private ArrayList<Factor> factors;

    private String sign;

    public Term(){
        this.factors = new ArrayList<Factor>();
        this.sign = "+";
    }

    public void addFactor(Factor x){
        this.factors.add(x);
    }

    public void setSign(String f){
        this.sign = f;
    }

    public String getSign(){
        return this.sign;
    }

    @Override
    public String toString(){
        Iterator<Factor> iter = factors.iterator();
        StringBuilder sb = new StringBuilder();
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
