package expr;

import java.util.ArrayList;

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

    /*@Override
    public String toString(){

    }*/

}
