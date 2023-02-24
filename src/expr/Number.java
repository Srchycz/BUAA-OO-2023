package expr;

import java.math.BigInteger;

public class Number implements Factor{

    private BigInteger num;

    private int index;

    public Number(BigInteger val){
        this.num = val;
        this.index = 1;
    }

    public Number(String val){
        this.num = new BigInteger(val);
        this.index = 1;
    }

    public void setIndex(int index) {
        this.index = index;
    }
}
