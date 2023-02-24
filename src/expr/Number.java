package expr;

import java.math.BigInteger;

public class Number implements Factor{

    private BigInteger num;

    private int index;

    public Number(BigInteger val){this.num = val;}

    public void setIndex(int index) {
        this.index = index;
    }
}
