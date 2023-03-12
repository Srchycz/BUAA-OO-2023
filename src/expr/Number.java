package expr;

import java.math.BigInteger;

public class Number implements Factor, Cloneable {

    private BigInteger num;

    private int index;

    public Number(BigInteger val) {
        this.num = val;
        this.index = 1;
    }

    public Number(String val) {
        try {
            this.num = new BigInteger(val);
        } catch (NumberFormatException e) {
            throw e;
        }
        this.index = 1;
    }

    public void setIndex(int index) {
        this.index = index;
    }

    public int getIndex() {
        return index;
    }

    @Override
    public String toString() {
        if (index == 0) {
            return String.valueOf(1);
        }
        StringBuilder sb = new StringBuilder();
        sb.append(num);
        if (index > 1) {
            sb.append("**");
            sb.append(index);
        }
        return sb.toString();
    }

    @Override
    public Number clone() throws CloneNotSupportedException {
        return (Number) super.clone();
    }
}
