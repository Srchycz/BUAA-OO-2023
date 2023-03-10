package expr;

public class Var implements Factor, Cloneable
{

    private final String var;

    private int index;

    private String sign;

    public String getSign() {
        return sign;
    }

    public void setSign(String sign) {
        this.sign = sign;
    }

    public Var(String x)
    {
        this.var = x;
        this.index = 1;
        this.sign = "+";
    }

    public void setIndex(int c) {
        this.index = c;
    }

    public int getIndex() {
        return index;
    }

    @Override
    public String toString()
    {
        if (index == 0)
        {
            return String.valueOf(1);
        }
        StringBuilder sb = new StringBuilder();
        sb.append(var);
        if (index > 1)
        {
            sb.append("**");
            sb.append(index);
        }
        return sb.toString();
    }

    @Override
    public Var clone() throws CloneNotSupportedException {
        return (Var) super.clone();
    }

}
