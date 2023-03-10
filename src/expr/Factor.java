package expr;

public interface Factor extends Cloneable {
    public void setIndex(int c);

    public int getIndex();

    Object clone() throws CloneNotSupportedException;

}
