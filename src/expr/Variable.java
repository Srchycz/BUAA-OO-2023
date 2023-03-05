package expr;

import java.math.BigInteger;
import java.util.ArrayList;

public class Variable {
    private BigInteger coe;

    private int xidx;

    private int yidx;

    private int zidx;

    private String sign;

    private ArrayList<Tri> tris;

    public Variable() {
        this.xidx = 0;
        this.yidx = 0;
        this.zidx = 0;
        this.coe = BigInteger.ONE;
        this.sign = "+";
        this.tris = new ArrayList<>();
    }

    public BigInteger getCoe() {
        return coe;
    }

    public int getYidx() {
        return yidx;
    }

    public int getXidx() {
        return xidx;
    }

    public int getZidx() {
        return zidx;
    }

    public String getSign() {
        return sign;
    }

    public void setSign(String sign) {
        this.sign = sign;
    }

    public void addTri(Tri tri) {
        this.tris.add(tri);
    }

    public void addIdx(String var, int c) {
        switch (var) {
            case "x": {
                xidx += c;
                break;
            }
            case "y": {
                yidx += c;
                break;
            }
            case "z": {
                zidx += c;
                break;
            }
            default: { }
        }
    }

    public void mulCoe(String num, int c) {
        BigInteger temp = new BigInteger(num);
        for (int i = 1; i <= c; ++ i) {
            coe = coe.multiply(temp);
        }
    }

    public boolean comp(Variable src) {
        return (src.getXidx() == xidx) & (src.getYidx() == yidx) & (src.getZidx() == zidx);
    }

    public void merge(Variable src) {
        if (src.getSign().equals("+")) {
            if (sign.equals("+")) {
                coe = coe.add(src.getCoe());
            }
            else {
                coe = coe.subtract(src.getCoe());
            }
        }
        else {
            if (sign.equals("-")) {
                coe = coe.add(src.getCoe());
            }
            else {
                coe = coe.subtract(src.getCoe());
            }
        }
    }

    @Override
    public String toString() {
        if (coe.compareTo(BigInteger.ZERO) == 0) {
            return "";
        }
        StringBuilder sb = new StringBuilder();
        sb.append(sign);
        sb.append(coe);
        switch (xidx) {
            case 0 : { break; }
            case 1 : {
                sb.append("*x");
                break;
            }
            case 2 : {
                sb.append("*x*x");
                break;
            }
            default : {
                sb.append("*x**").append(xidx);
            }
        }
        switch (yidx) {
            case 0 : { break; }
            case 1 : {
                sb.append("*y");
                break;
            }
            case 2 : {
                sb.append("*y*y");
                break;
            }
            default : {
                sb.append("*y**").append(yidx);
            }
        }
        switch (zidx) {
            case 0 : { break; }
            case 1 : {
                sb.append("*z");
                break;
            }
            case 2 : {
                sb.append("*z*z");
                break;
            }
            default : {
                sb.append("*z**").append(zidx);
            }
        }
        for (Tri tri : tris) {
            sb.append("*");
            sb.append(tri);
        }
        return sb.toString();
    }
}
