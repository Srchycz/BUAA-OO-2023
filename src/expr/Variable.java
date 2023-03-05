package expr;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;

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

    public int getCount() {
        return tris.size();
    }

    public ArrayList<Tri> getTris() {
        return tris;
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
        if (!((src.getXidx() == xidx) & (src.getYidx() == yidx) & (src.getZidx() == zidx))) {
            return false;
        }
        if (src.getCount() != getCount()) {
            return false;
        }
        if (src.getCount() == getCount()) {
            HashMap<Tri, Boolean> vis = new HashMap<>();
            ArrayList<Tri> t = src.getTris();
            for (Tri tri : tris) {
                int flag = 0;
                for (Tri tri1 : t) {
                    if (tri.getName().equals(tri1.getName())) {
                        if (vis.containsKey(tri1)) {
                            continue;
                        }
                        if (tri.getIndex() != tri1.getIndex()) {
                            continue;
                        }
                        if (tri.getExpression().comp(tri1.getExpression())) {
                            flag = 1;
                            vis.put(tri1, true);
                            break;
                        }
                    }
                }
                if (flag == 0) {
                    return false;
                }
            }
        }
        return true;
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
        if (coe.abs().compareTo(BigInteger.ONE) == 0
                && ((xidx | yidx | zidx) > 0 || !tris.isEmpty())) {
            sb.append(sign);
        }
        else {
            sb.append(sign);
            sb.append(coe);
        }
        sb.append(varToS(xidx, 'x'));
        sb.append(varToS(yidx, 'y'));
        sb.append(varToS(zidx, 'z'));
        for (Tri tri : tris) {
            sb.append("*");
            sb.append(tri);
        }
        return sb.toString();
    }

    private String varToS(int c, char x) {
        StringBuilder sb = new StringBuilder();
        switch (c) {
            case 0 : { break; }
            case 1 : {
                sb.append("*").append(x);
                break;
            }
            case 2 : {
                sb.append("*").append(x).append("*").append(x);
                break;
            }
            default : {
                sb.append("*").append(x).append("**").append(c);
            }
        }
        return sb.toString();
    }

}
