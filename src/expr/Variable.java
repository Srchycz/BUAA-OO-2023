package expr;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;

public class Variable implements Cloneable {
    private BigInteger coe;

    private int xidx;

    private int yidx;

    private int zidx;

    private String sign;

    private ArrayList<Tri> tris;

    private ArrayList<Expression> expressions;

    public void setCoe(BigInteger coe) {
        this.coe = coe;
    }

    public Variable() {
        this.xidx = 0;
        this.yidx = 0;
        this.zidx = 0;
        this.coe = BigInteger.ONE;
        this.sign = "+";
        this.tris = new ArrayList<>();
        this.expressions = new ArrayList<>();
    }

    public Variable(Variable src) {
        this.xidx = src.getXidx();
        this.yidx = src.getYidx();
        this.zidx = src.getZidx();
        this.coe = src.getCoe();
        this.sign = src.getSign();
        this.tris = new ArrayList<>();
        this.tris.addAll(src.getTris());
        this.expressions = new ArrayList<>();
        this.expressions.addAll(src.getExpressions());
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

    public ArrayList<Tri> getTris() { return tris; }

    public ArrayList<Expression> getExpressions() { return expressions; }

    public void addTri(Tri tri) {
        this.tris.add(tri);
    }

    public void addExpression(Expression expression) { this.expressions.add(expression); }

    public boolean isZero() {
        if (coe.compareTo(BigInteger.ZERO) == 0) {
            return true;
        }
        boolean k = true;
        if ((xidx | yidx | zidx) > 0) {
            return false;
        }
        if (!expressions.isEmpty()) {
            return false;
        }
        for (Tri t: tris) {
            k &= t.isZero();
        }
        return k && !tris.isEmpty();
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

    public boolean equals(Variable src) {
        if (src.getSign().equals(getSign())) {
            if (coe.compareTo(src.getCoe()) != 0) {
                return false;
            }
        }
        else {
            if (coe.add(src.getCoe()).compareTo(BigInteger.ZERO) != 0) {
                return false;
            }
        }
        return comp(src);
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

    public static Variable mulVariable(Variable v1, Variable v2) throws CloneNotSupportedException {
        if (v1 == null) {
            return v2;
        }
        if (v2 == null) {
            return v1;
        }
        Variable v = v1.clone();
        v.setCoe(v.getCoe().multiply(v2.getCoe()));
        v.addIdx("x", v2.getXidx());
        v.addIdx("y", v2.getYidx());
        v.addIdx("z", v2.getZidx());
        for (Tri tri : v2.getTris()) {
            v.addTri(tri.clone());
        }
        for (Expression expression: v2.getExpressions()) {
            v.addExpression(expression.clone());
        }
        if (v.getSign().equals(v2.getSign())) {
            v.setSign("+");
        }
        else {
            v.setSign("-");
        }
        return v;
    }

    @Override
    public String toString() {
        if (coe.compareTo(BigInteger.ZERO) == 0) {
            return "";
        }
        StringBuilder sb = new StringBuilder();
        if (coe.abs().compareTo(BigInteger.ONE) == 0
                && ((xidx | yidx | zidx) > 0 || !tris.isEmpty())) {
            if (coe.compareTo(BigInteger.ZERO) > 0) {
                sb.append(sign);
            }
            else {
                sb.append(sign.equals("+") ? "-" : "+");
            }
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
        for (Expression expression: expressions) {
            sb.append("*");
            sb.append("(");
            sb.append(expression);
            sb.append(")");
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

    public ArrayList<Variable> derive(String var) throws CloneNotSupportedException {
        ArrayList<Variable> v = new ArrayList<>();
        for (int i = 0; i < tris.size(); ++ i) {
            Variable vtemp = new Variable(this);
            vtemp.tris.remove(tris.get(i));
            Variable vcopy = vtemp.clone();
            v.add(Variable.mulVariable(vcopy, tris.get(i).derive(var)));
        }
        Variable variable = this.clone();
        switch (var) {
            case "x": {
                if (xidx == 0) {
                    variable.setCoe(BigInteger.ZERO);
                }
                else {
                    variable.mulCoe(String.valueOf(xidx), 1);
                    variable.addIdx("x", -1);
                }
                break;
            }
            case "y": {
                if (yidx == 0) {
                    variable.setCoe(BigInteger.ZERO);
                }
                else {
                    variable.mulCoe(String.valueOf(yidx), 1);
                    variable.addIdx("y", -1);
                }
                break;
            }
            case "z": {
                if (zidx == 0) {
                    variable.setCoe(BigInteger.ZERO);
                }
                else {
                    variable.mulCoe(String.valueOf(zidx), 1);
                    variable.addIdx("z", -1);
                }
                break;
            }
            default: { }
        }
        v.add(variable);
        return v;
    }

    @Override
    public Variable clone() throws CloneNotSupportedException {
        Variable clone = (Variable) super.clone();
        clone.tris = new ArrayList<>();
        for (Tri tri : tris) {
            clone.tris.add(tri.clone());
        }
        return clone;
    }
}
