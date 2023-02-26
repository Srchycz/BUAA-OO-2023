package expr;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;

public class Expression {
    private ArrayList<Variable> variables;

    public Expression() {
        this.variables = new ArrayList<>();
    }

    public void addVariable(Variable variable) {
        this.variables.add(variable);
    }

    public void simplify() {
        Collections.sort(variables, new Comparator<Variable>() {
            @Override
            public int compare(Variable o1, Variable o2) {
                if (o1.getXidx() == o2.getXidx()) {
                    if (o1.getYidx() == o2.getYidx()) {
                        return o1.getZidx() - o2.getZidx();
                    }
                    return o1.getYidx() - o2.getYidx();
                }
                return o1.getXidx() - o2.getXidx();
            }
        });
        Iterator<Variable> iter = variables.iterator();
        Variable now = iter.next();
        while (iter.hasNext()) {
            Variable nxt = iter.next();
            if (now.comp(nxt)) {
                now.merge(nxt);
                iter.remove();
            }
            else {
                now = nxt;
            }
        }
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        for (Variable variable : variables) {
            sb.append(variable);
        }
        if (sb.toString().equals("")) {
            sb.append("+0");
        }
        return sb.toString();
    }
}
