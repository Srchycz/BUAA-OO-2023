import java.text.MessageFormat;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class SelfFunction {

    private static final String REGEX = "(\\w)\\((.+)\\)=(.*)";

    private static final Pattern p = Pattern.compile(REGEX);

    private final String name;

    private final MessageFormat formula;

    private final String rawformula;

    private final String[] param;

    public SelfFunction(String s) {
        Matcher m = p.matcher(s);
        if (!m.find()) {
            System.out.println("SF cannot initialize!");
            System.out.println(s);
            System.exit(0);
        }
        this.name = m.group(1);
        this.param = m.group(2).split(",");
        this.rawformula = m.group(3);
        String formula1;
        formula1 = m.group(3);
        for (int i = 0; i < param.length; ++ i) {
            formula1 = formula1.replaceAll(param[i], "({" + i + "})");
        }
        this.formula = new MessageFormat(formula1);
    }

    public String getName() {
        return this.name;
    }

    public String deFunction(String s) {
        String[] expr = s.split(",");
        if (param.length != expr.length) {
            System.out.println("F is not match!");
            System.exit(0);
        }
        return formula.format(expr);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(this.name);
        sb.append("(");
        sb.append(this.param[0]);
        for (int i = 1; i < param.length; ++ i) {
            sb.append(",");
            sb.append(this.param[1]);
        }
        sb.append(")=");
        sb.append(this.rawformula);
        return sb.toString();
    }
}
