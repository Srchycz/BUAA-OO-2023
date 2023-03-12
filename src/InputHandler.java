import expr.Expr;
import expr.Expression;

import java.util.ArrayList;
import java.util.Scanner;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class InputHandler {

    private static final String REGEX = "(.*)=(.*)";

    private static final Pattern p = Pattern.compile(REGEX);
    private final Scanner scanner;

    private ArrayList<SelfFunction> selfFunctions;

    private String string;

    public InputHandler(Scanner s) {
        this.scanner = s;
        this.selfFunctions = new ArrayList<>();
    }

    public String getString() {
        return this.string;
    }

    private String simderiv(String s) throws CloneNotSupportedException {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < s.length(); ++ i) {
            if (s.charAt(i) != 'd') {
                sb.append(s.charAt(i));
            }
            else {
                int cnt = 1;
                int f = 0;
                for (int j = i + 3; j < s.length(); ++ j) {
                    if (s.charAt(j) == '(') {
                        ++ cnt;
                    }
                    if (s.charAt(j) == ')') {
                        -- cnt;
                    }
                    if (cnt == 0) {
                        f = j;
                        break;
                    }
                }
                sb.append("(");
                sb.append(Derive(s.substring(i + 3, f), s.charAt(i + 1)));
                sb.append(")");
                i = f;
            }
        }
        return sb.toString();
    }

    public void input() throws CloneNotSupportedException {
        int n = scanner.nextInt();
        scanner.nextLine(); //读去换行符
        if (n > 0) {
            String s = Main.simplifySign(scanner.nextLine().replaceAll("\\s",""));
            Matcher m = p.matcher(s);
            m.find();
            SelfFunction function = new SelfFunction(m.group(1) + "=" + simderiv(m.group(2)));
            selfFunctions.add(function);
        }
        for (int i = 1; i < n; ++ i) {
            String string = scanner.nextLine().replaceAll("\\s","");
            Matcher matcher = p.matcher(string);
            matcher.find();
            SelfFunction function = new SelfFunction(matcher.group(1)
                    + "=" + simderiv(Main.simplifySign(simplify(matcher.group(2)))));
            selfFunctions.add(function);
        }
        string = scanner.nextLine().replaceAll("\\s", "");
        string = simderiv(Main.simplifySign(simplify(string)));
    }

    public String simplify(String string) {
        StringBuilder sb = new StringBuilder();
        int pos = 0;
        int len = string.length();
        while (pos < len) {
            char c = string.charAt(pos);
            if ("fgh".indexOf(c) != -1) {
                pos += 2;
                String funcname = String.valueOf(c);
                sb.append(deFunction(string, pos, funcname));
                int u = 1;
                while (u > 0) {
                    char x = string.charAt(pos);
                    ++pos;
                    if (x == '(') {
                        ++u;
                    }
                    if (x == ')') {
                        --u;
                    }
                }
            }
            else {
                sb.append(c);
                ++pos;
            }
        }
        return sb.toString();
    }

    public String deFunction(String input, int pos, String func) {
        StringBuilder sb = new StringBuilder();
        int cnt = 1;
        int addr = pos;
        while (cnt > 0) {
            char c = input.charAt(addr);
            if (c == '(') {
                ++ cnt;
            }
            if (c == ')') {
                -- cnt;
            }
            if ("fgh".indexOf(c) != -1) {
                addr += 2;
                String funcname = String.valueOf(c);
                sb.append(deFunction(input, addr, funcname));
                int u = 1;
                while (u > 0) {
                    char x = input.charAt(addr);
                    ++ addr;
                    if (x == '(') {
                        ++ u;
                    }
                    if (x == ')') {
                        -- u;
                    }
                }
            }
            else {
                sb.append(c);
                ++ addr;
            }
        }
        sb.deleteCharAt(sb.length() - 1);
        for (SelfFunction function : selfFunctions) {
            if (function.getName().equals(func)) {
                return function.deFunction(sb.toString());
            }
        }
        return "";
    }

    public String Derive(String string, char var) throws CloneNotSupportedException {
        Lexer lexer = new Lexer(string);
        Parser parser = new Parser(lexer);
        Expr expr = parser.parseExpr();
        Lexer lexer1 = new Lexer(Main.simplifySign(expr.toString().replaceAll("\\s","")));
        Parser parser1 = new Parser(lexer1);
        Expression expression = parser1.parseExpression();
        expression = expression.derive(String.valueOf(var));
        return expression.toString().replaceAll("\\+\\*","+").replaceAll("-\\*","-");
    }
}
