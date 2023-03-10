import expr.Expr;
import expr.Expression;

import java.util.Scanner;

public class Main {
    public static void main(String[] args) throws CloneNotSupportedException {
        Scanner scanner = new Scanner(System.in);
        InputHandler inputHandler = new InputHandler(scanner);
        inputHandler.input();

        Lexer lexer = new Lexer(simplifySign(inputHandler.getString()).
                replaceAll("\\*-sin", "*-1*sin").
                replaceAll("\\*-cos", "*-1*cos"));
        Parser parser = new Parser(lexer);
        Expr expr = parser.parseExpr();

        Lexer lexer1 = new Lexer(simplifySign(expr.toString().replaceAll("\\s","")));
        Parser parser1 = new Parser(lexer1);
        Expression expression = parser1.parseExpression();
        expression.simplify();
        System.out.println(simplifySign(expression.toString().
                replaceAll("\\+\\*","+").
                replaceAll("-\\*","-").replaceAll("\\(\\+", "(")));
    }

    public static String simplifySign(String input) {
        StringBuilder sb = new StringBuilder();
        int pos = 0;
        while (pos < input.length()) {
            if (input.charAt(pos) == '+' || input.charAt(pos) == '-') {
                int flag = 1;
                if (input.charAt(pos) == '-') {
                    flag ^= 1;
                    ++ pos;
                }
                while (input.charAt(pos) == '+' || input.charAt(pos) == '-') {
                    if (input.charAt(pos) == '-') {
                        flag ^= 1;
                    }
                    ++ pos;
                }
                if (flag == 1) {
                    sb.append("+");
                }
                else {
                    sb.append("-");
                }
            }
            else {
                sb.append(input.charAt(pos));
                ++ pos;
            }
        }
        if (sb.toString().equals("")) {
            return "+0";
        }
        return sb.toString();
    }
}
//0
//-1*2*sin((+y))**2-2*sin((+x))**2*1+2*sin((+x))**2*2*sin((+y))**2