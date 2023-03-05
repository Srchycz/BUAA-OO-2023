import expr.Expr;

import java.util.Scanner;

public class Main {
    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        InputHandler inputHandler = new InputHandler(scanner);

        inputHandler.input();
        //System.out.println(inputHandler.simplify());

        Lexer lexer = new Lexer(simplifySign(inputHandler.simplify()));
        Parser parser = new Parser(lexer);
        Expr expr = parser.parseExpr();
        System.out.println(simplifySign(expr.toString()));

        /*Lexer lexer1 = new Lexer(simplifySign(expr.toString().replaceAll("\\s","")));
//        Parser parser1 = new Parser(lexer1);
//        Expression expression = parser1.parseExpression();
//        expression.simplify();
          System.out.println(expression);*/
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