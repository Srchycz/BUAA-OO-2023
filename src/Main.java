import expr.Expr;

import java.util.Scanner;

public class Main {
    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        String input = scanner.nextLine();

        Lexer lexer = new Lexer(simplifySign(input.replaceAll("\\s+","")));
        Parser parser = new Parser(lexer);

        Expr expr = parser.parseExpr();
        System.out.println(expr);
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
        return sb.toString();
    }
}