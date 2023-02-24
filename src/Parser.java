import expr.*;
import expr.Number;

import java.math.BigInteger;

public class Parser {
    private final Lexer lexer;

    public Parser(Lexer lexer) {
        this.lexer = lexer;
    }

    public Expr parseExpr() {
        Expr expr = new Expr();
        expr.addTerm(parseTerm());

        while (lexer.peek().equals("+") || lexer.peek().equals("-")) {
            lexer.next();
            expr.addTerm(parseTerm());
        }
        return expr;
    }

    public Term parseTerm() {
        Term term = new Term();
        if(lexer.peek().equals("+") || lexer.peek().equals("-")){
            term.setSign(lexer.peek());
            lexer.nextNumber();
        }
        term.addFactor(parseFactor());

        while (lexer.peek().equals("*")) {
            lexer.next();
            term.addFactor(parseFactor());
        }
        return term;
    }

    public Factor parseFactor() {
        if (lexer.peek().equals("(")) {
            lexer.next();
            Factor expr = parseExpr();
            lexer.next();
            if(lexer.peek().equals("**")){
                lexer.nextNumber();
                expr.setIndex(Integer.parseInt(lexer.peek()));
                lexer.next();
            }
            return expr;
        } else {
            if(lexer.peek().equals("x") || lexer.peek().equals("y") || lexer.peek().equals("z")){
                Var var = new Var(lexer.peek());
                lexer.next();
                if(lexer.peek().equals("**")){
                    lexer.nextNumber();
                    var.setIndex(Integer.parseInt(lexer.peek()));
                    lexer.next();
                }
                return var;
            }
            else{
                expr.Number number = new Number(lexer.peek());
                lexer.next();
                if(lexer.peek().equals("**")){
                    lexer.nextNumber();
                    number.setIndex(Integer.parseInt(lexer.peek()));
                    lexer.next();
                }
                return number;
            }
        }
    }
}
