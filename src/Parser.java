import expr.Var;
import expr.Term;
import expr.Expression;
import expr.Factor;
import expr.Variable;
import expr.Expr;
import expr.Number;

public class Parser {
    private final Lexer lexer;

    public Parser(Lexer lexer) {
        this.lexer = lexer;
    }

    public Expr parseExpr() {
        Expr expr = new Expr();
        expr.addTerm(parseTerm());

        while (lexer.peek().equals("+") || lexer.peek().equals("-")) {
            String c = lexer.peek();
            lexer.next();
            Term term = parseTerm();
            expr.addTerm(term);
            term.mergeSign(c);
        }
        return expr;
    }

    public Term parseTerm() {
        Term term = new Term();
        if (lexer.peek().equals("+") || lexer.peek().equals("-"))
        {
            term.setSign(lexer.peek());
            lexer.nextNumber();
        }
        term.addFactor(parseFactor());

        while (lexer.peek().equals("*")) {
            lexer.nextNumber();
            term.addFactor(parseFactor());
        }
        return term;
    }

    public Factor parseFactor() {
        if (lexer.peek().equals("(")) {
            lexer.next();
            Factor expr = parseExpr();
            lexer.next();
            if (lexer.peek().equals("**")) {
                lexer.nextNumber();
                expr.setIndex(Integer.parseInt(lexer.peek()));
                lexer.next();
            }
            return expr;
        } else {
            if (lexer.peek().equals("x") || lexer.peek().equals("y") || lexer.peek().equals("z")) {
                Var var = new Var(lexer.peek());
                lexer.next();
                if (lexer.peek().equals("**")) {
                    lexer.nextNumber();
                    var.setIndex(Integer.parseInt(lexer.peek()));
                    lexer.next();
                }
                return var;
            }
            else {
                expr.Number number = new Number(lexer.peek());
                lexer.next();
                if (lexer.peek().equals("**")) {
                    lexer.nextNumber();
                    number.setIndex(Integer.parseInt(lexer.peek()));
                    lexer.next();
                }
                return number;
            }
        }
    }

    public Expression parseExpression() {
        Expression expression = new Expression();

        while (lexer.peek().equals("+") || lexer.peek().equals("-")) {
            String c = lexer.peek();
            lexer.next();
            Variable variable = parseVariable();
            expression.addVariable(variable);
            variable.setSign(c);
        }
        return expression;

    }

    public Variable parseVariable() {
        Variable variable = new Variable();
        parseFac(variable);

        while (lexer.peek().equals("*")) {
            lexer.next();
            parseFac(variable);
        }
        return variable;
    }

    private void parseFac(Variable variable) {
        if (lexer.peek().equals("x") || lexer.peek().equals("y") || lexer.peek().equals("z")) {
            String var = lexer.peek();
            int c = 1;
            lexer.next();
            if (lexer.peek().equals("**")) {
                lexer.next();
                c = Integer.parseInt(lexer.peek());
                lexer.next();
            }
            variable.addIdx(var, c);
        }
        else {
            String num = lexer.peek();
            int c = 1;
            lexer.next();
            if (lexer.peek().equals("**")) {
                lexer.next();
                c = Integer.parseInt(lexer.peek());
                lexer.next();
            }
            variable.mulCoe(num, c);
        }
    }
}
