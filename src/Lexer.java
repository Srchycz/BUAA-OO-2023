public class Lexer {

    private final String input;

    private int pos = 0;
    private String curToken;

    public Lexer(String input) {
        this.input = input;
        this.next();
    }

    private String getNumber() {
        StringBuilder sb = new StringBuilder();
        while (pos < input.length() && Character.isDigit(input.charAt(pos))) {
            sb.append(input.charAt(pos));
            ++pos;
        }

        return sb.toString();
    }

    public void next() {
        if (pos == input.length()) {
            return;
        }

        char c = input.charAt(pos);
        if (Character.isDigit(c)) {
            curToken = this.getNumber();
        }
        else {
            if ("()+-*xyz".indexOf(c) != -1) {
                ++ pos;
                if (c == '*' && input.charAt(pos) == '*') {
                    curToken = "**";
                    ++ pos;
                }
                else {
                    curToken = String.valueOf(c);
                }
            }
            else {
                System.out.println("cannot identify!");
            }
        }
    }

    public void nextNumber() {
        if (pos == input.length()) {
            return;
        }

        char c = input.charAt(pos);
        if ("+-".indexOf(c) != -1) {
            StringBuilder sb = new StringBuilder();
            sb.append(c);
            ++pos;
            sb.append(this.getNumber());
            curToken = sb.toString();
        }
        else {
            if (Character.isDigit(c)) {
                curToken = this.getNumber();
            }
            else {
                curToken = String.valueOf(c);
                ++ pos;
            }
        }
    }

    public String peek() {
        return this.curToken;
    }

}
