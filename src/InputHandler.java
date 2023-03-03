import java.util.ArrayList;
import java.util.Scanner;

public class InputHandler {
    private final Scanner scanner;

    private ArrayList<SelfFunction> selfFunctions;

    private String string;

    public InputHandler(Scanner s) {
        this.scanner = s;
        this.selfFunctions = new ArrayList<>();
    }

    public void input() {
        int n = scanner.nextInt();
        scanner.nextLine(); //读去换行符
        for (int i = 0; i < n; ++ i) {
            SelfFunction function = new SelfFunction(scanner.nextLine().replaceAll("\\s", ""));
            selfFunctions.add(function);
        }
        string = scanner.nextLine().replaceAll("\\s", "");
    }

    public String simplify() {
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
}
