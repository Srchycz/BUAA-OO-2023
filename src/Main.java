import java.util.Scanner;

public class Main {
    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);
        Library library = Library.getInstance();
        insertBooks(scanner, library);
        act(scanner, library);
    }

    private static void insertBooks(Scanner scanner, Library library) {
        int n = scanner.nextInt();
        for (int i = 0; i < n; ++ i) {
            String bookId = scanner.next();
            Type type = Type.valueOf(bookId.substring(0, 1));
            int num = scanner.nextInt();
            library.addNewBook(type, bookId.substring(2), num);
        }
    }

    private static void act(Scanner scanner, Library library) {
        int m = scanner.nextInt();
        for (int i = 0; i < m; ++ i) {
            String date = scanner.next();
            String studentId = scanner.next();
            String action = scanner.next();
            String bookId = scanner.next();
            Type type = Type.valueOf(bookId.substring(0, 1));
            Action act = Action.getAction(action);
            library.handle(date, studentId, act, bookId.substring(2), type);
        }
    }
}