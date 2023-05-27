import java.util.Iterator;
import java.util.LinkedList;

public class Student {
    private final String id;

    private final LinkedList<Book> borrowedBooks;

    public Student(String id) {
        this.id = id;
        this.borrowedBooks = new LinkedList<>();
    }

    public String getId() {
        return id;
    }

    public Boolean hasTypeBook(Type type) {
        for (Book book : borrowedBooks) {
            if (book.getType() == type) {
                return true;
            }
        }
        return false;
    }

    public Boolean hasBook(Type type, String id) {
        for (Book book : borrowedBooks) {
            if (book.getType() == type && book.getId().equals(id)) {
                return true;
            }
        }
        return false;
    }

    public void addBook(Book book) {
        borrowedBooks.add(book);
    }

    public Book removeBook(Type type, String id) {
        Iterator<Book> iterator = borrowedBooks.iterator();
        while (iterator.hasNext()) {
            Book book = iterator.next();
            if (book.getType() == type && book.getId().equals(id)) {
                iterator.remove();
                return book;
            }
        }
        return null;
    }

    public void loseBook(Type type, String id) {
        Iterator<Book> iterator = borrowedBooks.iterator();
        while (iterator.hasNext()) {
            Book book = iterator.next();
            if (book.getType() == type && book.getId().equals(id)) {
                book.setState(State.LOST);
                iterator.remove();
                return;
            }
        }
        System.out.println("No such book!");
    }

    public void smearBook(Type type, String id) {
        for (Book book : borrowedBooks) {
            if (book.getType() == type && book.getId().equals(id)) {
                book.setState(State.SMEARED);
                return;
            }
        }
        System.out.println("No such book!");
    }
}
