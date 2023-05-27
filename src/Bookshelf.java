import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;

// This is a singleton class. It is a class that can only have one instance.
public class Bookshelf {

    private Bookshelf() {
        books = new ArrayList<>(Type.values().length);
        for (int i = 0; i < Type.values().length; i++) {
            books.add(new HashMap<>());
        }
    }

    private static final Bookshelf INSTANCE = new Bookshelf();

    public static Bookshelf getInstance() {
        return INSTANCE;
    }

    private final ArrayList<HashMap<String, Book>> books;

    public Book tryGetBook(Type type, String id) {
        return books.get(type.ordinal()).get(id).getOne();
    }

    public Boolean hasBook(Type type, String id) {
        return books.get(type.ordinal()).containsKey(id) &&
                books.get(type.ordinal()).get(id).getNumber() > 0;
    }

    public void addBooks(LinkedList<Book> bookList) {
        for (Book book : bookList) {
            addBook(book);
        }
    }

    public void addBook(Book book) {
        assert book.getState() == State.NORMAL;
        books.get(book.getType().ordinal()).get(book.getId()).add();
    }

    public void addNewBook(Type type, String id, int number) {
        assert !books.get(type.ordinal()).containsKey(id);
        books.get(type.ordinal()).put(id, new Book(type, id, number));
    }
}