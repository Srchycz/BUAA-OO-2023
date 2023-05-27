import java.util.LinkedList;

// This is a singleton class. It is a class that can only have one instance.
public class LogisticsDivision implements Collectible {

    private LogisticsDivision() {
        strandedBooks = new LinkedList<>();
    }

    private static class LogisticsDivisionHolder {
        private static final LogisticsDivision INSTANCE = new LogisticsDivision();
    }

    public static LogisticsDivision getInstance() {
        return LogisticsDivisionHolder.INSTANCE;
    }

    private LinkedList<Book> strandedBooks;

    @Override
    public LinkedList<Book> recycleBook() {
        LinkedList<Book> books = strandedBooks;
        strandedBooks = new LinkedList<>();
        return books;
    }

    public void restoreBook(Book book) {
        book.setState(State.NORMAL);
        strandedBooks.add(book);
        //[YYYY-mm-dd] <类别号-序列号> got repaired by <服务部门>
        System.out.println(Calendar.getInstance().getDate() + " " +
                book.getBookInfo() + " got repaired by logistics division");
    }
}
