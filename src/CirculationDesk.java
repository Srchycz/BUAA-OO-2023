import java.util.LinkedList;

// This is a singleton class. It is a class that can only have one instance.
public class CirculationDesk implements Collectible, Registrable {

    private CirculationDesk() {
        strandedBooks = new LinkedList<>();
    }

    private static class CirculationDeskHolder {
        private static final CirculationDesk INSTANCE = new CirculationDesk();
    }

    public static CirculationDesk getInstance() {
        return CirculationDeskHolder.INSTANCE;
    }

    private LinkedList<Book> strandedBooks;

    @Override
    public LinkedList<Book> recycleBook() {
        LinkedList<Book> books = strandedBooks;
        strandedBooks = new LinkedList<>();
        return books;
    }

    public void loanBook(Type type, String id, Student student) {
        assert type == Type.B;
        Book book = Bookshelf.getInstance().tryGetBook(type, id);
        if (student.hasTypeBook(type)) {
            strandedBooks.add(book);
        }
        else {
            //[YYYY-mm-dd] <学号> borrowed <类别号-序列号> from <服务部门>
            System.out.println(Calendar.getInstance().getDate() + " " + student.getId() +
                    " borrowed " + type + "-" + id + " from borrowing and returning librarian");
            student.addBook(book);
            ReservationDesk.getInstance().cancelOrder(type, student);
        }
    }

    public void tryReturnBook(Type type, String id, Student student) {
        assert type == Type.B;
        Book book = student.removeBook(type, id);
        switch (book.getState()) {
            case NORMAL:
                returnBook(book, student);
                strandedBooks.add(book);
                break;
            case SMEARED:
                payFine(student);
                returnBook(book, student);
                LogisticsDivision.getInstance().restoreBook(book);
                break;
            case LOST:
                payFine(student);
                break;
            default:
                System.out.println("Error: Invalid book state.");
                break;
        }
    }

    private void returnBook(Book book, Student student) {
        //[YYYY-mm-dd] <学号> returned <类别号-序列号> to <服务部门>
        System.out.println(Calendar.getInstance().getDate() + " " + student.getId() +
                " returned " + book.getBookInfo() + " to borrowing and returning librarian");
    }

    public void payFine(Student student) {
        //[YYYY-mm-dd] <学号> got punished by <服务部门>
        System.out.println(Calendar.getInstance().getDate() + " " + student.getId() +
                " got punished by borrowing and returning librarian");
    }
}
