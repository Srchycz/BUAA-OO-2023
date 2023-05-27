import java.util.LinkedList;

// This is a singleton class. It is a class that can only have one instance.
public class SelfServiceMachine implements Collectible, Registrable {

    private SelfServiceMachine() {
        strandedBooks = new LinkedList<>();
    }

    private static class SelfServiceMachineHolder {
        private static final SelfServiceMachine INSTANCE = new SelfServiceMachine();
    }

    public static SelfServiceMachine getInstance() {
        return SelfServiceMachineHolder.INSTANCE;
    }

    private LinkedList<Book> strandedBooks;

    @Override
    public LinkedList<Book> recycleBook() {
        LinkedList<Book> books = strandedBooks;
        strandedBooks = new LinkedList<>();
        return books;
    }

    public Boolean queryBook(Type type, String id, Student student) {
        //[YYYY-mm-dd] <学号> queried <类别号-序列号> from <服务部门>
        System.out.println(Calendar.getInstance().getDate() + " " + student.getId() +
                " queried " + type + "-" + id + " from self-service machine");
        return Bookshelf.getInstance().hasBook(type, id);
    }

    public void loanBook(Type type, String id, Student student) {
        assert type == Type.C;
        Book book = Bookshelf.getInstance().tryGetBook(type, id);
        if (student.hasBook(type, id)) {
            strandedBooks.add(book);
        }
        else {
            //[YYYY-mm-dd] <学号> borrowed <类别号-序列号> from <服务部门>
            System.out.println(Calendar.getInstance().getDate() + " " + student.getId() +
                    " borrowed " + type + "-" + id + " from self-service machine");
            student.addBook(book);
        }
    }

    public void tryReturnBook(Type type, String id, Student student) {
        assert type == Type.C;
        Book book = student.removeBook(type, id);
        switch (book.getState()) {
            case NORMAL:
                returnBook(book, student);
                strandedBooks.add(book);
                break;
            case SMEARED:
                CirculationDesk.getInstance().payFine(student);
                returnBook(book, student);
                LogisticsDivision.getInstance().restoreBook(book);
                break;
            default:
                System.out.println("Error: Invalid book state.");
                break;
        }
    }

    private void returnBook(Book book, Student student) {
        //[YYYY-mm-dd] <学号> returned <类别号-序列号> to <服务部门>
        System.out.println(Calendar.getInstance().getDate() + " " + student.getId() +
                " returned " + book.getBookInfo() + " to self-service machine");
    }
}
