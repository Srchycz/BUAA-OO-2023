import java.util.LinkedList;

public class Collector {
    public static void RecycleBook() {
        LinkedList<Book> recycleBooks = new LinkedList<>();
        recycleBooks.addAll(CirculationDesk.getInstance().recycleBook());
        recycleBooks.addAll(SelfServiceMachine.getInstance().recycleBook());
        recycleBooks.addAll(LogisticsDivision.getInstance().recycleBook());
        ReservationDesk.getInstance().arrange(recycleBooks);
        Bookshelf.getInstance().addBooks(recycleBooks);
    }
}
