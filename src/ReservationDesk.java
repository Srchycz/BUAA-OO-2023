import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Objects;

//Singleton
public class ReservationDesk {
    private ReservationDesk() {
        requestsB = new LinkedList<>();
        requestsC = new LinkedList<>();
        count = new HashMap<>();
        date = null;
    }

    private static class ReservationDeskHolder {
        private static final ReservationDesk INSTANCE = new ReservationDesk();
    }

    public static ReservationDesk getInstance() {
        return ReservationDeskHolder.INSTANCE;
    }

    private final LinkedList<Request> requestsB;
    private final LinkedList<Request> requestsC;
    private final HashMap<Student, Integer> count;
    private String date;

    public void tryOrder(Type type, String id, Student student) {
        //[YYYY-mm-dd] <学号> ordered <类别号-序列号> from <服务部门>
        if (type == Type.B) {
            if (!student.hasTypeBook(Type.B) && isValid(student)
                    && !hasBook(Type.B, id, student)) {
                System.out.println(Calendar.getInstance().getDate() + " " + student.getId() +
                        " ordered " + type + "-" + id + " from ordering librarian");
                requestsB.addLast(new Request(id, student, Type.B));
                addCount(student);
            }
        }
        else if (type == Type.C) {
            if (!student.hasBook(Type.C, id) && isValid(student)
                    && !hasBook(Type.C, id, student)) {
                System.out.println(Calendar.getInstance().getDate() + " " + student.getId() +
                        " ordered " + type + "-" + id + " from ordering librarian");
                requestsC.addLast(new Request(id, student, Type.C));
                addCount(student);
            }
        }
    }

    private Boolean isValid(Student student) {
        if (date == null || !Calendar.getInstance().getDate().equals(date)) {
            count.clear();
            date = Calendar.getInstance().getDate();
        }
        if (count.containsKey(student)) {
            return count.get(student) <= 2;
        }
        else {
            return true;
        }
    }

    private Boolean hasBook(Type type, String id, Student student) {
        if (type == Type.B) {
            for (Request request : requestsB) {
                if (Objects.equals(request.getId(), id) &&
                        Objects.equals(request.getStudent(), student)) {
                    return true;
                }
            }
        }
        else {
            for (Request request : requestsC) {
                if (Objects.equals(request.getId(), id) &&
                        Objects.equals(request.getStudent(), student)) {
                    return true;
                }
            }
        }
        return false;
    }

    private void addCount(Student student) {
        count.put(student, count.getOrDefault(student, 0) + 1);
    }

    public void arrange(LinkedList<Book> books) {
        Iterator<Book> iterator = books.iterator();
        while (iterator.hasNext()) {
            Book book = iterator.next();
            if (book.getType() == Type.B) {
                for (Request request : requestsB) {
                    if (Objects.equals(request.getId(), book.getId())) {
                        //[YYYY-mm-dd] <学号> borrowed <类别号-序列号> from <服务部门>
                        System.out.println(Calendar.getInstance().getDate() + " " +
                                request.getStudent().getId() + " borrowed " + book.getBookInfo() +
                                " from ordering librarian");
                        request.getStudent().addBook(book);
                        cancelOrder(Type.B, request.getStudent());
                        iterator.remove();
                        break;
                    }
                }
            }
            else {
                Iterator<Request> iterator1 = requestsC.iterator();
                while (iterator1.hasNext()) {
                    Request request = iterator1.next();
                    if (Objects.equals(request.getId(), book.getId())) {
                        //[YYYY-mm-dd] <学号> borrowed <类别号-序列号> from <服务部门>
                        System.out.println(Calendar.getInstance().getDate() + " " +
                                request.getStudent().getId() + " borrowed " + book.getBookInfo() +
                                " from ordering librarian");
                        request.getStudent().addBook(book);
                        iterator.remove();
                        iterator1.remove();
                        break;
                    }
                }
            }
        }
    }

    public void cancelOrder(Type type, String id, Student student) {
        assert type == Type.C;
        Iterator<Request> iterator = requestsC.iterator();
        while (iterator.hasNext()) {
            Request request = iterator.next();
            if (Objects.equals(request.getId(), id) &&
                    Objects.equals(request.getStudent(), student)) {
                iterator.remove();
                break;
            }
        }
    }

    public void cancelOrder(Type type, Student student) {
        assert type == Type.B;
        requestsB.removeIf(request -> Objects.equals(request.getStudent(), student));
    }
}
