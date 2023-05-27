import java.util.HashMap;

//Singleton class
public class Library {
    private Library() {
        count = 0;
        students = new HashMap<>();
        calendar = Calendar.getInstance();
        bookshelf = Bookshelf.getInstance();
        selfServiceMachine = SelfServiceMachine.getInstance();
        circulationDesk = CirculationDesk.getInstance();
        reservationDesk = ReservationDesk.getInstance();
    }

    private static final Library INSTANCE = new Library();

    public static Library getInstance() {
        return INSTANCE;
    }

    private final HashMap<String, Student> students;

    private final Calendar calendar;
    private int count;
    private final Bookshelf bookshelf;
    private final SelfServiceMachine selfServiceMachine;
    private final CirculationDesk circulationDesk;
    private final ReservationDesk reservationDesk;

    public void addNewBook(Type type, String id, int num) {
        bookshelf.addNewBook(type, id, num);
    }

    public void handle(String date, String studentId, Action action, String bookId, Type type) {
        updateCalendar(date);
        Student student = getStudent(studentId);
        switch (action) {
            case BORROW:
                tryBorrowBook(student, bookId, type);
                break;
            case LOSE:
                student.loseBook(type, bookId);
                circulationDesk.payFine(student);
                break;
            case SMEAR:
                student.smearBook(type, bookId);
                break;
            case RETURN:
                tryReturnBook(student, bookId, type);
                break;
            default:
                throw new RuntimeException("Invalid action");
        }
    }

    private void updateCalendar(String date) {
        assert date.matches("\\[\\d{4}-\\d{2}-\\d{2}]");
        while (calendar.getDate().compareTo(date) < 0) {
            calendar.nextDay();
            ++ count;
            if (count == 3) {
                Collector.RecycleBook();
                count = 0;
            }
        }
        if (calendar.getDate().compareTo(date) > 0) {
            throw new RuntimeException("Invalid date");
        }
    }

    private Student getStudent(String studentId) {
        students.putIfAbsent(studentId, new Student(studentId));
        return students.get(studentId);
    }

    private void tryBorrowBook(Student student, String id, Type type) {
        if (selfServiceMachine.queryBook(type, id, student)) {
            switch (type) {
                case A:
                    break;
                case B:
                    circulationDesk.loanBook(type, id, student);
                    break;
                case C:
                    selfServiceMachine.loanBook(type, id, student);
                    break;
                default:
                    throw new RuntimeException("Invalid type");
            }
        }
        else {
            orderBook(type, id, student);
        }
    }

    private void orderBook(Type type, String id, Student student) {
        reservationDesk.tryOrder(type, id, student);
    }

    private void tryReturnBook(Student student, String id, Type type) {
        switch (type) {
            case B:
                circulationDesk.tryReturnBook(type, id, student);
                break;
            case C:
                selfServiceMachine.tryReturnBook(type, id, student);
                break;
            default:
                throw new RuntimeException("Invalid type");
        }
    }
}
