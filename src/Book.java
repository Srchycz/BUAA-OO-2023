public class Book {
    private State state;
    private final Type type;
    private final String id;
    private int number;

    public Book(Type type, String id, int number) {
        this.type = type;
        this.id = id;
        this.number = number;
        if (type == Type.A) {
            state = State.RESERVED;
        }
        else {
            state = State.NORMAL;
        }
    }

    public String getId() {
        return id;
    }

    public Type getType() {
        return type;
    }

    public int getNumber() {
        return number;
    }

    public Book getOne() {
        if (state != State.NORMAL) {
            System.out.println(getBookInfo() + "This book is not available!");
            return null;
        }
        if (number > 0) {
            number--;
            return new Book(type, id, 1);
        }
        else {
            System.out.println(getBookInfo() + "No book left!");
            return null;
        }
    }

    public String getBookInfo() {
        return String.format("%s-%s", type, id);
    }

    public void add() {
        ++ number;
    }

    public State getState() {
        return state;
    }

    public void setState(State state) {
        this.state = state;
    }
}
