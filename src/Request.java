public class Request {
    private final String id;
    private final Student student;
    private final Type type;

    public Request(String id, Student student, Type type) {
        this.id = id;
        this.student = student;
        this.type = type;
    }

    public String getId() {
        return id;
    }

    public Student getStudent() {
        return student;
    }

    public Type getType() {
        return type;
    }
}
