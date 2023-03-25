public class Request {
    private final Person person;

    private final int start;

    private final int destination;

    public Request(int id, int start, int destination) {
        person = new Person(id);
        this.start = start;
        this.destination = destination;
    }

    public int getPersonID() {
        return person.getId();
    }

    public int getStart() {
        return start;
    }

    public int getDestination() {
        return destination;
    }
}
