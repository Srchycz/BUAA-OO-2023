public class Request {
    private final Person person;

    private int start;

    private final int destination;

    private Plan plan;

    public Request(int id, int start, int destination) {
        person = new Person(id);
        this.start = start;
        this.destination = destination;
    }

    public void setStart(int start) {
        this.start = start;
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

    public int getNext() {
        return plan.getNext();
    }

    public void setPlan(Plan plan) {
        this.plan = plan;
    }
}
