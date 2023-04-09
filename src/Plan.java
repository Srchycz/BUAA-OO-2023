import java.util.LinkedList;

public class Plan {
    private final int start;

    private final int destination;

    private LinkedList<Integer> list;

    public Plan(Request request) {
        this.start = request.getStart();
        this.destination = request.getDestination();
    }

    public void setList(LinkedList<Integer> list) {
        this.list = list;
    }

    public void remove() {
        list.removeFirst();
    }

    public int getNext() {
        assert (!list.isEmpty());
        return list.getFirst();
    }

}