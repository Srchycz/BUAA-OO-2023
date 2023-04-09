import java.util.LinkedList;

public class Plan {
    private int start;

    private final int destination;

    private LinkedList<Integer> list;

    public Plan(Request request) {
        this.start = request.getStart();
        this.destination = request.getDestination();
    }

    public void setList(LinkedList<Integer> list) {
        this.list = list;
    }

    public int remove() {
        return start = list.removeFirst();
    }

    public int getNext() {
        assert (!list.isEmpty());
        return list.getFirst();
    }

    public void Print() {
        System.out.print(start);
        for(Integer i : list) {
            System.out.print(" -> " + i);
        }
        System.out.println();
    }

}