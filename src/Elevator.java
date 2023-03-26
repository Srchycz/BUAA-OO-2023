import com.oocourse.elevator1.TimableOutput;

import java.util.ArrayList;
import java.util.Iterator;

public class Elevator {
    private static final int MaxFloor = 11;
    private static final int MinFloor = 1;
    private final int id;

    private long lastTime;

    private int floor;

    private final ArrayList<Request> requests;

    public Elevator(int id) {
        this.id = id;
        this.floor = 1;
        this.requests = new ArrayList<>();
        this.lastTime = System.currentTimeMillis();
    }

    public int getId() {
        return id;
    }

    public int getNum() {
        return requests.size();
    }

    public int getFloor() {
        return floor;
    }

    public long getLastTime() {
        return lastTime;
    }

    public void up() {
        if (floor == MaxFloor) {
            System.out.println("OUT OF CEIL!");
            System.exit(0);
        }
        ++ floor;
        TimableOutput.println(String.format("ARRIVE-%d-%d", floor, id));
        lastTime = System.currentTimeMillis();
    }

    public void down() {
        if (floor == MinFloor) {
            System.out.println("BREAK THE LOWER LIMIT!");
            System.exit(0);
        }
        -- floor;
        TimableOutput.println(String.format("ARRIVE-%d-%d", floor, id));
        lastTime = System.currentTimeMillis();
    }

    public void open() {
        TimableOutput.println(String.format("OPEN-%d-%d", floor, id));
    }

    public void close() {
        TimableOutput.println(String.format("CLOSE-%d-%d", floor, id));
        lastTime = System.currentTimeMillis();
    }

    public int numOfOut() {
        int cnt = 0;
        for (Request request : requests) {
            if (request.getDestination() == floor) {
                ++cnt;
            }
        }
        return cnt;
    }

    public void getoff() {
        Iterator<Request> iter = requests.iterator();
        while (iter.hasNext()) {
            Request r = iter.next();
            if (r.getDestination() == floor) {
                iter.remove();
                TimableOutput.println(String.format(
                        "OUT-%d-%d-%d", r.getPersonID(), r.getDestination(), id));
            }
        }
    }

    public void geton(Request request) {
        assert (request.getStart() == floor);
        requests.add(request);
        TimableOutput.println(String.format(
                "IN-%d-%d-%d", request.getPersonID(), request.getStart(), id));
    }

    public Direction getDirection() {
        if (requests.isEmpty()) {
            return Direction.STAY;
        }
        if (requests.get(0).getDestination() > floor) {
            return Direction.UP;
        }
        else {
            return Direction.DOWN;
        }
    }
}
