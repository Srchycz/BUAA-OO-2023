import java.util.ArrayList;

public class RequestQueue {

    private boolean isEnd;
    private final ArrayList<Request> requests;

    public RequestQueue() {
        requests = new ArrayList<>();
        this.isEnd = false;
    }

    public synchronized void addRequest(Request request) {
        requests.add(request);
        notifyAll();
    }

    public synchronized boolean isEnd() {
        return isEnd;
    }

    public synchronized boolean isEmpty() { return requests.isEmpty(); }

    public synchronized void setEnd() {
        this.isEnd = true;
        notifyAll();
    }

    public synchronized Request getRequest(int floor, Direction direction) { // judge pick up
        int idx = -1;
        for (int i = 0; i < requests.size(); ++ i) {
            if (requests.get(i).getStart() == floor) {
                if (direction == Direction.UP) {
                    if (requests.get(i).getDestination() > floor) {
                        idx = i;
                        break;
                    }
                    continue;
                }
                if (direction == Direction.DOWN) {
                    if (requests.get(i).getDestination() < floor) {
                        idx = i;
                        break;
                    }
                    continue;
                }
                idx = i;
                break;
            }
        }
        if (idx == -1) {
            notifyAll();
            return null;
        }
        Request request = requests.get(idx);
        requests.remove(idx);
        notifyAll();
        return request;
    }

    public synchronized Request getTop() {
        while (requests.isEmpty() && !isEnd) {
            try {
                wait();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
        if (requests.isEmpty()) {
            return null;
        }
        Request request = requests.get(0);
        notifyAll();
        return request;
    }

}
