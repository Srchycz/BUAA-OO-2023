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

    public synchronized Request getOneRequest() { // judge pick up
        while (requests.isEmpty() && !isEnd()) {
            try {
                wait();
            } catch (InterruptedException e) {
                throw new RuntimeException(e);
            }
        }
        if (requests.isEmpty()) {
            return null;
        }
        Request request = requests.get(0);
        requests.remove(0);
        notifyAll();
        return request;
    }

}
