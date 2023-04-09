import java.util.ArrayList;

public class RequestQueue {

    private boolean isEnd;
    private final ArrayList<Request> requests;

    private int cnt;

    public RequestQueue() {
        requests = new ArrayList<>();
        this.isEnd = false;
        this.cnt = 0;
    }

    public synchronized void addRequest(Request request) {
        requests.add(request);
        ++cnt;
        notifyAll();
    }

    public synchronized void subCnt(int t) {
        cnt = cnt - t;
        assert (cnt >= 0);
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

    public synchronized boolean isFinish() { return isEnd & (cnt == 0); }

    public synchronized Request getOneRequest() { // judge pick up
        while (requests.isEmpty() && !isEnd()) {
            try {
                wait();
            } catch (InterruptedException e) {
                throw new RuntimeException(e);
            }
        }
        if (requests.isEmpty()) {
            notifyAll();
            return null;
        }
        Request request = requests.get(0);
        requests.remove(0);
        notifyAll();
        return request;
    }

}
