import java.util.concurrent.Semaphore;

public class Controller {
    private int expectNum;

    private int finishNum;

    private boolean inputEnd;

    private RequestQueue requestQueue;

    private final Semaphore[] onlyPick;

    private final Semaphore[] serve;

    public Controller(RequestQueue requestQueue) {
        this.expectNum = 0;
        this.finishNum = 0;
        this.inputEnd = false;
        this.requestQueue = requestQueue;
        this.onlyPick = new Semaphore[12];
        this.serve = new Semaphore[12];
        for (int i = 1; i <= 11; ++ i) {
            onlyPick[i] = new Semaphore(2);
            serve[i] = new Semaphore(4);
        }
    }

    public synchronized void setInputEnd() {
        this.inputEnd = true;
        if (isFinish()) {
            requestQueue.setRealEnd();
        }
    }

    public synchronized void addExpectNum() {
        ++expectNum;
    }

    public synchronized void addFinishNum() {
        ++finishNum;
    }

    public synchronized void addFinishNum(int x) {
        finishNum = finishNum + x;
        //System.out.println(finishNum);
        if (isFinish()) {
            //System.out.println("yes");
            requestQueue.setRealEnd();
        }
    }

    public synchronized boolean isFinish() {
        assert (expectNum >= finishNum);
        return (expectNum == finishNum) && inputEnd;
    }

    public void Print() {
        System.out.println("ExpectNum : " + expectNum +
                "  FinishNum : " + finishNum + " isInputEnd : " + inputEnd);
    }

    public void onlyPick(int floor) {
        try {
            onlyPick[floor].acquire();
            serve[floor].acquire();
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
    }

    public void onlyPickRelease(int floor) {
        onlyPick[floor].release();
        serve[floor].release();
    }

    public void serve(int floor) {
        try {
            serve[floor].acquire();
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
    }

    public void serveRelease(int floor) {
        serve[floor].release();
    }
}
