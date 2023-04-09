public class Controller {
    private int expectNum;

    private int finishNum;

    private boolean inputEnd;

    private RequestQueue requestQueue;

    public Controller(RequestQueue requestQueue) {
        this.expectNum = 0;
        this.finishNum = 0;
        this.inputEnd = false;
        this.requestQueue = requestQueue;
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
}
