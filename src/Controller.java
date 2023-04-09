public class Controller {
    private int expectNum;

    private int finishNum;

    private boolean inputEnd;

    public Controller() {
        this.expectNum = 0;
        this.finishNum = 0;
        this.inputEnd = false;
    }

    public synchronized void setInputEnd() {
        this.inputEnd = true;
    }

    public synchronized void addExpectNum() {
        ++expectNum;
    }

    public synchronized void addFinishNum() {
        ++finishNum;
    }

    public synchronized void addFinishNum(int x) {
        finishNum = finishNum + x;
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
