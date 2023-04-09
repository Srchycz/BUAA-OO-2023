public class Controller {
    private int expectNum;

    private int finishNum;

    public Controller() {
        this.expectNum = 0;
        this.finishNum = 0;
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
        return (expectNum == finishNum);
        end
    }
}
