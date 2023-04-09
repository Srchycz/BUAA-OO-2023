import java.util.ArrayList;

public class Dispatcher {
    private ArrayList<ElevatorThread> elevatorThreads;

    public void assignRequest(Request request) {
        int s = request.getStart();
        int t = request.getNext();
        for (ElevatorThread elevatorThread : elevatorThreads) {
            if (elevatorThread.isAccess(s) && elevatorThread.isAccess(t)) {
                elevatorThread.getWaitqueue().addRequest(request);
                return;
            }
        }
        System.out.println("Fail in distribute request!");
    }
}
