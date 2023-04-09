import java.util.ArrayList;

public class Scheduler extends Thread{
    private final ArrayList<ElevatorThread> elevatorThreadArrayList;

    private final RequestQueue requestQueue;

    private Planner planner;

    private Controller controller;

    public Scheduler(RequestQueue requestQueue, Controller controller,
                     ArrayList<ElevatorThread> elevatorThreads) {
        this.requestQueue = requestQueue;
        elevatorThreadArrayList = elevatorThreads;
        this.controller = controller;
        this.planner = new Planner(elevatorThreads);
    }

    @Override
    public void run(){
        while (true) {
            if (requestQueue.isEnd()) {
                synchronized (elevatorThreadArrayList) {
                    for (ElevatorThread elevatorThread : elevatorThreadArrayList) {
                        elevatorThread.getWaitqueue().setEnd();
                    }
                }
            }
            if (controller.isFinish()) {
                synchronized (elevatorThreadArrayList) {
                    for (ElevatorThread elevatorThread : elevatorThreadArrayList) {
                        elevatorThread.getWaitqueue().setEnd();
                    }
                }
                break;
            }
            Request request = requestQueue.getOneRequest();
            if (request == null) continue;
            assignRequest(request);
        }
    }

    public void assignRequest(Request request) {
        int s = request.getStart();
        int t = request.getNext();
        synchronized (elevatorThreadArrayList) {
            for (ElevatorThread elevatorThread : elevatorThreadArrayList) {
                if (elevatorThread.isAccess(s) && elevatorThread.isAccess(t)) {
                    elevatorThread.getWaitqueue().addRequest(request);
                    return;
                }
            }
        }
        Plan plan = planner.getPlan(request);
        request.setPlan(plan);
        synchronized (elevatorThreadArrayList) {
            for (ElevatorThread elevatorThread : elevatorThreadArrayList) {
                if (elevatorThread.isAccess(s) && elevatorThread.isAccess(t)) {
                    elevatorThread.getWaitqueue().addRequest(request);
                    return;
                }
            }
        }
        System.out.println("Fail in distribute request!");
        assignRequest(request);
    }

    public Planner getPlanner() {
        return this.planner;
    }
}
