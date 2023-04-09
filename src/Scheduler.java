import java.util.ArrayList;

public class Scheduler extends Thread {
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
    public void run() {
        while (true) {
            /*
            if (requestQueue.isEnd()) {
                synchronized (elevatorThreadArrayList) {
                    for (ElevatorThread elevatorThread : elevatorThreadArrayList) {
                        elevatorThread.getWaitqueue().setEnd();
                    }
                }
            }*/
            if (controller.isFinish()) {
                synchronized (elevatorThreadArrayList) {
                    for (ElevatorThread elevatorThread : elevatorThreadArrayList) {
                        elevatorThread.getWaitqueue().setEnd();
                    }
                }
                //System.out.println("scheduler is finish");
                break;
            }
            Request request = requestQueue.getOneRequest();
            if (request == null) { continue; }
            assignRequest(request);
        }
    }

    public void assignRequest(Request request) {
        int s = request.getStart();
        int t = request.getNext();
        int num = 100;
        ElevatorThread aim = null;
        synchronized (elevatorThreadArrayList) {
            for (ElevatorThread elevatorThread : elevatorThreadArrayList) {
                if (elevatorThread.isAccess(s) && elevatorThread.isAccess(t)) {
                    if (elevatorThread.getNum() == 0) {
                        //System.out.println("distribute " + request.getPersonID() +
                        //" to "+ elevatorThread.getElevatorId());
                        elevatorThread.getWaitqueue().addRequest(request);
                        return;
                    }
                    else if (elevatorThread.getNum() < num) {
                        aim = elevatorThread;
                        num = elevatorThread.getNum();
                    }
                }
            }
        }
        if (aim != null) {
            aim.getWaitqueue().addRequest(request);
            return;
        }
        Plan plan = planner.getPlan(request);
        request.setPlan(plan);
        synchronized (elevatorThreadArrayList) {
            for (ElevatorThread elevatorThread : elevatorThreadArrayList) {
                if (elevatorThread.isAccess(s) && elevatorThread.isAccess(t)) {
                    if (elevatorThread.getNum() == 0) {
                        elevatorThread.getWaitqueue().addRequest(request);
                        return;
                    }
                    else if (elevatorThread.getNum() < num) {
                        aim = elevatorThread;
                        num = elevatorThread.getNum();
                    }
                }
            }
        }
        if (aim != null) {
            aim.getWaitqueue().addRequest(request);
            return;
        }
        System.out.println("Fail in distribute request!");
        assignRequest(request);
    }

    public Planner getPlanner() {
        return this.planner;
    }
}
