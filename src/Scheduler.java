import java.util.ArrayList;

public class Scheduler extends Thread{
    private final ArrayList<ElevatorThread> elevatorThreadArrayList;

    private final RequestQueue requestQueue;

    private Planner planner;

    private Controller controller;

    public Scheduler(RequestQueue requestQueue, Controller controller) {
        this.requestQueue = requestQueue;
        elevatorThreadArrayList = new ArrayList<>();
        this.controller = controller;
    }

    @Override
    public void run(){
        while (true) {
            if (requestQueue.isEnd() && controller.isFinish()) {
                break;
            }
            Request request = requestQueue.getOneRequest();
            if (request == null) continue;
            Plan plan = planner.getPlan(request);
            request.setPlan(plan);

        }
    }

    public void addElevator(ElevatorThread e) {
        elevatorThreadArrayList.add(e);
    }
}
