import java.util.ArrayList;

public class Scheduler extends Thread{
    private ArrayList<ElevatorThread> elevatorThreadArrayList;

    private RequestQueue requestQueue;

    private Planner planner;

    public Scheduler(RequestQueue requestQueue) {
        this.requestQueue = requestQueue;
        elevatorThreadArrayList = new ArrayList<>();
    }

    @Override
    public void run(){
        while (true) {
            if (requestQueue.isEnd() && /*all request is finished*/) {
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
