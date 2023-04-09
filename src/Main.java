import com.oocourse.elevator3.TimableOutput;

import java.util.ArrayList;

public class Main {
    public static void main(String[] args) {
        TimableOutput.initStartTimestamp();
        Controller controller = new Controller();
        RequestQueue requestQueue = new RequestQueue();
        ArrayList<ElevatorThread> elevatorThreads = new ArrayList<>();
        for (int i = 1; i <= 6; i++) {
            ElevatorThread elevatorThread = new ElevatorThread(i, controller, requestQueue);
            elevatorThreads.add(elevatorThread);
            elevatorThread.start();
        }
        Scheduler scheduler = new Scheduler(requestQueue, controller, elevatorThreads);
        scheduler.start();
        InputThread inputThread = new InputThread(requestQueue,
                elevatorThreads, controller, scheduler.getPlanner());
        inputThread.start();
    }
}