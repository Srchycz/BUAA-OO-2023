import com.oocourse.elevator2.TimableOutput;

import java.util.ArrayList;

public class Main {
    public static void main(String[] args) {
        TimableOutput.initStartTimestamp();
        RequestQueue requestQueue = new RequestQueue();
        ArrayList<ElevatorThread> elevatorThreads = new ArrayList<>();
        for (int i = 1; i <= 6; i++) {
            ElevatorThread elevatorThread = new ElevatorThread(i, requestQueue);
            elevatorThreads.add(elevatorThread);
            elevatorThread.start();
        }
        InputThread inputThread = new InputThread(requestQueue, elevatorThreads);
        inputThread.start();
    }
}