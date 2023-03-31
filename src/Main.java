import com.oocourse.elevator2.TimableOutput;

import java.util.ArrayList;

public class Main {
    public static void main(String[] args) {
        TimableOutput.initStartTimestamp();
        RequestQueue requestQueue = new RequestQueue();
        ArrayList<ElevatorThread> elevatorThreads = new ArrayList<>();
        for (int i = 1; i <= 6; i++) {
            ElevatorThread elevatorThread = new ElevatorThread(i, requestQueue, 6, 0.4);
            elevatorThreads.add(elevatorThread);
            elevatorThread.start();
        }
        InputThread inputThread = new InputThread(requestQueue, elevatorThreads);
        inputThread.start();
    }
}
/*
1-FROM-2-TO-8
2-FROM-11-TO-3
3-FROM-3-TO-8
 */