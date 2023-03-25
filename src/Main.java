import com.oocourse.elevator1.TimableOutput;

public class Main {
    public static void main(String[] args) {
        TimableOutput.initStartTimestamp();
        RequestQueue requestQueue = new RequestQueue();
        for (int i = 1; i <= 6; i++) {
            ElevatorThread elevatorThread = new ElevatorThread(i, requestQueue);
            elevatorThread.start();
        }
        InputThread inputThread = new InputThread(requestQueue);
        inputThread.start();
    }
}