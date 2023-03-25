import com.oocourse.elevator1.ElevatorInput;
import com.oocourse.elevator1.PersonRequest;

public class InputThread extends Thread {
    private final ElevatorInput elevatorInput;

    private final RequestQueue requestQueue;

    public InputThread(RequestQueue requestQueue) {
        this.requestQueue = requestQueue;
        elevatorInput = new ElevatorInput(System.in);
    }

    @Override
    public void run() {
        while (true) {
            PersonRequest request = elevatorInput.nextPersonRequest();

            if (request == null) {
                requestQueue.setEnd();
                break;
            } else {
                Request r = new Request(request.getPersonId(),
                        request.getFromFloor(), request.getToFloor());
                requestQueue.addRequest(r);
            }
        }
    }

}
