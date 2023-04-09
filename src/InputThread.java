import com.oocourse.elevator3.ElevatorInput;
import com.oocourse.elevator3.ElevatorRequest;
import com.oocourse.elevator3.MaintainRequest;
import com.oocourse.elevator3.PersonRequest;

import java.util.ArrayList;
import java.util.Iterator;

public class InputThread extends Thread {
    private final ElevatorInput elevatorInput;

    private final RequestQueue requestQueue;

    private final ArrayList<ElevatorThread> elevatorThreads;

    public InputThread(RequestQueue requestQueue, ArrayList<ElevatorThread> elevatorThreads) {
        this.requestQueue = requestQueue;
        elevatorInput = new ElevatorInput(System.in);
        this.elevatorThreads = elevatorThreads;
    }

    @Override
    public void run() {
        while (true) {
            com.oocourse.elevator3.Request request = elevatorInput.nextRequest();

            if (request == null) {
                requestQueue.setEnd();
                break;
            } else {
                if (request instanceof PersonRequest) {
                    PersonRequest personRequest = (PersonRequest) request;
                    Request r = new Request(personRequest.getPersonId(),
                            personRequest.getFromFloor(), personRequest.getToFloor());
                    requestQueue.addRequest(r);
                } else if (request instanceof ElevatorRequest) {
                    ElevatorRequest elevatorRequest = (ElevatorRequest) request;

                } else if (request instanceof MaintainRequest) {
                    MaintainRequest maintainRequest = (MaintainRequest) request;
                    Iterator<ElevatorThread> iter = elevatorThreads.iterator();
                    while (iter.hasNext()) {
                        ElevatorThread elevatorThread = iter.next();
                        if (elevatorThread.getElevatorId() == maintainRequest.getElevatorId()) {
                            elevatorThread.setMaintain();
                            iter.remove();
                            break;
                        }
                    }
                }

            }
        }
    }

}
