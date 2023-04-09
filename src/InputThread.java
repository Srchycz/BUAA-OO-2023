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

    private final Controller controller;

    private final Planner planner;

    public InputThread(RequestQueue requestQueue, ArrayList<ElevatorThread> elevatorThreads,
                       Controller controller, Planner planner) {
        this.requestQueue = requestQueue;
        elevatorInput = new ElevatorInput(System.in);
        this.elevatorThreads = elevatorThreads;
        this.controller = controller;
        this.planner = planner;
    }

    @Override
    public void run() {
        while (true) {
            com.oocourse.elevator3.Request request = elevatorInput.nextRequest();

            if (request == null) {
                controller.setInputEnd();
                requestQueue.setEnd();
                break;
            } else {
                if (request instanceof PersonRequest) {
                    PersonRequest personRequest = (PersonRequest) request;
                    Request r = new Request(personRequest.getPersonId(),
                            personRequest.getFromFloor(), personRequest.getToFloor());
                    controller.addExpectNum();
                    requestQueue.addRequest(r);
                } else if (request instanceof ElevatorRequest) {
                    ElevatorRequest elevatorRequest = (ElevatorRequest) request;
                    ElevatorThread elevatorThread = new ElevatorThread(
                            elevatorRequest.getElevatorId(), elevatorRequest.getCapacity(),
                            elevatorRequest.getSpeed(), elevatorRequest.getAccess(),
                            elevatorRequest.getFloor(), controller, requestQueue);
                    synchronized (elevatorThreads) {
                        elevatorThreads.add(elevatorThread);
                    }
                    planner.add(elevatorThread.getElevator());
                    elevatorThread.start();
                } else if (request instanceof MaintainRequest) {
                    MaintainRequest maintainRequest = (MaintainRequest) request;
                    synchronized (elevatorThreads) {
                        Iterator<ElevatorThread> iter = elevatorThreads.iterator();
                        while (iter.hasNext()) {
                            ElevatorThread elevatorThread = iter.next();
                            if (elevatorThread.getElevatorId() == maintainRequest.getElevatorId()) {
                                planner.sub(elevatorThread.getElevator());
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

}
