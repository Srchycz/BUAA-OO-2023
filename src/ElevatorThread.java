import java.util.ArrayList;
import java.util.concurrent.atomic.AtomicBoolean;

public class ElevatorThread extends Thread {
    private final Elevator elevator;

    private final PreQueue waitqueue;

    private final RequestQueue requestQueue;

    private final Strategy strategy;

    private AtomicBoolean toMaintain;

    private Controller controller;

    public ElevatorThread(int id, int capacity, double speed, int floor, int access,
                          Controller controller, RequestQueue requestQueue) {
        this.elevator = new Elevator(id, capacity, speed, floor, access);
        this.waitqueue = new PreQueue();
        this.strategy = new Strategy(elevator, waitqueue);
        toMaintain = new AtomicBoolean(false);
        this.controller = controller;
        this.requestQueue = requestQueue;
    }

    public ElevatorThread(int id, Controller controller, RequestQueue requestQueue) {
        this.elevator = new Elevator(id);
        this.waitqueue = new PreQueue();
        this.strategy = new Strategy(elevator, waitqueue);
        toMaintain = new AtomicBoolean(false);
        this.controller = controller;
        this.requestQueue = requestQueue;
    }

    public void setMaintain() {
        toMaintain.set(true);
    }

    public int getElevatorId() {
        return elevator.getId();
    }

    public boolean isAccess(int floor) { return elevator.isAccess(floor); }

    public PreQueue getWaitqueue() {
        return this.waitqueue;
    }

    public Elevator getElevator() {
        return this.elevator;
    }

    @Override
    public void run() {
        while (true) {
            if (toMaintain.get()) {
                Maintain();
                break;
            }
            if (controller.isFinish() && elevator.getNum() == 0 && waitqueue.isEmpty()) {
                break;
            }
            if (elevator.numOfOut() > 0) {
                assert (isAccess(elevator.getFloor()));
                exchange();
            }
            else if (elevator.getNum() < elevator.getCapacity() && isAccess(elevator.getFloor())) {
                checkPickup();
            }
            Direction d = strategy.getSuggestion();
            long currentTime = System.currentTimeMillis();
            switch (d) {
                case UP: {
                    try {
                        sleep(Math.max(elevator.getMoveTime() -
                                currentTime + elevator.getLastTime(), 0));
                    } catch (InterruptedException e) {
                        throw new RuntimeException(e);
                    }
                    elevator.up();
                    break;
                }
                case DOWN: {
                    try {
                        sleep(Math.max(elevator.getMoveTime() -
                                currentTime + elevator.getLastTime(), 0));
                    } catch (InterruptedException e) {
                        throw new RuntimeException(e);
                    }
                    elevator.down();
                    break;
                }
                default: { }
            }
        }
    }

    private void exchange() {
        elevator.open();
        try {
            sleep(200);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
        //waitqueue.subCnt(elevator.numOfOut());
        controller.addFinishNum(elevator.numOfFinish());
        elevator.getoff();
        ArrayList<Request> requests = elevator.getoff();
        for (Request request : requests) {
            requestQueue.addRequest(request);
        }
        while (elevator.getNum() < elevator.getCapacity()) {
            Request request = waitqueue.getRequest(elevator.getFloor(), elevator.getDirection());
            if (request == null) {
                break;
            }
            elevator.geton(request);
        }
        try {
            sleep(200);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
        elevator.close();
    }

    private void checkPickup() {
        ArrayList<Request> pickRequest = new ArrayList<>();
        for (int i = elevator.getNum(); i < elevator.getCapacity(); ++ i) {
            Request request = waitqueue.getRequest(elevator.getFloor(), elevator.getDirection());
            if (request == null) {
                break;
            }
            pickRequest.add(request);
        }
        if (!pickRequest.isEmpty()) {
            elevator.open();
            try {
                sleep(200);
            } catch (InterruptedException e) {
                throw new RuntimeException(e);
            }
            for (Request request : pickRequest) {
                elevator.geton(request);
            }
            try {
                sleep(200);
            } catch (InterruptedException e) {
                throw new RuntimeException(e);
            }
            elevator.close();
        }
    }

    private void Maintain() {
        if (elevator.getNum() > 0) {
            elevator.open();
            try {
                sleep(200);
            } catch (InterruptedException e) {
                throw new RuntimeException(e);
            }
            //waitqueue.subCnt(elevator.numOfOut());
            controller.addFinishNum(elevator.numOfFinish());
            ArrayList<Request> requests = elevator.clean();
            for (Request request : requests) {
                requestQueue.addRequest(request);
            }
            //waitqueue.subCnt(requests.size());
            try {
                sleep(200);
            } catch (InterruptedException e) {
                throw new RuntimeException(e);
            }
            elevator.close();
        }
        elevator.Maintain();
    }

}
