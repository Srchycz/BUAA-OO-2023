import java.util.ArrayList;
import java.util.concurrent.atomic.AtomicBoolean;

public class ElevatorThread extends Thread {
    private final Elevator elevator;

    private final RequestQueue waitqueue;

    private final Strategy strategy;

    private AtomicBoolean toMaintain;

    public ElevatorThread(int id, RequestQueue waitqueue, int capacity, double speed, int floor) {
        this.elevator = new Elevator(id, capacity, speed, floor);
        this.waitqueue = waitqueue;
        this.strategy = new Strategy(elevator, waitqueue);
        toMaintain = new AtomicBoolean(false);
    }

    public ElevatorThread(int id, RequestQueue waitqueue) {
        this.elevator = new Elevator(id);
        this.waitqueue = waitqueue;
        this.strategy = new Strategy(elevator, waitqueue);
        toMaintain = new AtomicBoolean(false);
    }

    public void setMaintain() {
        toMaintain.set(true);
    }

    public int getElevatorId() {
        return elevator.getId();
    }

    @Override
    public void run() {
        while (true) {
            if (toMaintain.get()) {
                Maintain();
                break;
            }
            if (waitqueue.isFinish() && elevator.getNum() == 0 && waitqueue.isEmpty()) {
                break;
            }
            if (elevator.numOfOut() > 0) {
                exchange();
            }
            else if (elevator.getNum() < elevator.getCapacity()) {
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
        waitqueue.subCnt(elevator.numOfOut());
        elevator.getoff();
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
            waitqueue.subCnt(elevator.numOfOut());
            ArrayList<Request> requests = elevator.clean();
            for (Request request : requests) {
                waitqueue.addRequest(request);
            }
            waitqueue.subCnt(requests.size());
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
