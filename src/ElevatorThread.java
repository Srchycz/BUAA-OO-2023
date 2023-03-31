import java.util.ArrayList;

public class ElevatorThread extends Thread {
    private final Elevator elevator;

    private final RequestQueue waitqueue;

    private final Strategy strategy;

    private boolean toMaintain;

    public ElevatorThread(int id, RequestQueue waitqueue, int capacity, double speed) {
        this.elevator = new Elevator(id, capacity, speed);
        this.waitqueue = waitqueue;
        this.strategy = new Strategy(elevator, waitqueue);
        this.toMaintain = false;
    }

    public void setMaintain() {
        this.toMaintain = true;
    }

    public int getElevatorId() {
        return elevator.getId();
    }

    @Override
    public void run() {
        while (true) {
            if (toMaintain) {
                Maintain();
                break;
            }
            if (waitqueue.isEnd() && elevator.getNum() == 0 && waitqueue.isEmpty()) {
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
            ArrayList<Request> requests = elevator.clean();
            for (Request request : requests) {
                waitqueue.addRequest(request);
            }
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
