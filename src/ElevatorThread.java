import java.util.ArrayList;

public class ElevatorThread extends Thread {
    private final Elevator elevator;

    private final RequestQueue waitqueue;

    private final Strategy strategy;

    public ElevatorThread(int id, RequestQueue waitqueue) {
        this.elevator = new Elevator(id);
        this.waitqueue = waitqueue;
        this.strategy = new Strategy(elevator, waitqueue);
    }

    @Override
    public void run() {
        while (true) {
            if (waitqueue.isEnd() && elevator.getNum() == 0 && waitqueue.isEmpty()) {
                break;
            }
            if (elevator.numOfOut() > 0) {
                exchange();
            }
            else if (elevator.getNum() < 6) {
                checkPickup();
            }
            Direction d = strategy.getSuggestion();
            long currentTime = System.currentTimeMillis();
            switch (d) {
                case UP: {
                    try {
                        sleep(Math.max(400 - currentTime + elevator.getLastTime(), 0));
                    } catch (InterruptedException e) {
                        throw new RuntimeException(e);
                    }
                    elevator.up();
                    break;
                }
                case DOWN: {
                    try {
                        sleep(Math.max(400 - currentTime + elevator.getLastTime(), 0));
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
        while (elevator.getNum() < 6) {
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
        for (int i = elevator.getNum(); i < 6; ++ i) {
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

}
