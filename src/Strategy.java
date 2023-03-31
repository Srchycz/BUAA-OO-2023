public class Strategy {
    private final Elevator elevator;

    private final RequestQueue requestQueue;

    public Strategy(Elevator elevator, RequestQueue requestQueue) {
        this.elevator = elevator;
        this.requestQueue = requestQueue;
    }

    public Direction getSuggestion() {
        if (elevator.getNum() == 0) {
            Request request = requestQueue.getTop();
            if (request == null) {
                return Direction.STAY;
            }
            else {
                if (request.getStart() > elevator.getFloor()) {
                    return Direction.UP;
                }
                else if (request.getStart() < elevator.getFloor()) {
                    return Direction.DOWN;
                }
                else { return Direction.STAY; }
            }
        }
        else {
            return elevator.getDirection();
        }
    }

}
