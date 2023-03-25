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
                if (request.getDestination() > elevator.getFloor()) {
                    return Direction.UP;
                }
                else {
                    return Direction.DOWN;
                }
            }
        }
        else {
            return elevator.getDirection();
        }
    }

}
