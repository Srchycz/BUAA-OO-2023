public class Strategy {
    private final Elevator elevator;

    private final PreQueue requestQueue;

    public Strategy(Elevator elevator, PreQueue requestQueue) {
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

    /*
    public int getCost() {
        int cnt = 0, lim = 12;
        int[] v = new int[12];
        Arrays.fill(v, 0);
        for(Request r: requestQueue) {
            int des = r.getDestination();
            lim = Math.max(Math.abs(des - elevator.getFloor()), lim);
            if (v[des] == 0)
                ++ cnt;
            v[des] = 1;
        }
        return lim * ((int)elevator.getMoveTime() / 100) + cnt * 4;
    }*/
}
