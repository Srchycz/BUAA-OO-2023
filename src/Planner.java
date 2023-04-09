import java.util.ArrayList;
import java.util.LinkedList;

public class Planner {
    static final int MaxDist = 0xffff;
    private int[][] graph = new int[12][12];

    private int[][] pass = new int[12][12];

    private int[][] dist = new int[12][12];

    private boolean isUpdate;

    public Planner(ArrayList<ElevatorThread> elevators) {
        for (ElevatorThread elevator : elevators) {
            add(elevator.getElevator());
        }
        this.isUpdate = true;
    }

    private void init() {
        for (int i = 1; i <= 11; ++i) {
            for (int j = 1; j <= 11; ++j) {
                dist[i][j] = graph[i][j] > 0 ? 1 : MaxDist;
                pass[i][j] = 0;
            }
            dist[i][i] = 0;
        }
    }

    private synchronized void Floyd() {
        init();
        //Print();
        for (int k = 1; k <= 11; ++k) {
            for (int i = 1; i <= 11; ++i) {
                if (k == i) { continue; }
                for (int j = 1; j <= 11; ++j) {
                    if (k == j) { continue; }
                    if (dist[i][j] > dist[i][k] + dist[k][j]) {
                        dist[i][j] = dist[i][k] + dist[k][j];
                        pass[i][j] = k;
                    }
                }
            }
        }
        isUpdate = true;
    }

    public synchronized Plan getPlan(Request request) {
        int s = request.getStart();
        int t = request.getDestination();
        Plan plan = new Plan(request);
        LinkedList<Integer> list = new LinkedList<>();
        if (!isUpdate) {
            Floyd();
        }
        getPass(s, t, list);
        list.addLast(t);
        plan.setList(list);
        return plan;
    }

    private void getPass(int s, int t, LinkedList<Integer> list) {
        if (pass[s][t] == 0 || s == t) {
            return;
        }
        //System.out.println("s: " + s + " t: " + t + " pass :" + pass[s][t]);
        getPass(s, pass[s][t], list);
        list.addLast(pass[s][t]);
        getPass(pass[s][t], t, list);
    }

    public synchronized void add(Elevator elevator) {
        update(elevator, 1);
    }

    public synchronized void sub(Elevator elevator) {
        update(elevator, -1);
    }

    private synchronized void update(Elevator elevator, int k) {
        //elevator.Print();
        for (int i = 1; i <= 11; ++ i) {
            if (!elevator.isAccess(i)) { continue; }
            for (int j = 1; j <= 11; ++ j) {
                if (elevator.isAccess(j)) {
                    graph[i][j] += k;
                }
            }
        }
        isUpdate = false;
    }

    public synchronized void Print() {
        for (int i = 1; i <= 11; ++i) {
            for (int j = 1; j <= 11; ++j) {
                System.out.print(graph[i][j] + " ");
            }
            System.out.println();
        }
    }
}
