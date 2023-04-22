import java.util.HashMap;

public class Counter {
    private int total;

    private final HashMap<Integer, Integer> cnt;

    public Counter() {
        this.total = 0;
        this.cnt = new HashMap<>();
    }

    public void count(int id) {
        if (cnt.containsKey(id)) {
            int temp = cnt.get(id);
            cnt.replace(id, temp + 1);
        }
        else {
            cnt.put(id, 1);
        }
        ++ total;
    }

    public int getTotal() {
        return this.total;
    }

    public int getCount(int id) {
        if (cnt.containsKey(id)) {
            return cnt.get(id);
        }
        return 0;
    }
}
