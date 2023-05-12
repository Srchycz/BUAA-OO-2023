package exception;

import com.oocourse.spec3.exceptions.PathNotFoundException;

public class MyPathNotFoundException extends PathNotFoundException {
    private final int id;
    private static final Counter counter = new Counter();

    public MyPathNotFoundException(int id) {
        this.id = id;
        counter.count(id);
    }

    public void print() {
        System.out.printf("pnf-%d, %d-%d\n", counter.getTotal(), id, counter.getCount(id));
    }
}
