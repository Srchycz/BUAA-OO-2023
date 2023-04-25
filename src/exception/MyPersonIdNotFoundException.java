package exception;

import com.oocourse.spec2.exceptions.PersonIdNotFoundException;

public class MyPersonIdNotFoundException extends PersonIdNotFoundException {
    private final int id;

    private static final Counter counter = new Counter();

    public MyPersonIdNotFoundException(int id) {
        this.id = id;
        counter.count(id);
    }

    public void print() {
        System.out.printf("pinf-%d, %d-%d\n", counter.getTotal(), id, counter.getCount(id));
    }
}
