package exception;

import com.oocourse.spec3.exceptions.AcquaintanceNotFoundException;

public class MyAcquaintanceNotFoundException extends AcquaintanceNotFoundException {
    private final int id;

    private static final Counter counter = new Counter();

    public MyAcquaintanceNotFoundException(int id) {
        this.id = id;
        counter.count(id);
    }

    public void print() {
        System.out.printf("anf-%d, %d-%d\n", counter.getTotal(), id, counter.getCount(id));
    }
}
