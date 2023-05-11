package exception;

import com.oocourse.spec3.exceptions.EqualMessageIdException;

public class MyEqualMessageIdException extends EqualMessageIdException {
    private final int id;

    private static final Counter counter = new Counter();

    public MyEqualMessageIdException(int id) {
        this.id = id;
        counter.count(id);
    }

    public void print() {
        System.out.printf("emi-%d, %d-%d\n", counter.getTotal(), id, counter.getCount(id));
    }
}
