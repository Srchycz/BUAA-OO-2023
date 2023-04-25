package exception;

import com.oocourse.spec2.exceptions.EqualGroupIdException;

public class MyEqualGroupIdException extends EqualGroupIdException {
    private final int id;

    private static final Counter counter = new Counter();

    public MyEqualGroupIdException(int id) {
        this.id = id;
        counter.count(id);
    }

    public void print() {
        System.out.printf("egi-%d, %d-%d\n", counter.getTotal(), id, counter.getCount(id));
    }
}
