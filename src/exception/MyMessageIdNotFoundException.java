package exception;

import com.oocourse.spec2.exceptions.MessageIdNotFoundException;

public class MyMessageIdNotFoundException extends MessageIdNotFoundException {
    private final int id;

    private static final Counter counter = new Counter();

    public MyMessageIdNotFoundException(int id) {
        this.id = id;
        counter.count(id);
    }

    public void print() {
        System.out.printf("minf-%d, %d-%d\n", counter.getTotal(), id, counter.getCount(id));
    }
}
