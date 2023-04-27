package exception;

import com.oocourse.spec2.exceptions.GroupIdNotFoundException;

public class MyGroupIdNotFoundException extends GroupIdNotFoundException {
    private final int id;

    private static final Counter counter = new Counter();

    public MyGroupIdNotFoundException(int id) {
        this.id = id;
        counter.count(id);
    }

    public void print() {
        System.out.printf("ginf-%d, %d-%d\n", counter.getTotal(), id, counter.getCount(id));
    }
}
