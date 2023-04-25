package exception;

import com.oocourse.spec2.exceptions.EqualRelationException;

public class MyEqualRelationException extends EqualRelationException {
    private final int id1;

    private final int id2;

    private static final Counter counter = new Counter();

    public MyEqualRelationException(int id1, int id2) {
        this.id1 = id1;
        this.id2 = id2;
        counter.count(id1, id2);
    }

    public void print() {
        if (id1 < id2) {
            System.out.printf("er-%d, %d-%d, %d-%d\n", counter.getTotal(),
                    id1, counter.getCount(id1), id2, counter.getCount(id2));
        }
        else {
            System.out.printf("er-%d, %d-%d, %d-%d\n", counter.getTotal(),
                    id2, counter.getCount(id2), id1, counter.getCount(id1));
        }
    }
}
