package exception;

import com.oocourse.spec3.exceptions.EqualEmojiIdException;
public class MyEqualEmojiIdException extends EqualEmojiIdException {
    private final int id;
    private static final Counter counter = new Counter();

    public MyEqualEmojiIdException(int id) {
        this.id = id;
        counter.count(id);
    }

    public void print() {
        System.out.printf("eei-%d, %d-%d\n", counter.getTotal(), id, counter.getCount(id));
    }
}
