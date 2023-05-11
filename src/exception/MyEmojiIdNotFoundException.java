package exception;

import com.oocourse.spec3.exceptions.EmojiIdNotFoundException;
public class MyEmojiIdNotFoundException extends EmojiIdNotFoundException {
    private final int id;

    private static final Counter counter = new Counter();

    public MyEmojiIdNotFoundException(int id) {
        this.id = id;
        counter.count(id);
    }

    public void print() {
        System.out.printf("einf-%d, %d-%d\n", counter.getTotal(), id, counter.getCount(id));
    }
}
