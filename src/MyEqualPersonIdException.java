import com.oocourse.spec1.exceptions.EqualPersonIdException;

public class MyEqualPersonIdException extends EqualPersonIdException {
    private final int id;

    static private final Counter counter = new Counter();

    public MyEqualPersonIdException(int id) {
        this.id = id;
        counter.count(id);
    }

    public void print() {
        System.out.printf("epi-%d, %d-%d\n", counter.getTotal(), id, counter.getCount(id));
    }
}
