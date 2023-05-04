import com.oocourse.spec2.main.Group;
import com.oocourse.spec2.main.Message;
import com.oocourse.spec2.main.Person;

public class MyMessage implements Message {
    private final int id;
    private final int socialValue;
    private final int type;
    private final Person person1;
    private final Person person2;
    private final Group group;

    public MyMessage(int id, int socialValue, Person person1, Person person2) {
        this.id = id;
        this.socialValue = socialValue;
        this.type = 0;
        this.group = null;
        this.person1 = person1;
        this.person2 = person2;
    }

    public MyMessage(int id, int socialValue, Person person1, Group group) {
        this.id = id;
        this.socialValue = socialValue;
        this.type = 1;
        this.person1 = person1;
        this.group = group;
        this.person2 = null;
    }

    public int getType() {
        return this.type;
    }

    public int getId() {
        return this.id;
    }

    public int getSocialValue() {
        return this.socialValue;
    }

    public Person getPerson1() {
        return this.person1;
    }

    public Person getPerson2() {
        assert (person2 != null);
        return this.person2;
    }

    public Group getGroup() {
        return this.group;
    }

    public boolean equals(Object obj) {
        if (!(obj instanceof Message)) {
            return false;
        }
        return (((Message) obj).getId() == id);
    }
}
