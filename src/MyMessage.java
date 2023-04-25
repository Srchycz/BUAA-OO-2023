import com.oocourse.spec2.main.Group;
import com.oocourse.spec2.main.Message;
import com.oocourse.spec2.main.Person;

public class MyMessage implements Message {
    private final int id;
    private int socialValue;
    private final int type;
    private Person person1;
    private Person person2;
    private Group group;
     /*@ public instance model int id;
      @ public instance model int socialValue;
      @ public instance model int type;
      @ public instance model non_null Person person1;
      @ public instance model nullable Person person2;
      @ public instance model nullable Group group;
      @*/

    public MyMessage(int id, int socialValue, int type, Person person1, Person person2) {
        this.id = id;
        this.socialValue = socialValue;
        this.type = type;
        this.person1 = person1;
        this.person2 = person2;
    }

    public MyMessage(int id, int socialValue, int type, Person person1, Group group) {
        this.id = id;
        this.socialValue = socialValue;
        this.type = type;
        this.person1 = person1;
        this.group = group;
        this.person2 = null;
    }

    //@ ensures \result == type;
    public /*@ pure @*/ int getType() {
        return this.type;
    }

    //@ ensures \result == id;
    public /*@ pure @*/ int getId() {
        return this.id;
    }

    //@ ensures \result == socialValue;
    public /*@ pure @*/ int getSocialValue() {
        return this.socialValue;
    }

    //@ ensures \result == person1;
    public /*@ pure @*/ Person getPerson1() {
        return this.person1;
    }

    /*@ requires person2 != null;
      @ ensures \result == person2;
      @*/
    public /*@ pure @*/ Person getPerson2() {
        assert (person2 != null);
        return this.person2;
    }

    /*@ requires group != null;
      @ ensures \result == group;
      @*/
    public /*@ pure @*/ Group getGroup() {
        return this.group;
    }

    /*@ also
      @ public normal_behavior
      @ requires obj != null && obj instanceof Message;
      @ assignable \nothing;
      @ ensures \result == (((Message) obj).getId() == id);
      @ also
      @ public normal_behavior
      @ requires obj == null || !(obj instanceof Message);
      @ assignable \nothing;
      @ ensures \result == false;
      @*/
    public /*@ pure @*/ boolean equals(Object obj) {
        if (!(obj instanceof Message)) {
            return false;
        }
        return (((Message) obj).getId() == id);
    }
}
