import com.oocourse.spec2.main.Message;
import com.oocourse.spec2.main.Person;

import java.util.HashMap;
import java.util.List;

public class MyPerson implements Person {
    private MyPerson fa;

    private final int id;
    private final String name;
    private final int age;
    private final HashMap<Integer, Person> acquaintance;
    private final HashMap<Integer, Integer> value;

    private int socialValue;

    private final HashMap<Integer, Message> messages;

    public MyPerson(int id, String name, int age) {
        this.id = id;
        this.name = name;
        this.age = age;
        this.acquaintance = new HashMap<>();
        this.value = new HashMap<>();
        this.fa = this;
        this.socialValue = 0;
        this.messages = new HashMap<>();
    }

    public int getId() { return this.id; }

    public String getName() { return this.name; }

    public int getAge() {
        return this.age;
    }

    public boolean equals(Object obj) {
        if (!(obj instanceof Person)) {
            return false;
        }
        return (((Person) obj).getId() == id);
    }

    public /*@ pure @*/ boolean isLinked(Person person) {
        if (person.getId() == id) {
            return true;
        }
        return acquaintance.containsKey(person.getId());
    }

    public /*@ pure @*/ int queryValue(Person person) {
        if (acquaintance.containsKey(person.getId())) {
            return value.get(person.getId());
        }
        return 0;
    }

    public /*@ pure @*/ int compareTo(Person p2) {
        return name.compareTo(p2.getName());
    }

    public void addAcquaintance(Person person, Integer v) {
        acquaintance.put(person.getId(), person);
        value.put(person.getId(), v);
        setFa(((MyPerson) person).getFa());
    }

    public MyPerson getFa() {
        if (fa.getId() == id) {
            return fa;
        }
        return this.fa = fa.getFa();
    }

    private void setFa(MyPerson person) {
        if (fa.getId() == id) {
            this.fa = person;
        }
        else {
            getFa().setFa(person);
        }
    }

    public HashMap<Integer, Person> getAcquaintance() {
        return this. acquaintance;
    }

    /*@ public normal_behavior
     @ assignable socialValue;
     @ ensures socialValue == \old(socialValue) + num;
     @*/
    public void addSocialValue(int num) {
        this.socialValue += num;
    }

    //@ ensures \result == socialValue;
    public /*@ pure @*/ int getSocialValue() {
        return this.socialValue;
    }

    /*@ ensures (\result.size() == messages.length) &&
      @           (\forall int i; 0 <= i && i < messages.length;
      @             messages[i] == \result.get(i));
      @*/
    public /*@ pure @*/ List<Message> getMessages() {

    }

    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures (\forall int i; 0 <= i && i < messages.length && i <= 4;
      @           \result.contains(messages[i]) && \result.get(i) == messages[i]);
      @ ensures \result.size() == ((messages.length < 5)? messages.length: 5);
      @*/
    public /*@ pure @*/ List<Message> getReceivedMessages() {

    }

}
