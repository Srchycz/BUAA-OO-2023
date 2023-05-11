import com.oocourse.spec3.main.Message;
import com.oocourse.spec3.main.Person;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class MyPerson implements Person {
    private final int id;
    private final String name;
    private final int age;
    private int money;
    private final HashMap<Integer, Person> acquaintance;
    private final HashMap<Integer, Integer> values;

    private int socialValue;

    private final LinkedList<Message> messages;

    public MyPerson(int id, String name, int age) {
        this.id = id;
        this.name = name;
        this.age = age;
        this.acquaintance = new HashMap<>();
        this.values = new HashMap<>();
        this.socialValue = 0;
        this.messages = new LinkedList<>();
        this.money = 0;
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

    public boolean isLinked(Person person) {
        if (person.getId() == id) {
            return true;
        }
        return acquaintance.containsKey(person.getId());
    }

    public int queryValue(Person person) {
        if (acquaintance.containsKey(person.getId())) {
            return values.get(person.getId());
        }
        return 0;
    }

    public int queryValue(int id) {
        if (acquaintance.containsKey(id)) {
            return values.get(id);
        }
        return 0;
    }

    public int compareTo(Person p2) {
        return name.compareTo(p2.getName());
    }

    public void addAcquaintance(Person person, Integer v) {
        acquaintance.put(person.getId(), person);
        values.put(person.getId(), v);
    }

    public HashMap<Integer, Person> getAcquaintance() {
        return this.acquaintance;
    }

    public void addSocialValue(int num) {
        this.socialValue += num;
    }

    public int getSocialValue() {
        return this.socialValue;
    }

    public List<Message> getMessages() {
        return messages;
    }

    public List<Message> getReceivedMessages() {
        LinkedList<Message> m = new LinkedList<>();
        for (int i = 0; i < messages.size() && i < 5; ++ i) {
            m.addLast(messages.get(i));
        }
        return m;
    }

    public void addMessage(Message message) {
        messages.addFirst(message);
    }

    public void modifyRelation(int id, int value) {
        if (value + values.get(id) > 0) {
            values.replace(id, values.get(id) + value);
        }
        else {
            acquaintance.remove(id);
            values.remove(id);
        }
    }

    public int bestIdx() {
        int res = 0xfffff;
        int max = -1;
        for (Map.Entry<Integer, Integer> i : values.entrySet()) {
            if (i.getValue() > max || (i.getValue() == max && i.getKey() < res)) {
                max = i.getValue();
                res = i.getKey();
            }
        }
        return res;
    }

    /*@ public normal_behavior
  @ assignable money;
  @ ensures money == \old(money) + num;
  @*/
    public void addMoney(int num) {
        money += num;
    }

    public int getMoney() {
        return money;
    }

    public void clearNotices() {
        messages.removeIf(message -> message instanceof MyNoticeMessage);
    }
}
