import com.oocourse.spec1.main.Person;

import java.util.HashMap;

public class MyPerson implements Person {
    private MyPerson fa;

    private final int id;
    private final String name;
    private final int age;
    private final HashMap<Integer, Person> acquaintance;
    private final HashMap<Integer, Integer> value;

    public MyPerson(int id, String name, int age) {
        this.id = id;
        this.name = name;
        this.age = age;
        this.acquaintance = new HashMap<>();
        this.value = new HashMap<>();
        this.fa = this;
    }

    public int getId() { return this.id; }

    public String getName() { return this.name; }

    public int getAge() {
        return this.age;
    }

    public boolean equals(Object obj) {
        assert (obj != null);
        if (obj instanceof Person) {
            return (((Person) obj).getId() == id);
        }
        else {
            return false;
        }
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
        this.fa = ((MyPerson) person).getFa();
    }

    public MyPerson getFa() {
        if (fa.getId() == id) {
            return fa;
        }
        return this.fa = fa.getFa();
    }

    public HashMap<Integer, Person> getAcquaintance() {
        return this. acquaintance;
    }
}