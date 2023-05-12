import com.oocourse.spec3.main.Group;
import com.oocourse.spec3.main.Person;

import java.util.HashMap;
import java.util.Map;

public class MyGroup implements Group {
    private final int id;
    private final HashMap<Integer, Person> people;
    private int sumAge;
    private int sumPowAge;

    public MyGroup(int id) {
        this.id = id;
        this.people = new HashMap<>();
        this.sumAge = 0;
        this.sumPowAge = 0;
    }

    public int getId() {
        return this.id;
    }

    public boolean equals(Object obj) {
        if (!(obj instanceof Group)) {
            return false;
        }
        return (((Group) obj).getId() == id);
    }

    public void addPerson(Person person) {
        assert (!hasPerson(person));
        people.put(person.getId(), person);
        this.sumAge += person.getAge();
        this.sumPowAge += person.getAge() * person.getAge();
    }

    public boolean hasPerson(Person person) {
        return people.containsKey(person.getId());
    }

    public int getValueSum() {
        int sum = 0;
        for (Map.Entry<Integer, Person> i : people.entrySet()) {
            for (Map.Entry<Integer, Person> j : people.entrySet()) {
                if (i.getValue().isLinked(j.getValue())) {
                    sum += i.getValue().queryValue(j.getValue());
                }
            }
        }
        return sum;
    }

    public /*@ pure @*/ int getAgeMean() {
        if (people.isEmpty()) {
            return 0;
        }
        return sumAge / people.size();
    }

    public int getAgeVar() {
        if (people.isEmpty()) {
            return 0;
        }
        int mean = getAgeMean();
        return (sumPowAge - 2 * mean * sumAge + getSize() * mean * mean) / people.size();
    }

    public void delPerson(Person person) {
        assert (hasPerson(person));
        people.remove(person.getId());
        this.sumAge -= person.getAge();
        this.sumPowAge -= person.getAge() * person.getAge();
    }

    public int getSize() {
        return people.size();
    }

    public void addSocialValue(int num) {
        for (Map.Entry<Integer, Person> i : people.entrySet()) {
            i.getValue().addSocialValue(num);
        }
    }

    public void addMoney(int num, int id) {
        for (Map.Entry<Integer, Person> i : people.entrySet()) {
            if (i.getKey() == id) {
                continue;
            }
            i.getValue().addMoney(num);
        }
    }
}
