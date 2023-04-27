import com.oocourse.spec2.main.Group;
import com.oocourse.spec2.main.Person;

import java.util.HashMap;
import java.util.Map;

public class MyGroup implements Group {
    private final int id;
    private final HashMap<Integer, Person> people;
    private int sumAge;
    private int sumPowAge;
     /*@ public instance model int id;
      @ public instance model non_null Person[] people;
      @*/
    public MyGroup(int id) {
        this.id = id;
        this.people = new HashMap<>();
        this.sumAge = 0;
        this.sumPowAge = 0;
    }

    //@ ensures \result == id;
    public /*@ pure @*/ int getId() {
        return this.id;
    }

    /*@ also
      @ public normal_behavior
      @ requires obj != null && obj instanceof Group;
      @ assignable \nothing;
      @ ensures \result == (((Group) obj).getId() == id);
      @ also
      @ public normal_behavior
      @ requires obj == null || !(obj instanceof Group);
      @ assignable \nothing;
      @ ensures \result == false;
      @*/
    public /*@ pure @*/ boolean equals(Object obj) {
        if (!(obj instanceof Group)) {
            return false;
        }
        return (((Group) obj).getId() == id);
    }

    /*@ public normal_behavior
      @ requires !hasPerson(person);
      @ assignable people[*];
      @ ensures (\forall Person p; \old(hasPerson(p)); hasPerson(p));
      @ ensures \old(people.length) == people.length - 1;
      @ ensures hasPerson(person);
      @*/
    public void addPerson(/*@ non_null @*/Person person) {
        assert (!hasPerson(person));
        people.put(person.getId(), person);
        this.sumAge += person.getAge();
        this.sumPowAge += person.getAge() * person.getAge();
    }

    //@ ensures \result == (\exists int i; 0 <= i && i < people.length; people[i].equals(person));
    public /*@ pure @*/ boolean hasPerson(Person person) {
        return people.containsKey(person.getId());
    }

    /*@ ensures \result == (\sum int i; 0 <= i && i < people.length;
      @          (\sum int j; 0 <= j && j < people.length &&
      @           people[i].isLinked(people[j]); people[i].queryValue(people[j])));
      @*/
    public /*@ pure @*/ int getValueSum() {
        int sum = 0;
        for (Map.Entry<Integer, Person> i : people.entrySet()) {
            for (Map.Entry<Integer, Person> j : people.entrySet()) {
                if (i.getKey().equals(j.getKey())) {
                    continue;
                }
                if (i.getValue().isLinked(j.getValue())) {
                    sum += i.getValue().queryValue(j.getValue());
                }
            }
        }
        return sum >> 1;
    }

    /*@ ensures \result == (people.length == 0? 0:
      @          ((\sum int i; 0 <= i && i < people.length; people[i].getAge()) / people.length));
      @*/
    public /*@ pure @*/ int getAgeMean() {
        return sumAge / people.size();
    }

    /*@ ensures \result == (people.length == 0? 0 : ((\sum int i; 0 <= i && i < people.length;
      @          (people[i].getAge() - getAgeMean()) * (people[i].getAge() - getAgeMean())) /
      @           people.length));
      @*/
    public /*@ pure @*/ int getAgeVar() {
        int mean = getAgeMean();
        return (sumPowAge - 2 * mean * sumAge + getSize() * mean * mean) / people.size();
    }

    /*@ public normal_behavior
      @ requires hasPerson(person) == true;
      @ assignable people[*];
      @ ensures (\forall Person p; hasPerson(p); \old(hasPerson(p)));
      @ ensures \old(people.length) == people.length + 1;
      @ ensures hasPerson(person) == false;
      @*/
    public void delPerson(/*@ non_null @*/Person person) {
        assert (hasPerson(person));
        people.remove(person.getId());
        this.sumAge -= person.getAge();
        this.sumPowAge -= person.getAge() * person.getAge();
    }

    //@ ensures \result == people.length;
    public /*@ pure @*/ int getSize() {
        return people.size();
    }

    public void addSocialValue(int num) {
        for (Map.Entry<Integer, Person> i : people.entrySet()) {
            i.getValue().addSocialValue(num);
        }
    }
}
