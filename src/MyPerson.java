import com.oocourse.spec1.main.Person;

import java.util.HashMap;

public class MyPerson implements Person {
    private MyPerson fa;

    private final int id;
    private final String name;
    private final int age;
    private final HashMap<Integer, Person> acquaintance;
    private final HashMap<Integer, Integer> value;
     /*@ public instance model int id;
      @ public instance model non_null String name;
      @ public instance model int age;
      @ public instance model non_null Person[] acquaintance;
      @ public instance model non_null int[] value;
      @*/

    public MyPerson(int id, String name, int age) {
        this.id = id;
        this.name = name;
        this.age = age;
        this.acquaintance = new HashMap<>();
        this.value = new HashMap<>();
        this.fa = this;
    }


    /*@ invariant acquaintance!= null && value != null && acquaintance.length == value.length &&
      @  (\forall int i,j; 0 <= i && i < j && j < acquaintance.length;
      @   !acquaintance[i].equals(acquaintance[j]));*/

    //@ ensures \result == id;
    public /*@ pure @*/ int getId() { return this.id; }

    //@ ensures \result.equals(name);
    public /*@ pure @*/ String getName() { return this.name; }

    //@ ensures \result == age;
    public /*@ pure @*/ int getAge() {
        return this.age;
    }

    /*@ also
      @ public normal_behavior
      @ requires obj != null && obj instanceof Person;
      @ assignable \nothing;
      @ ensures \result == (((Person) obj).getId() == id);
      @ also
      @ public normal_behavior
      @ requires obj == null || !(obj instanceof Person);
      @ assignable \nothing;
      @ ensures \result == false;
      @*/
    public /*@ pure @*/ boolean equals(Object obj) {
        assert (obj != null);
        if (obj instanceof Person) {
            return (((Person) obj).getId() == id);
        }
        else {
            return false;
        }
    }

    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == (\exists int i; 0 <= i && i < acquaintance.length;
      @                     acquaintance[i].getId() == person.getId()) || person.getId() == id;
      @*/
    public /*@ pure @*/ boolean isLinked(Person person) {
        if (person.getId() == id) {
            return true;
        }
        return acquaintance.containsKey(person.getId());
    }

    /*@ public normal_behavior
      @ requires (\exists int i; 0 <= i && i < acquaintance.length;
      @          acquaintance[i].getId() == person.getId());
      @ assignable \nothing;
      @ ensures (\exists int i; 0 <= i && i < acquaintance.length;
      @         acquaintance[i].getId() == person.getId() && \result == value[i]);
      @ also
      @ public normal_behavior
      @ requires (\forall int i; 0 <= i && i < acquaintance.length;
      @          acquaintance[i].getId() != person.getId());
      @ ensures \result == 0;
      @*/
    public /*@ pure @*/ int queryValue(Person person) {
        if (acquaintance.containsKey(person.getId())) {
            return value.get(person.getId());
        }
        return 0;
    }

    //@ also ensures \result == name.compareTo(p2.getName());
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
}
