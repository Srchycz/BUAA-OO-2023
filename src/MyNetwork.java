import com.oocourse.spec1.exceptions.EqualPersonIdException;
import com.oocourse.spec1.exceptions.EqualRelationException;
import com.oocourse.spec1.exceptions.PersonIdNotFoundException;
import com.oocourse.spec1.exceptions.RelationNotFoundException;
import com.oocourse.spec1.main.Network;
import com.oocourse.spec1.main.Person;
import exception.MyEqualPersonIdException;
import exception.MyEqualRelationException;
import exception.MyPersonIdNotFoundException;
import exception.MyRelationNotFoundException;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

public class MyNetwork implements Network {

    private int blockSum;

    private int tripleSum;

    private boolean blockUpdate;

    private boolean tripleUpdate;

    private final HashMap<Integer, Person> people;

    public MyNetwork() {
        people = new HashMap<>();
        this.blockSum = 0;
        this.tripleSum = 0;
        this.blockUpdate = false;
        this.tripleUpdate = false;
    }

    public boolean contains(int id) {
        return people.containsKey(id);
    }

    public Person getPerson(int id) {
        if (people.containsKey(id)) {
            return people.get(id);
        }
        return null;
    }

    public void addPerson(Person person) throws EqualPersonIdException {
        if (people.containsKey(person.getId())) {
            throw new MyEqualPersonIdException(person.getId());
        }
        people.put(person.getId(), person);
        blockUpdate = false;
    }

    public void addRelation(int id1, int id2, int value) throws
            PersonIdNotFoundException, EqualRelationException {
        if (contains(id1) && contains(id2) && !getPerson(id1).isLinked(getPerson(id2))) {
            MyPerson myPerson1 = (MyPerson) getPerson(id1);
            MyPerson myPerson2 = (MyPerson) getPerson(id2);
            myPerson1.addAcquaintance(myPerson2, value);
            myPerson2.addAcquaintance(myPerson1, value);
        }
        else {
            if (!contains(id1)) {
                throw new MyPersonIdNotFoundException(id1);
            }
            if (!contains(id2)) {
                throw new MyPersonIdNotFoundException(id2);
            }
            if (getPerson(id1).isLinked(getPerson(id2))) {
                throw new MyEqualRelationException(id1, id2);
            }
        }
        blockUpdate = false;
        tripleUpdate = false;
    }

    public int queryValue(int id1, int id2) throws
            PersonIdNotFoundException, RelationNotFoundException {
        if (!contains(id1)) {
            throw new MyPersonIdNotFoundException(id1);
        }
        if (!contains(id2)) {
            throw new MyPersonIdNotFoundException(id2);
        }
        if (!getPerson(id1).isLinked(getPerson(id2))) {
            throw new MyRelationNotFoundException(id1, id2);
        }
        return getPerson(id1).queryValue(getPerson(id2));
    }

    public /*@ pure @*/ boolean isCircle(int id1, int id2) throws PersonIdNotFoundException {
        if (!contains(id1)) {
            throw new MyPersonIdNotFoundException(id1);
        }
        if (!contains(id2)) {
            throw new MyPersonIdNotFoundException(id2);
        }
        MyPerson myPerson1 = (MyPerson) getPerson(id1);
        MyPerson myPerson2 = (MyPerson) getPerson(id2);
        return myPerson1.getFa() == myPerson2.getFa();
    }

    public /*@ pure @*/ int queryBlockSum() {
        if (blockUpdate) {
            return blockSum;
        }
        int sum = 0;
        for (Integer i : people.keySet()) {
            if (((MyPerson) people.get(i)).getFa().equals(people.get(i))) {
                ++ sum;
            }
        }
        blockUpdate = true;
        return blockSum = sum;
    }

    public /*@ pure @*/ int queryTripleSum() {
        if (tripleUpdate) {
            return tripleSum;
        }
        int sum = 0;
        for (Map.Entry<Integer, Person> i : people.entrySet()) {
            MyPerson u = (MyPerson) i.getValue();
            for (Map.Entry<Integer, Person> j : u.getAcquaintance().entrySet()) {
                MyPerson v = (MyPerson) j.getValue();
                if (!hasEdge(u, v)) {
                    continue;
                }
                for (Map.Entry<Integer, Person> k : v.getAcquaintance().entrySet()) {
                    MyPerson w = (MyPerson) k.getValue();
                    if (u.isLinked(w) && hasEdge(u, w) && hasEdge(w, v)) {
                        ++ sum;
                    }
                }
            }
        }
        return tripleSum = sum;
    }

    private boolean hasEdge(MyPerson u, MyPerson v) {
        return (u.getAcquaintance().size() < v.getAcquaintance().size())
                || (u.getAcquaintance().size() == v.getAcquaintance().size()
                && u.getId() < v.getId());
    }

    /*@ ensures \result ==
      @         (\sum int i; 0 <= i && i < people.length;
      @             (\sum int j; i < j && j < people.length;
      @                 (\sum int k; j < k && k < people.length
      @                     && getPerson(people[i].getId()).isLinked(getPerson(people[j].getId()))
      @                     && getPerson(people[j].getId()).isLinked(getPerson(people[k].getId()))
      @                     && getPerson(people[k].getId()).isLinked(getPerson(people[i].getId()));
      @                     1)));
      @*/
    public boolean queryTripleSumOKTest(HashMap<Integer, HashMap<Integer, Integer>> beforeData,
                                        HashMap<Integer, HashMap<Integer, Integer>> afterData,
                                        int result) {
        if (!beforeData.equals(afterData)) {
            return false;
        }
        long res = 0;
        for (Map.Entry<Integer, HashMap<Integer, Integer>> i : beforeData.entrySet()) {
            for (Map.Entry<Integer, HashMap<Integer, Integer>> j : beforeData.entrySet()) {
                if (Objects.equals(i.getKey(), j.getKey())) {
                    continue;
                }
                for (Map.Entry<Integer, HashMap<Integer, Integer>> k : beforeData.entrySet()) {
                    if (Objects.equals(i.getKey(), k.getKey())
                            || Objects.equals(j.getKey(), k.getKey())) {
                        continue;
                    }
                    if (i.getValue().containsKey(j.getKey())
                            && j.getValue().containsKey(k.getKey())
                            && k.getValue().containsKey(i.getKey())) {
                        ++ res;
                    }
                }
            }
        }
        return (res / 6) == result;
    }
}
