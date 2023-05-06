import com.oocourse.spec2.exceptions.EqualMessageIdException;
import com.oocourse.spec2.exceptions.EqualGroupIdException;
import com.oocourse.spec2.exceptions.MessageIdNotFoundException;
import com.oocourse.spec2.exceptions.EqualRelationException;
import com.oocourse.spec2.exceptions.AcquaintanceNotFoundException;
import com.oocourse.spec2.exceptions.PersonIdNotFoundException;
import com.oocourse.spec2.exceptions.GroupIdNotFoundException;
import com.oocourse.spec2.exceptions.EqualPersonIdException;
import com.oocourse.spec2.exceptions.RelationNotFoundException;
import com.oocourse.spec2.main.Group;
import com.oocourse.spec2.main.Message;
import com.oocourse.spec2.main.Network;
import com.oocourse.spec2.main.Person;
import exception.MyEqualMessageIdException;
import exception.MyEqualGroupIdException;
import exception.MyMessageIdNotFoundException;
import exception.MyAcquaintanceNotFoundException;
import exception.MyPersonIdNotFoundException;
import exception.MyEqualPersonIdException;
import exception.MyGroupIdNotFoundException;
import exception.MyRelationNotFoundException;
import exception.MyEqualRelationException;

import java.util.HashMap;
import java.util.Map;
import java.util.Queue;
import java.util.LinkedList;
import java.util.List;
import java.util.Objects;

public class MyNetwork implements Network {
    private int blockSum;
    private int tripleSum;
    private boolean blockUpdate;
    private boolean tripleUpdate;
    private final HashMap<Integer, Person> people;
    private final HashMap<Integer, Group> groups;
    private final HashMap<Integer, Message> messages;

    public MyNetwork() {
        this.blockSum = 0;
        this.tripleSum = 0;
        this.blockUpdate = true;
        this.tripleUpdate = false;
        this.people = new HashMap<>();
        this.groups = new HashMap<>();
        this.messages = new HashMap<>();
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
        ++ blockSum;
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

    public void modifyRelation(int id1, int id2, int value) throws PersonIdNotFoundException,
            EqualPersonIdException, RelationNotFoundException {
        if (!contains(id1)) {
            throw new MyPersonIdNotFoundException(id1);
        }
        if (!contains(id2)) {
            throw new MyPersonIdNotFoundException(id2);
        }
        if (id1 == id2) {
            throw new MyEqualPersonIdException(id1);
        }
        if (!getPerson(id1).isLinked(getPerson(id2))) {
            throw new MyRelationNotFoundException(id1, id2);
        }
        Person person1 = getPerson(id1);
        Person person2 = getPerson(id2);
        ((MyPerson) person1).modifyRelation(id2, value);
        ((MyPerson) person2).modifyRelation(id1, value);
        if (!person1.isLinked(person2)) {
            tripleUpdate = blockUpdate = false;
        }
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
        if (id1 == id2) {
            return true;
        }
        HashMap<Integer, Integer> vis = new HashMap<>();
        vis.put(id1, id1);
        vis.put(id2, id2);
        Queue<Person> q1 = new LinkedList<>();
        Queue<Person> q2 = new LinkedList<>();
        q1.offer(getPerson(id1));
        q2.offer(getPerson(id2));
        while (!q1.isEmpty() && !q2.isEmpty()) {
            MyPerson now1 = (MyPerson) q1.poll();
            if (bfs(id2, id1, vis, q1, now1)) {
                return true;
            }
            MyPerson now2 = (MyPerson) q2.poll();
            if (bfs(id1, id2, vis, q2, now2)) {
                return true;
            }
        }
        return false;
    }

    private boolean bfs(int aim, int id,
                        HashMap<Integer, Integer> vis, Queue<Person> queue, MyPerson now) {
        for (int i : now.getAcquaintance().keySet()) {
            if (vis.containsKey(i)) {
                if (vis.get(i) == aim) {
                    return true;
                }
                continue;
            }
            vis.put(i, id);
            queue.offer(getPerson(i));
        }
        return false;
    }

    public int queryBlockSum() {
        if (blockUpdate) {
            return blockSum;
        }
        int sum = 0;
        HashMap<Integer, Boolean> vis = new HashMap<>();
        for (Integer i : people.keySet()) {
            if (vis.containsKey(i)) {
                continue;
            }
            dfs(i, vis);
            ++sum;
        }
        blockUpdate = true;
        return blockSum = sum;
    }

    private void dfs(int idx, HashMap<Integer, Boolean> vis) {
        vis.put(idx, true);
        MyPerson person = (MyPerson) getPerson(idx);
        for (Integer i : person.getAcquaintance().keySet()) {
            if (!vis.containsKey(i)) {
                dfs(i, vis);
            }
        }
    }

    public int queryTripleSum() {
        if (tripleUpdate) {
            return tripleSum;
        }
        int sum = 0;
        for (Map.Entry<Integer, Person> i : people.entrySet()) {
            MyPerson u = (MyPerson) i.getValue();
            for (Map.Entry<Integer, Person> j : u.getAcquaintance().entrySet()) {
                MyPerson v = (MyPerson) j.getValue();
                if (hasEdge(u, v)) {
                    for (Map.Entry<Integer, Person> k : v.getAcquaintance().entrySet()) {
                        MyPerson w = (MyPerson) k.getValue();
                        if (u.isLinked(w) && hasEdge(u, w) && hasEdge(w, v)) {
                            ++ sum;
                        }
                    }
                }
            }
        }
        return tripleSum = sum;
    }

    private boolean hasEdge(MyPerson u, MyPerson v) {
        return (u.getAcquaintance().size() < v.getAcquaintance().size()) ||
                (u.getAcquaintance().size() == v.getAcquaintance().size() && u.getId() < v.getId());
    }

    public void addGroup(Group group) throws EqualGroupIdException {
        if (groups.containsKey(group.getId())) {
            throw new MyEqualGroupIdException(group.getId());
        }
        groups.put(group.getId(), group);
    }

    public Group getGroup(int id) {
        if (groups.containsKey(id)) {
            return groups.get(id);
        }
        return null;
    }

    public void addToGroup(int id1, int id2) throws GroupIdNotFoundException,
            PersonIdNotFoundException, EqualPersonIdException {
        Group group = getGroup(id2);
        if (group == null) {
            throw new MyGroupIdNotFoundException(id2);
        }
        Person person = getPerson(id1);
        if (person == null) {
            throw new MyPersonIdNotFoundException(id1);
        }
        if (group.hasPerson(person)) {
            throw new MyEqualPersonIdException(id1);
        }
        if (group.getSize() <= 1111) {
            group.addPerson(person);
        }
    }

    public int queryGroupValueSum(int id) throws GroupIdNotFoundException {
        Group group = getGroup(id);
        if (group == null) {
            throw new MyGroupIdNotFoundException(id);
        }
        return group.getValueSum();
    }

    public int queryGroupAgeVar(int id) throws GroupIdNotFoundException {
        Group group = getGroup(id);
        if (group == null) {
            throw new MyGroupIdNotFoundException(id);
        }
        return group.getAgeVar();
    }

    public void delFromGroup(int id1, int id2)
            throws GroupIdNotFoundException, PersonIdNotFoundException, EqualPersonIdException {
        Group group = getGroup(id2);
        if (group == null) {
            throw new MyGroupIdNotFoundException(id2);
        }
        Person person = getPerson(id1);
        if (person == null) {
            throw new MyPersonIdNotFoundException(id1);
        }
        if (!group.hasPerson(person)) {
            throw new MyEqualPersonIdException(id1);
        }
        group.delPerson(person);
    }

    public boolean containsMessage(int id) {
        return messages.containsKey(id);
    }

    public void addMessage(Message message) throws
            EqualMessageIdException, EqualPersonIdException {
        if (containsMessage(message.getId())) {
            throw new MyEqualMessageIdException(message.getId());
        }
        if (message.getType() == 0 && message.getPerson1().equals(message.getPerson2())) {
            throw new MyEqualPersonIdException(message.getPerson1().getId());
        }
        messages.put(message.getId(), message);
    }

    public Message getMessage(int id) {
        if (messages.containsKey(id)) {
            return messages.get(id);
        }
        return null;
    }

    public void sendMessage(int id) throws
            RelationNotFoundException, MessageIdNotFoundException, PersonIdNotFoundException {
        Message message = getMessage(id);
        if (message == null) {
            throw new MyMessageIdNotFoundException(id);
        }
        if (message.getType() == 0 && !message.getPerson1().isLinked(message.getPerson2())) {
            throw new MyRelationNotFoundException(
                    message.getPerson1().getId(), message.getPerson2().getId());
        }
        if (message.getType() == 1 && !(message.getGroup().hasPerson(message.getPerson1()))) {
            throw new MyPersonIdNotFoundException(message.getPerson1().getId());
        }
        if (message.getType() == 0) {
            Person person1 = message.getPerson1();
            Person person2 = message.getPerson2();
            person1.addSocialValue(message.getSocialValue());
            person2.addSocialValue(message.getSocialValue());
            ((MyPerson) person2).addMessage(message);
        }
        else {
            ((MyGroup) message.getGroup()).addSocialValue(message.getSocialValue());
        }
        messages.remove(message.getId());
    }

    public int querySocialValue(int id) throws PersonIdNotFoundException {
        Person person = getPerson(id);
        if (person == null) {
            throw new MyPersonIdNotFoundException(id);
        }
        return person.getSocialValue();
    }

    public List<Message> queryReceivedMessages(int id)
            throws PersonIdNotFoundException {
        Person person = getPerson(id);
        if (person == null) {
            throw new MyPersonIdNotFoundException(id);
        }
        return person.getReceivedMessages();
    }

    public int queryBestAcquaintance(int id) throws
            PersonIdNotFoundException, AcquaintanceNotFoundException {
        MyPerson person = (MyPerson) getPerson(id);
        if (person == null) {
            throw new MyPersonIdNotFoundException(id);
        }
        if (person.getAcquaintance().size() == 0) {
            throw new MyAcquaintanceNotFoundException(id);
        }
        return person.bestIdx();
    }

    public /*@ pure @*/ int queryCoupleSum() {
        int res = 0;
        for (Map.Entry<Integer, Person> i : people.entrySet()) {
            MyPerson p = (MyPerson) i.getValue();
            if (p.getAcquaintance().size() > 0) {
                MyPerson q = (MyPerson) getPerson(p.bestIdx());
                if (q.getAcquaintance().size() > 0 && q.bestIdx() == i.getKey()) {
                    ++ res;
                }
            }
        }
        return res >> 1;
    }

    public int modifyRelationOKTest(int id1, int id2, int value,
                                    HashMap<Integer, HashMap<Integer, Integer>> beforeData,
                                    HashMap<Integer, HashMap<Integer, Integer>> afterData) {
        if (beforeData.containsKey(id1) && beforeData.containsKey(id2) && id1 != id2 &&
                beforeData.get(id1).containsKey(id2) && beforeData.get(id1).get(id2) + value > 0) {
            return okTestPart1(id1, id2, value, beforeData, afterData);
        }
        else if (beforeData.containsKey(id1) && beforeData.containsKey(id2) && id1 != id2 &&
            beforeData.get(id1).containsKey(id2) && beforeData.get(id1).get(id2) + value <= 0) {
            return okTestPart2(id1, id2, value, beforeData, afterData);
        }
        else {
            return beforeData.equals(afterData) ? 0 : -1;
        }
    }

    private int okTestPart1(int id1, int id2, int value,
                            HashMap<Integer, HashMap<Integer, Integer>> beforeData,
                            HashMap<Integer, HashMap<Integer, Integer>> afterData) {
        int res = test1to3(id1, id2, beforeData, afterData);
        if (res > 0) {
            return res;
        }
        if (!beforeData.get(id1).containsKey(id2) || !afterData.get(id2).containsKey(id1)) {
            return 4;
        }
        if (beforeData.get(id1).get(id2) + value != afterData.get(id2).get(id1)) {
            return 5;
        }
        if (beforeData.get(id2).get(id1) + value != afterData.get(id1).get(id2)) {
            return 6;
        }
        if (beforeData.get(id1).size() != afterData.get(id1).size()) {
            return 7;
        }
        if (beforeData.get(id2).size() != afterData.get(id2).size()) {
            return 8;
        }
        for (int i : beforeData.get(id1).keySet()) {
            if (!afterData.get(id1).containsKey(i)) {
                return 9;
            }
        }
        for (int i : beforeData.get(id2).keySet()) {
            if (!afterData.get(id2).containsKey(i)) {
                return 10;
            }
        }
        for (int i : beforeData.get(id1).keySet()) {
            if (i == id1 || i == id2) {
                continue;
            }
            if (!Objects.equals(beforeData.get(id1).get(i), afterData.get(id1).get(i))) {
                return 11;
            }
        }
        for (int i : beforeData.get(id2).keySet()) {
            if (i == id1 || i == id2) {
                continue;
            }
            if (!Objects.equals(beforeData.get(id2).get(i), afterData.get(id2).get(i))) {
                return 12;
            }
        }
        return 0;
    }

    private int okTestPart2(int id1, int id2, int value,
                            HashMap<Integer, HashMap<Integer, Integer>> beforeData,
                            HashMap<Integer, HashMap<Integer, Integer>> afterData) {
        int res = test1to3(id1, id2, beforeData, afterData);
        if (res > 0) {
            return res;
        }
        if (afterData.get(id1).containsKey(id2) || afterData.get(id2).containsKey(id1)) {
            return 15;
        }
        if (beforeData.get(id1).size() + 1 != afterData.get(id1).size()) {
            return 16;
        }
        if (beforeData.get(id2).size() + 1 != afterData.get(id2).size()) {
            return 17;
        }
        for (int i : afterData.get(id1).keySet()) {
            if (!afterData.get(i).equals(beforeData.get(i))) {
                return 20;
            }
        }
        for (int i : afterData.get(id2).keySet()) {
            if (!afterData.get(i).equals(beforeData.get(i))) {
                return 21;
            }
        }
        return 0;
    }

    private int test1to3(int id1, int id2,
                         HashMap<Integer, HashMap<Integer, Integer>> beforeData,
                         HashMap<Integer, HashMap<Integer, Integer>> afterData) {
        if (beforeData.size() != afterData.size()) {
            return 1;
        }
        for (int i : beforeData.keySet()) {
            if (!afterData.containsKey(i)) {
                return 2;
            }
        }
        for (int i : beforeData.keySet()) {
            if (i == id1 || i == id2) {
                continue;
            }
            if (!beforeData.get(i).equals(afterData.get(i))) {
                return 3;
            }
        }
        return 0;
    }
}