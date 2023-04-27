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
import exception.*;

import java.util.*;

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
        this.blockUpdate = false;
        this.tripleUpdate = false;
        people = new HashMap<>();
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

    /*@ public normal_behavior
     @ requires contains(id1) && contains(id2) && id1 != id2 && getPerson(id1).isLinked(getPerson(id2))
               && getPerson(id1).queryValue(getPerson(id2)) + value > 0;
     @ assignable people;
     @ 1 ensures people.length == \old(people.length);
     @ 2 ensures (\forall int i; 0 <= i && i < \old(people.length);
     @          (\exists int j; 0 <= j && j < people.length; people[j].getId() == \old(people[i]).getId()));
     @ 3 ensures (\forall int i; 0 <= i && i < people.length && \old(people[i].getId()) != id1 &&
     @     \old(people[i].getId()) != id2; \not_assigned(people[i]));
     @ 4 ensures getPerson(id1).isLinked(getPerson(id2)) && getPerson(id2).isLinked(getPerson(id1));
     @ 5 ensures getPerson(id1).queryValue(getPerson(id2)) == \old(getPerson(id1).queryValue(getPerson(id2))) + value;
     @ 6 ensures getPerson(id2).queryValue(getPerson(id1)) == \old(getPerson(id2).queryValue(getPerson(id1))) + value;
     @ 7 ensures getPerson(id1).acquaintance.length == \old(getPerson(id1).acquaintance.length);
     @ 8 ensures getPerson(id2).acquaintance.length == \old(getPerson(id2).acquaintance.length);
     @ 9 ensures (\forall int i; 0 <= i && i < getPerson(id1).acquaintance.length; getPerson(id1).acquaintance[i].equals(\old(getPerson(id1).acquaintance[i]));
     @ 10 ensures (\forall int i; 0 <= i && i < getPerson(id2).acquaintance.length; getPerson(id2).acquaintance[i].equals(\old(getPerson(id2).acquaintance[i]));
     @ 11 ensures (\forall int i; 0 <= i && i < getPerson(id1).acquaintance.length && getPerson(id1).acquaintance[i].getId() != id2;
     @             getPerson(id1).value[i] == \old(getPerson(id1).value[i]));
     @ 12 ensures (\forall int i; 0 <= i && i < getPerson(id2).acquaintance.length && getPerson(id2).acquaintance[i].getId() != id1;
     @             getPerson(id2).value[i] == \old(getPerson(id2).value[i]));
     @ 13 ensures getPerson(id1).value.length == getPerson(id1).acquaintance.length;
     @ 14 ensures getPerson(id2).value.length == getPerson(id2).acquaintance.length;
     @ also
     @ public normal_behavior
     @ requires contains(id1) && contains(id2) && id1 != id2 && getPerson(id1).isLinked(getPerson(id2))
     @         && getPerson(id1).queryValue(getPerson(id2)) + value <= 0;
     @ 1 ensures people.length == \old(people.length);
     @ 2 ensures (\forall int i; 0 <= i && i < \old(people.length);
     @          (\exists int j; 0 <= j && j < people.length; people[j] == \old(people[i])));
     @ 3 ensures (\forall int i; 0 <= i && i < people.length && \old(people[i].getId()) != id1 &&
     @     \old(people[i].getId()) != id2; \not_assigned(people[i]));
     @ 15 ensures !getPerson(id1).isLinked(getPerson(id2)) && !getPerson(id2).isLinked(getPerson(id1));
     @ 16 ensures \old(getPerson(id1).value.length) == getPerson(id1).acquaintance.length + 1;
     @ 17 ensures \old(getPerson(id2).value.length) == getPerson(id2).acquaintance.length + 1;
     @ 18 ensures getPerson(id1).value.length == getPerson(id1).acquaintance.length;
     @ 19 ensures getPerson(id2).value.length == getPerson(id2).acquaintance.length;
     @ 20 ensures (\forall int i; 0 <= i && i < getPerson(id1).acquaintance.length;
     @         \old(getPerson(id1).acquaintance[i]) == getPerson(id1).acquaintance[i] &&
     @          \old(getPerson(id1).value[i]) == getPerson(id1).value[i]);
     @ 21 ensures (\forall int i; 0 <= i && i < getPerson(id2).acquaintance.length;
     @         \old(getPerson(id2).acquaintance[i]) == getPerson(id2).acquaintance[i] &&
     @          \old(getPerson(id2).value[i]) == getPerson(id2).value[i]);
     @ also
     @ public exceptional_behavior
     @ assignable \nothing;
     @ requires !contains(id1) || !contains(id2) || !getPerson(id1).isLinked(getPerson(id2));
     @ signals (PersonIdNotFoundException e) !contains(id1);
     @ signals (PersonIdNotFoundException e) contains(id1) && !contains(id2);
     @ signals (EqualPersonIdException e) contains(id1) && contains(id2) && id1 == id2;
     @ signals (RelationNotFoundException e) contains(id1) && contains(id2) && id1 != id2 &&
     @         !getPerson(id1).isLinked(getPerson(id2));
     @*/
    public void modifyRelation(int id1, int id2, int value) throws PersonIdNotFoundException,
            EqualPersonIdException, RelationNotFoundException{
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
            tripleUpdate = false;
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
        HashMap<Integer, Integer> vis = new HashMap<>();
        vis.put(id1, id1);
        vis.put(id2, id2);
        Queue<Person> q1 = new LinkedList<>();
        Queue<Person> q2 = new LinkedList<>();
        q1.offer(getPerson(id1));
        q2.offer(getPerson(id2));
        while (!q1.isEmpty() && !q2.isEmpty()) {
            MyPerson now1 = (MyPerson) q1.poll();
            for (int i : now1.getAcquaintance().keySet()) {
                if (vis.containsKey(i)) {
                    if (vis.get(i) == id2)
                        return true;
                    continue;
                }
                vis.put(i, id1);
                q1.offer(getPerson(i));
            }
            MyPerson now2 = (MyPerson) q2.poll();
            assert now2 != null;
            for (int i : now2.getAcquaintance().keySet()) {
                if (vis.containsKey(i)) {
                    if (vis.get(i) == id1)
                        return true;
                    continue;
                }
                vis.put(i, id2);
                q2.offer(getPerson(i));
            }
        }
        return false;
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

    /*@ public normal_behavior
     @ requires !(\exists int i; 0 <= i && i < groups.length; groups[i].equals(group));
     @ assignable groups[*];
     @ ensures groups.length == \old(groups.length) + 1;
     @ ensures (\forall int i; 0 <= i && i < \old(groups.length);
     @          (\exists int j; 0 <= j && j < groups.length; groups[j] == (\old(groups[i]))));
     @ ensures (\exists int i; 0 <= i && i < groups.length; groups[i] == group);
     @ also
     @ public exceptional_behavior
     @ signals (EqualGroupIdException e) (\exists int i; 0 <= i && i < groups.length;
     @                                     groups[i].equals(group));
     @*/
    public void addGroup(/*@ non_null @*/Group group) throws EqualGroupIdException {
        if (groups.containsKey(group.getId())) {
            throw new MyEqualGroupIdException(group.getId());
        }
        groups.put(group.getId(), group);
    }

    /*@ public normal_behavior
      @ requires (\exists int i; 0 <= i && i < groups.length; groups[i].getId() == id);
      @ ensures (\exists int i; 0 <= i && i < groups.length; groups[i].getId() == id &&
      @         \result == groups[i]);
      @ also
      @ public normal_behavior
      @ requires (\forall int i; 0 <= i && i < groups.length; groups[i].getId() != id);
      @ ensures \result == null;
      @*/
    public /*@ pure @*/ Group getGroup(int id) {
        if (groups.containsKey(id)) {
            return groups.get(id);
        }
        return null;
    }


    /*@ public normal_behavior
      @ requires (\exists int i; 0 <= i && i < groups.length; groups[i].getId() == id2) &&
      @           (\exists int i; 0 <= i && i < people.length; people[i].getId() == id1) &&
      @            getGroup(id2).hasPerson(getPerson(id1)) == false &&
      @             getGroup(id2).people.length <= 1111;
      @ assignable getGroup(id2).people[*];
      @ ensures (\forall Person i; \old(getGroup(id2).hasPerson(i));
      @          getGroup(id2).hasPerson(i));
      @ ensures \old(getGroup(id2).people.length) == getGroup(id2).people.length - 1;
      @ ensures getGroup(id2).hasPerson(getPerson(id1));
      @ also
      @ public normal_behavior
      @ requires (\exists int i; 0 <= i && i < groups.length; groups[i].getId() == id2) &&
      @           (\exists int i; 0 <= i && i < people.length; people[i].getId() == id1) &&
      @            getGroup(id2).hasPerson(getPerson(id1)) == false &&
      @             getGroup(id2).people.length > 1111;
      @ assignable \nothing;
      @ also
      @ public exceptional_behavior
      @ signals (GroupIdNotFoundException e) !(\exists int i; 0 <= i && i < groups.length;
      @          groups[i].getId() == id2);
      @ signals (PersonIdNotFoundException e) (\exists int i; 0 <= i && i < groups.length;
      @          groups[i].getId() == id2) && !(\exists int i; 0 <= i && i < people.length;
      @           people[i].getId() == id1);
      @ signals (EqualPersonIdException e) (\exists int i; 0 <= i && i < groups.length;
      @          groups[i].getId() == id2) && (\exists int i; 0 <= i && i < people.length;
      @           people[i].getId() == id1) && getGroup(id2).hasPerson(getPerson(id1));
      @*/
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


    /*@ public normal_behavior
      @ requires (\exists int i; 0 <= i && i < groups.length; groups[i].getId() == id);
      @ ensures \result == getGroup(id).getValueSum();
      @ also
      @ public exceptional_behavior
      @ signals (GroupIdNotFoundException e) !(\exists int i; 0 <= i && i < groups.length;
      @          groups[i].getId() == id);
      @*/
    public /*@ pure @*/ int queryGroupValueSum(int id) throws GroupIdNotFoundException {
        Group group = getGroup(id);
        if (group == null) {
            throw new MyGroupIdNotFoundException(id);
        }
        return group.getValueSum();
    }

    /*@ public normal_behavior
      @ requires (\exists int i; 0 <= i && i < groups.length; groups[i].getId() == id);
      @ ensures \result == getGroup(id).getAgeVar();
      @ also
      @ public exceptional_behavior
      @ signals (GroupIdNotFoundException e) !(\exists int i; 0 <= i && i < groups.length;
      @          groups[i].getId() == id);
      @*/
    public /*@ pure @*/ int queryGroupAgeVar(int id) throws GroupIdNotFoundException {
        Group group = getGroup(id);
        if (group == null) {
            throw new MyGroupIdNotFoundException(id);
        }
        return group.getAgeVar();
    }

    /*@ public normal_behavior
      @ requires (\exists int i; 0 <= i && i < groups.length; groups[i].getId() == id2) &&
      @           (\exists int i; 0 <= i && i < people.length; people[i].getId() == id1) &&
      @            getGroup(id2).hasPerson(getPerson(id1)) == true;
      @ assignable getGroup(id2).people[*];
      @ ensures (\forall Person i; getGroup(id2).hasPerson(i);
      @          \old(getGroup(id2).hasPerson(i)));
      @ ensures \old(getGroup(id2).people.length) == getGroup(id2).people.length + 1;
      @ ensures getGroup(id2).hasPerson(getPerson(id1)) == false;
      @ also
      @ public exceptional_behavior
      @ signals (GroupIdNotFoundException e) !(\exists int i; 0 <= i && i < groups.length;
      @          groups[i].getId() == id2);
      @ signals (PersonIdNotFoundException e) (\exists int i; 0 <= i && i < groups.length;
      @          groups[i].getId() == id2) && !(\exists int i; 0 <= i && i < people.length;
      @           people[i].getId() == id1);
      @ signals (EqualPersonIdException e) (\exists int i; 0 <= i && i < groups.length;
      @          groups[i].getId() == id2) && (\exists int i; 0 <= i && i < people.length;
      @           people[i].getId() == id1) && !getGroup(id2).hasPerson(getPerson(id1));
      @*/
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

    //@ ensures \result == (\exists int i; 0 <= i && i < messages.length; messages[i].getId() == id);
    public /*@ pure @*/ boolean containsMessage(int id) {
        return messages.containsKey(id);
    }

    /*@ public normal_behavior
      @ requires !(\exists int i; 0 <= i && i < messages.length; messages[i].equals(message)) &&
      @           ((message.getType() == 0) ==> (message.getPerson1() != message.getPerson2()));
      @ assignable messages;
      @ ensures messages.length == \old(messages.length) + 1;
      @ ensures (\forall int i; 0 <= i && i < \old(messages.length);
      @          (\exists int j; 0 <= j && j < messages.length; messages[j].equals(\old(messages[i]))));
      @ ensures (\exists int i; 0 <= i && i < messages.length; messages[i].equals(message));
      @ also
      @ public exceptional_behavior
      @ signals (EqualMessageIdException e) (\exists int i; 0 <= i && i < messages.length;
      @                                     messages[i].equals(message));
      @ signals (EqualPersonIdException e) !(\exists int i; 0 <= i && i < messages.length;
      @                                     messages[i].equals(message)) &&
      @                                     message.getType() == 0 && message.getPerson1() == message.getPerson2();
      @*/
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

    /*@ public normal_behavior
      @ requires containsMessage(id);
      @ ensures (\exists int i; 0 <= i && i < messages.length; messages[i].getId() == id &&
      @         \result == messages[i]);
      @ public normal_behavior
      @ requires !containsMessage(id);
      @ ensures \result == null;
      @*/
    public /*@ pure @*/ Message getMessage(int id) {
        if (messages.containsKey(id)) {
            return messages.get(id);
        }
        return null;
    }


    /*@ public normal_behavior
      @ requires containsMessage(id) && getMessage(id).getType() == 0 &&
      @          getMessage(id).getPerson1().isLinked(getMessage(id).getPerson2()) &&
      @          getMessage(id).getPerson1() != getMessage(id).getPerson2();
      @ assignable messages;
      @ assignable getMessage(id).getPerson1().socialValue;
      @ assignable getMessage(id).getPerson2().messages, getMessage(id).getPerson2().socialValue;
      @ ensures \old(getMessage(id)).getPerson1().getSocialValue() ==
      @         \old(getMessage(id).getPerson1().getSocialValue()) + \old(getMessage(id)).getSocialValue() &&
      @         \old(getMessage(id)).getPerson2().getSocialValue() ==
      @         \old(getMessage(id).getPerson2().getSocialValue()) + \old(getMessage(id)).getSocialValue();
      @ ensures !containsMessage(id) && messages.length == \old(messages.length) - 1 &&
      @         (\forall int i; 0 <= i && i < \old(messages.length) && \old(messages[i].getId()) != id;
      @         (\exists int j; 0 <= j && j < messages.length; messages[j].equals(\old(messages[i]))));
      @ ensures (\forall int i; 0 <= i && i < \old(getMessage(id).getPerson2().getMessages().size());
      @          \old(getMessage(id)).getPerson2().getMessages().get(i+1) == \old(getMessage(id).getPerson2().getMessages().get(i)));
      @ ensures \old(getMessage(id)).getPerson2().getMessages().get(0) == \old(getMessage(id));
      @ ensures \old(getMessage(id)).getPerson2().getMessages().size() == \old(getMessage(id).getPerson2().getMessages().size()) + 1;
      @ also
      @ public normal_behavior
      @ requires containsMessage(id) && getMessage(id).getType() == 1 &&
      @           getMessage(id).getGroup().hasPerson(getMessage(id).getPerson1());
      @ assignable people[*].socialValue, messages;
      @ ensures (\forall Person p; \old(getMessage(id)).getGroup().hasPerson(p); p.getSocialValue() ==
      @         \old(p.getSocialValue()) + \old(getMessage(id)).getSocialValue());
      @ ensures (\forall int i; 0 <= i && i < people.length && !\old(getMessage(id)).getGroup().hasPerson(people[i]);
      @          \old(people[i].getSocialValue()) == people[i].getSocialValue());
      @ ensures !containsMessage(id) && messages.length == \old(messages.length) - 1 &&
      @         (\forall int i; 0 <= i && i < \old(messages.length) && \old(messages[i].getId()) != id;
      @         (\exists int j; 0 <= j && j < messages.length; messages[j].equals(\old(messages[i]))));
      @ also
      @ public exceptional_behavior
      @ signals (MessageIdNotFoundException e) !containsMessage(id);
      @ signals (RelationNotFoundException e) containsMessage(id) && getMessage(id).getType() == 0 &&
      @          !(getMessage(id).getPerson1().isLinked(getMessage(id).getPerson2()));
      @ signals (PersonIdNotFoundException e) containsMessage(id) && getMessage(id).getType() == 1 &&
      @          !(getMessage(id).getGroup().hasPerson(getMessage(id).getPerson1()));
      @*/
    public void sendMessage(int id) throws
            RelationNotFoundException, MessageIdNotFoundException, PersonIdNotFoundException {
        Message message = getMessage(id);
        if (message == null) {
            throw new MyMessageIdNotFoundException(id);
        }
        if (message.getType() == 0 && !message.getPerson1().isLinked(message.getPerson2())) {
            throw new MyRelationNotFoundException(message.getPerson1().getId(), message.getPerson2().getId());
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
            MyGroup group = (MyGroup) message.getGroup();
            group.addSocialValue(message.getSocialValue());
        }
        messages.remove(message.getId());
    }

    /*@ public normal_behavior
      @ requires contains(id);
      @ ensures \result == getPerson(id).getSocialValue();
      @ also
      @ public exceptional_behavior
      @ signals (PersonIdNotFoundException e) !contains(id);
      @*/
    public /*@ pure @*/ int querySocialValue(int id) throws PersonIdNotFoundException {
        Person person = getPerson(id);
        if (person == null) {
            throw new MyPersonIdNotFoundException(id);
        }
        return person.getSocialValue();
    }


    /*@ public normal_behavior
      @ requires contains(id);
      @ ensures \result == getPerson(id).getReceivedMessages();
      @ also
      @ public exceptional_behavior
      @ signals (PersonIdNotFoundException e) !contains(id);
      @*/
    public /*@ pure @*/ List<Message> queryReceivedMessages(int id) throws PersonIdNotFoundException {
        Person person = getPerson(id);
        if (person == null) {
            throw new MyPersonIdNotFoundException(id);
        }
        return person.getReceivedMessages();
    }


    /*@ public normal_behavior
      @ requires contains(id) && getPerson(id).acquaintance.length != 0;
      @ ensures \result == (\min int bestIdx;
      @     0 <= bestIdx && bestIdx < getPerson(id).acquaintance.length &&
      @     (\forall int i; 0 <= i && i < getPerson(id).acquaintance.length;
      @         getPerson(id).value[i] <= getPerson(id).value[bestIdx]);
      @     getPerson(id).acquaintance[bestIdx].getId());
      @ public exceptional_behavior
      @ signals (PersonIdNotFoundException e) !contains(id);
      @ signals (AcquaintanceNotFoundException e) contains(id) &&
      @         getPerson(id).acquaintance.length == 0;
      @*/
    public /*@ pure @*/ int queryBestAcquaintance(int id) throws
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


    /*@ ensures \result ==
      @         (\sum int i, j; 0 <= i && i < j && j < people.length
      @                         && people[i].acquaintance.length > 0 && queryBestAcquaintance(people[i].getId()) == people[j].getId()
      @                         && people[j].acquaintance.length > 0 && queryBestAcquaintance(people[j].getId()) == people[i].getId();
      @                         1);
      @*/
    public /*@ pure @*/ int queryCoupleSum() {

    }

    public int modifyRelationOKTest(int id1, int id2, int value,
                                    HashMap<Integer, HashMap<Integer, Integer>> beforeData,
                                    HashMap<Integer, HashMap<Integer, Integer>> afterData) {

    }

}
