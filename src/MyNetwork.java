import com.oocourse.spec3.exceptions.EqualGroupIdException;
import com.oocourse.spec3.exceptions.EqualMessageIdException;
import com.oocourse.spec3.exceptions.EqualPersonIdException;
import com.oocourse.spec3.exceptions.EqualRelationException;
import com.oocourse.spec3.exceptions.PersonIdNotFoundException;
import com.oocourse.spec3.exceptions.EqualEmojiIdException;
import com.oocourse.spec3.exceptions.PathNotFoundException;
import com.oocourse.spec3.exceptions.GroupIdNotFoundException;
import com.oocourse.spec3.exceptions.MessageIdNotFoundException;
import com.oocourse.spec3.exceptions.EmojiIdNotFoundException;
import com.oocourse.spec3.exceptions.AcquaintanceNotFoundException;
import com.oocourse.spec3.exceptions.RelationNotFoundException;
import com.oocourse.spec3.main.Group;
import com.oocourse.spec3.main.Message;
import com.oocourse.spec3.main.Network;
import com.oocourse.spec3.main.Person;
import exception.MyEqualRelationException;
import exception.MyEqualPersonIdException;
import exception.MyEqualGroupIdException;
import exception.MyEqualMessageIdException;
import exception.MyEqualEmojiIdException;
import exception.MyRelationNotFoundException;
import exception.MyPersonIdNotFoundException;
import exception.MyGroupIdNotFoundException;
import exception.MyMessageIdNotFoundException;
import exception.MyEmojiIdNotFoundException;
import exception.MyPathNotFoundException;
import exception.MyAcquaintanceNotFoundException;

import java.util.HashMap;
import java.util.Map;
import java.util.ArrayList;
import java.util.Objects;
import java.util.List;

public class MyNetwork implements Network {
    private int blockSum;
    private int tripleSum;
    private boolean blockUpdate;
    private boolean tripleUpdate;
    private final HashMap<Integer, Person> people;//id->person
    private final HashMap<Integer, Group> groups;//id->group
    private final HashMap<Integer, Message> messages;//id->message
    private final HashMap<Integer, Integer> emojiIdMap;//emojiId->emojiHeat

    public MyNetwork() {
        this.blockSum = 0;
        this.tripleSum = 0;
        this.blockUpdate = true;
        this.tripleUpdate = false;
        this.people = new HashMap<>();
        this.groups = new HashMap<>();
        this.messages = new HashMap<>();
        this.emojiIdMap = new HashMap<>();
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
        return GraphHandler.isCircle(id1, id2, people);
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
            EqualMessageIdException, EmojiIdNotFoundException, EqualPersonIdException {
        if (containsMessage(message.getId())) {
            throw new MyEqualMessageIdException(message.getId());
        }
        if (message instanceof MyEmojiMessage) {
            MyEmojiMessage emojiMessage = (MyEmojiMessage) message;
            if (!containsEmojiId(emojiMessage.getEmojiId())) {
                throw new MyEmojiIdNotFoundException(emojiMessage.getEmojiId());
            }
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
            if (message instanceof MyRedEnvelopeMessage) {
                int money = ((MyRedEnvelopeMessage) message).getMoney();
                person1.addMoney(-money);
                person2.addMoney(money);
            }
            if (message instanceof MyEmojiMessage) {
                int emojiId = ((MyEmojiMessage) message).getEmojiId();
                emojiIdMap.replace(emojiId, emojiIdMap.get(emojiId) + 1);
            }
        }
        else {
            ((MyGroup) message.getGroup()).addSocialValue(message.getSocialValue());
            if (message instanceof MyRedEnvelopeMessage) {
                int money = ((MyRedEnvelopeMessage) message).getMoney();
                int size = message.getGroup().getSize();
                int moneyPerPerson = money / size;
                Person person1 = message.getPerson1();
                person1.addMoney(-moneyPerPerson * (size - 1));
                ((MyGroup) message.getGroup()).addMoney(moneyPerPerson, person1.getId());
            }
            if (message instanceof MyEmojiMessage) {
                int emojiId = ((MyEmojiMessage) message).getEmojiId();
                emojiIdMap.replace(emojiId, emojiIdMap.get(emojiId) + 1);
            }
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

    public boolean containsEmojiId(int id) {
        return emojiIdMap.containsKey(id);
    }

    public void storeEmojiId(int id) throws EqualEmojiIdException {
        if (containsEmojiId(id)) {
            throw new MyEqualEmojiIdException(id);
        }
        emojiIdMap.put(id, 0);
    }

    public int queryMoney(int id) throws PersonIdNotFoundException {
        if (!contains(id)) {
            throw new MyPersonIdNotFoundException(id);
        }
        return getPerson(id).getMoney();
    }

    public int queryPopularity(int id) throws EmojiIdNotFoundException {
        if (!containsEmojiId(id)) {
            throw new MyEmojiIdNotFoundException(id);
        }
        return emojiIdMap.get(id);
    }

    public int deleteColdEmoji(int limit) {
        // delete emojiId
        for (Map.Entry<Integer, Integer> i : emojiIdMap.entrySet()) {
            if (i.getValue() < limit) {
                emojiIdMap.remove(i.getKey());
            }
        }
        // delete messages
        for (Map.Entry<Integer, Message> i : messages.entrySet()) {
            if (i.getValue() instanceof MyEmojiMessage) {
                MyEmojiMessage m = (MyEmojiMessage) i.getValue();
                if (!containsEmojiId(m.getEmojiId())) {
                    messages.remove(i.getKey());
                }
            }
        }
        return emojiIdMap.size();
    }

    public void clearNotices(int personId) throws PersonIdNotFoundException {
        if (!contains(personId)) {
            throw new MyPersonIdNotFoundException(personId);
        }
        ((MyPerson) getPerson(personId)).clearNotices();
    }

    public int queryLeastMoments(int id) throws PersonIdNotFoundException, PathNotFoundException {
        if (!contains(id)) {
            throw new MyPersonIdNotFoundException(id);
        }
        int result = GraphHandler.queryLeastMoment(id, people);
        if (result == -1) {
            throw new MyPathNotFoundException(id);
        }
        return result;
    }

    public int deleteColdEmojiOKTest(int limit, ArrayList<HashMap<Integer, Integer>> beforeData,
                                     ArrayList<HashMap<Integer, Integer>> afterData, int result) {
        HashMap<Integer, Integer> beforeEmojiId = beforeData.get(0);
        HashMap<Integer, Integer> afterEmojiId = afterData.get(0);
        int count = 0;
        for (int i : beforeEmojiId.keySet()) {
            if (beforeEmojiId.get(i) >= limit) {
                ++ count;
                if (!afterEmojiId.containsKey(i)) {
                    return 1;
                }
            }
        }
        for (int i : afterEmojiId.keySet()) {
            if (!beforeEmojiId.containsKey(i)) {
                return 2;
            }
            if (!Objects.equals(afterEmojiId.get(i), beforeEmojiId.get(i))) {
                return 2;
            }
        }
        if (count != afterEmojiId.size()) {
            return 3;
        }
        HashMap<Integer, Integer> beforeMessage = beforeData.get(1);
        HashMap<Integer, Integer> afterMessage = afterData.get(1);
        for (int i : beforeMessage.keySet()) {
            if (beforeMessage.get(i) == null) {
                ++ count;
                if (!afterMessage.containsKey(i) || afterMessage.get(i) != null) {
                    return 6;
                }
            }
            if (afterEmojiId.containsKey(beforeMessage.get(i))) {
                if (!afterMessage.containsKey(i) ||
                        !Objects.equals(afterMessage.get(i), beforeMessage.get(i))) {
                    return 5;
                }
            }
        }
        if (count != afterMessage.size()) {
            return 7;
        }
        if (result != afterEmojiId.size()) {
            return 8;
        }
        return 0;
    }

}