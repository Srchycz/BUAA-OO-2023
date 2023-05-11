import com.oocourse.spec3.main.Group;
import com.oocourse.spec3.main.Person;
import com.oocourse.spec3.main.RedEnvelopeMessage;
public class MyRedEnvelopeMessage extends MyMessage implements RedEnvelopeMessage {

    private final int money;

    /*@ ensures type == 0;
     @ ensures group == null;
     @ ensures id == messageId;
     @ ensures person1 == messagePerson1;
     @ ensures person2 == messagePerson2;
     @ ensures money == luckyMoney;
     @*/
    public MyRedEnvelopeMessage(int messageId, int luckyMoney, Person messagePerson1, Person messagePerson2) {
        super(messageId, luckyMoney * 5, messagePerson1, messagePerson2);
        this.money = luckyMoney;
    }

    /*@ ensures type == 1;
      @ ensures person2 == null;
      @ ensures id == messageId;
      @ ensures person1 == messagePerson1;
      @ ensures group == messageGroup;
      @ ensures money == luckyMoney;
      @*/
    public MyRedEnvelopeMessage(int messageId, int luckyMoney, Person messagePerson1, Group messageGroup) {
        super(messageId, luckyMoney * 5, messagePerson1, messageGroup);
        this.money = luckyMoney;
    }
    //@ public instance model int money;

    //@ public invariant socialValue == money * 5;

    //@ ensures \result == money;
    public /*@ pure @*/ int getMoney() {
        return this.money;
    }
}
