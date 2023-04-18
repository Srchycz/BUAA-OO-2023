package com.oocourse.spec1.main;

public interface Person extends Comparable<Person> {

    /*@ public instance model int id;
      @ public instance model non_null String name;
      @ public instance model int age;
      @ public instance model non_null Person[] acquaintance;
      @ public instance model non_null int[] value;
      @*/


    /*@ invariant acquaintance!= null && value != null && acquaintance.length == value.length &&
      @  (\forall int i,j; 0 <= i && i < j && j < acquaintance.length;
      @   !acquaintance[i].equals(acquaintance[j]));*/

    //@ ensures \result == id;
    public /*@ pure @*/ int getId();

    //@ ensures \result.equals(name);
    public /*@ pure @*/ String getName();

    //@ ensures \result == age;
    public /*@ pure @*/ int getAge();

    /*@ also
      @ public normal_behavior
      @ requires obj != null && obj instanceof Person;
      @ assignable \nothing;
      @ ensures \result == (((Person) obj).getId() == id) && (((Person) obj).getName().equals(name)) &&
      @                    (((Person) obj).getAge() == age) &&
      @                    (\forall int i; 0 <= i && i < ((Person) obj).getAcquaintance().length; acquaintance[i].equals(((Person) obj).getAcquaintance().get(i))) &&
      @                    (\forall int i; 0 <= i && i < ((Person) obj).getAcquaintance().length; value[i] == (((Person) obj).queryValue(((Person) obj).getAcquaintance().get(i)))) &&
      @                    (((Person) obj).getAcquaintance().length == acquaintance.length);
      @ also
      @ public normal_behavior
      @ requires obj == null || !(obj instanceof Person);
      @ assignable \nothing;
      @ ensures \result == false;
      @*/
    public /*@ pure @*/ boolean equals(Object obj);

    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures \result == (\exists int i; 0 <= i && i < acquaintance.length; 
      @                     acquaintance[i].equals(person) || person.equals(this);
      @*/
    public /*@ pure @*/ boolean isLinked(Person person);

    /*@ public normal_behavior
      @ requires (\exists int i; 0 <= i && i < acquaintance.length; 
      @          acquaintance[i].equals(person));
      @ assignable \nothing;
      @ ensures (\exists int i; 0 <= i && i < acquaintance.length; 
      @         acquaintance[i].equals(person) && \result == value[i]);
      @ also
      @ public normal_behavior
      @ requires (\forall int i; 0 <= i && i < acquaintance.length; 
      @          acquaintance[i].getId() != person.getId());
      @ ensures \result == 0;
      @*/
    public /*@ pure @*/ int queryValue(Person person);
}
