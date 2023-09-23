//Todo list program JML Specifiation
import java.util.*;

enum Status { 
    pending, started, finished 
}
class Task {
    private int id;
    private String description;
    private Status status;
    
    /* @requires s != null;
   @ requires i >= 0;
   @ requires d!= null;
   @ ensures status == s;
   @ ensures id == i;
   @ ensures description == d;
   @*/
   public Task(int i, String d, Status s) {
        id = i;
        description = d;
        status = s;
    }
    public int getId() {
        return id;
    }
    
    public String getDescription() {
        return description;
    }
    
    public Status getStatus() {
        return status;
    }
}

class User {
    private String name;
    private HashSet<Task> tasks;

//@ public invariant tasks.size() == 3;

//@ requires n != null;
//@ ensures name == n;
//@ ensures tasks.size() == 3;
    public User(String n, Task t1, Task t2, Task t3) {
        name = n;
        tasks = new HashSet<Task>();
        tasks.add(t1);
        tasks.add(t2);
        tasks.add(t3);
    }
//@ requires s == Status.pending || s == Status.started || s == Status.finished;
//@ requires t != null;
//@ ensures tasks.contains(t);
//@ ensures tasks.size() == \old(tasks.size()) + 1;
public void addTask(Task t, Status s) {
        t.getStatus() = s;
        tasks.add(t);
    }
public String getName() {
        return name;
    }
    
    public HashSet<Task> getTasks() {
        return tasks;
    }
}


public class ToDoList {
    private HashSet<User> users;

/*
-- Defining some constraints
-- Each user must have exactly three tasks assigned to them
-- Each task must have a unique task ID
-- No two task should have the same id within a user's tasks
*/
//@ public invariant(\forall Task t1,t2; t1 != t2 && t1.getId() != t2.getId);
//@ public invariant (\forall User u; u in users; u.getTasks().size() == 3);
//@ public invariant (\forall Task t1,t2; t1 in u1.getTasks() ; t2  in u2.getTasks());t1.getId() != t2.getId());
    public ToDoList() {
        users = new HashSet<User>();
    }
    
    public HashSet<User> getUsers() {
        return users;
    }

    /*@ requires u != null;
    @ ensures users.contains(u);
    @ ensures users.size() == \old(users.size()) + 1;
        @*/
    public void addUser(User u) {
        users.add(u);
    }


     /*@ requires t != null;
    @ ensures (\exists User u; u in users; t in u.getTasks());
     @*/
    public void addTaskToUser(Task t) {
        for (User u : users) {
            u.addTask(t);
        }
    }
}
