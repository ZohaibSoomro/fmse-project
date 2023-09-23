-- Defining constant values for status of a task
enum Status{
	pending, started, finished
}
-- Defining Task
sig Task{
	id: one Int,
	description: one String,
	status: one Status
}
-- Defining User as a set of tasks
sig User{
	name: one String,
	tasks: set Task
}

-- Defining todo list with a set of users each having exactly 3 tasks
one sig ToDoList {
    users: set User
} {
    all u: users | #u.tasks = 3
}

-- Defininig some sample users
one sig SampleTasks {
    t1, t2, t3: Task
}

-- Assigning values to the sample tasks
run {
    SampleTasks.t1.id = 1
    SampleTasks.t1.description = "FMSE TEST"
    SampleTasks.t1.status = pending
    SampleTasks.t2.id = 2
    SampleTasks.t2.description = "MC LAB"
    SampleTasks.t2.status = started
    SampleTasks.t3.id= 3
    SampleTasks.t3.description = "WE PPT"
    SampleTasks.t3.status = finished
}

-- Defininig some sample users
one sig SampleUsers {
    u1, u2, u3: User
}

-- Assigning tasks to the sample users
run {
    SampleUsers.u1.tasks = SampleTasks.t1 + SampleTasks.t2
    SampleUsers.u2.tasks = SampleTasks.t2 + SampleTasks.t3
    SampleUsers.u3.tasks = SampleTasks.t1 + SampleTasks.t3
}

-- Defining some constraints on the to-do list
assert ToDoListConstraints {
    -- Each task must have a unique task ID
    all t1, t2: Task | t1 != t2 implies t1.id!= t2.id

    -- No two task should have same id within user's tasks
    all u: User | no t1, t2: u.tasks | t1.id = t2.id
}

--checking assersion for any counter examples
check  ToDoListConstraints

-- Runing the model
run {} for 3
