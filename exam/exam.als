sig ProcessID {}
sig Process{ process: ProcessID -> ProcessState }

abstract sig ProcessState {}
one sig active extends ProcessState {}
one sig waiting extends ProcessState {}
one sig ready extends ProcessState {}

fact no_arbitrary_state {
    all p : Process, id : ProcessID |
     one p.process[id]
}

fact lone_active {
    all p : Process |
    lone p.process :> active
}

fact no_ready {
    all p : Process |
    no p.process :> active implies
    no p.process :> ready
}

pred add [id : ProcessID, p,p' : Process]{
    no p.process[id] 
    p'.process = p.process ++ (id -> waiting)
}

fun check_state [p:Process, id: ProcessID] : one ProcessState{
    p.process[id]
}

assert check_add {
    all p,p' : Process , id : ProcessID |
    add[id,p,p'] =>
    check_state[p', id] in waiting
}

check check_add for 5 expect 0

pred change_state[p,p' : Process , id : ProcessID, s : ProcessState]{
    p'.process = p.process + (id -> s)
}

pred Ready[p, p': Process, id : ProcessID]{
    p.process[id] in waiting 
    ( one p.process :> active ) implies change_state[p,p',id,ready]  
    ( no p.process :> active ) implies change_state[p,p',id,active]
}

assert check_ready {
    all p,p' :Process , id : ProcessID |
    p.process[id] in waiting and
    Ready[p,p',id] implies (check_state[p', id] in waiting or check_state[p',id] in active ) 
}

check check_ready for 5 expect 0

fun check_activeid [p: Process ] : ProcessID {
    ( p.process :> active ).active
}

pred Swap[p,p' : Process]{
    all id: ProcessID |(
    p.process[id] in active implies
    p'.process[id] in waiting )
}

run Swap for 4

assert check_swap{
    all p, p': Process |
    (one p.process :> active and
    Swap[p,p'] implies lone p'.process :> active)
}

check check_swap for 5 expect 1