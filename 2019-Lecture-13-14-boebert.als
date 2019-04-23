module boebert

// we impose an "ordering" on States, which allows us to talk about entire
// execution sequences of the form s0, s1, s2, ..., sn where s0 is the initial
// state, and s1 is the state obtained after the occurrence of the first operation,
// then state s2 follows from s1 after some operation happens, etc. all the way
// to the final state sn
open util/ordering[State] as ord

// models data in the system
sig Data {}

// we model just two access rights, Read and Write
abstract sig Rights {}
one sig Read, Write extends Rights {}

// we model just two classifications, High and Low
abstract sig Classification {}
one sig High, Low extends Classification {}

// objects are things that have a classification
abstract sig Object {clas : one Classification}

// a capability is a special kind of data item that identifies some
// target object that it grants access to, along with a set of
// access rights that define what operations the capability authorises
// to be performed on the target object
sig Cap extends Data { target : one Object, perms : set Rights }

// objects are either memory Segments or Actors
sig Segment extends Object {}
sig Actor extends Object {}

// memory Segments hold Data, while Actors hold Capabilities
// which they can use to perform operations on memory Segments
// a State of the system models this information
sig State {
  segsdata : Segment -> set Data,
  actorscaps : Actor -> set Cap
}

// the write operation involves some Actor a writing Data d to a
// memory Segment o, authorised by Capability c
// - doing so causes a state change to occur from state s to s'
// - writing data to a Segment alters no Actor's capabilities
// - it does update the data of the Segment o being written to to
//    include the Data d that is being written.
// - if the Data d being written is a Capability, then the Actor a
//    must possess that Capability (to model the idea that Caps
//    can never be forged)
// - naturally, the Actor a must possess the Capability c that is
//   authorising the write operation. this Cap must authorise
//   Writing to Segment o
pred write [s, s' : State] {
  some a : Actor, o : Segment, d : Data, c : Cap {
    s'.actorscaps = s.actorscaps and
    s'.segsdata = s.segsdata + o -> d and
    (d in Cap implies d in s.actorscaps[a]) and
    (c in s.actorscaps[a] and o = c.target and Write in c.perms)
  }
}

// the read operation involves some Actor a reading Data d from
// a memory Segment o, authorised by Capability c
// - doing so doesn't change any Segment's Data
// - if the Data d being read is a Cap, it is added to the Actor a's
//    set of Caps that they possess; however, the Actor is allowed to
//    get the Cap in this way only if its access rights are not greater
//    than those of the Cap c that authorises the read action
// - otherwise, the Caps all Actors are unchanged
// - naturally, the Data being read must be in the Segment o,
// - and the Cap c must be possessed by the Actor a and it must
//    correctly authorise the Read of Segment o
pred read [s, s' : State] {
 some a : Actor, o : Segment, d : Data, c : Cap {
    s'.segsdata = s.segsdata and
    s'.actorscaps = 
      (d in Cap and d.perms in c.perms => 
            s.actorscaps + a -> d 
       else 
            s.actorscaps) and
    (d in s.segsdata[o]) and
    (c in s.actorscaps[a] and o = c.target and Read in c.perms)
  }
}

// a state transition occurs when either a read or write operation happens
// We exclude transitions that don't modify the state as they're irrelevant
pred state_transition [s, s' : State] {
    (read [s,s'] or write [s,s']) and 
    (s.actorscaps != s'.actorscaps or s.segsdata != s'.segsdata)
}


// we define what it means for a State to be "safe", which essentially
// means that it satisfies the Simple Security Property and the *-Property
// of the Bell LaPadula model:
//   1. "no read up": no Low Actor a possesses a Read Cap to a High object
//   2. "no write down": no High Actor a possesses a Write Cap to a Low object
pred safe_state [s : State] {
  (all a : Actor, c : Cap {
   c in s.actorscaps[a] implies (
   ((a.clas = Low and c.target.clas = High) implies Read not in c.perms)
   and
   ((a.clas = High and c.target.clas = Low) implies Write not in c.perms)
  ) 
 })
}

// show an example of a safe state
pred show_safe_state {
  some s : State | safe_state [s]
}
run show_safe_state for 2 expect 1


// asserts that a single write operation can never cause a safe state
// to become unsafe
assert write_safe {
  all s, s' : State | 
    write [s,s'] and safe_state[s] implies safe_state[s']
}
check write_safe for 10 expect 0
// this tells us that writes on their own can't make a state unsafe

// asserts the same thing for read operations
assert read_safe {
  all s, s' : State | 
    read [s,s'] and safe_state[s] implies safe_state[s']
}
check read_safe for 3 but 2 State expect 1
// this finds a counterexample, telling us that reads can make a
// safe state unsafe

// on its own this tell us that there might be an attack, but so
// far we don't know what the attack is.
// To have Alloy try to generate an attack, we need to talk about 
// multiple operations occurring one after the other in a sequence
// we do that as follows


// we first declare an axiom stating that
// for all states s, the next state after s in the ordering on states
// is one that follows from a single state transition, i.e. a single
// read or write operation occurring. Thus the ordering on states
// gives us a sequence of states representing some sequence of
// read and write events that occur in the system. This sequence
// of states (the ordering) captures a sequence of read and write
// operations occuring, i.e. an execution sequence.
fact state_transition {
  all s: State, s': ord/next[s] {
    state_transition[s,s']  
  }
}

pred show_example_execution_sequence {}

// show an execution seuqnece involving 2 states, i.e. the occurrence
// of a single operation (read or write)
run show_example_execution_sequence for 3 but 2 State expect 1

// show an execution sequence involving 3 states, i.e. two 
// consecutive operations
run show_example_execution_sequence for 3 expect 1

// assert that all execution sequences beginning in a safe stete,
// always end in a safe state, i.e. can never reach an unsafe state
// Put another way, this asserts that no sequence of reads and writes
// that can occur can ever make a safe state unafe.
assert no_violation {
   safe_state [ord/first] implies safe_state [ord/last]
}

check no_violation for 3 but 2 State expect 1
// this finds a counterexample, but one in which in the initial state
// there is a Segment that already holds a Cap that violates the
// spirit of the Bell-LaPadula security properties. 

// We therefore define a stronger initial condition to rule out
// this possibility.
//
// A stronger version of the safe state condition that also forbids
// High memory Segments from containing Low Write Caps and
// Low memory Segments from containing High Read Caps.
// This essentially extends the Bell-LaPadula properties to apply to
// Segments as well as Actors
pred safe_state_strong [s : State] {
  (all a : Actor, c : Cap {
   c in s.actorscaps[a] implies (
   ((a.clas = High and c.target.clas = Low) implies Write not in c.perms)
   and
   ((a.clas = Low and c.target.clas = High) implies Read not in c.perms)
  ) 
 }) and
 all a : Segment, c : Cap {
   c in s.segsdata[a] implies (
   ((a.clas = High and c.target.clas = Low) implies Write not in c.perms)
   and
   ((a.clas = Low and c.target.clas = High) implies Read not in c.perms)
  ) 
 }
}


// an assertion to try to find an attack beginning from a state
// satisfying the stronger safety condition, i.e. one that doesn't
// violate the spirit of Bell-LaPadula security policy
assert no_violation_from_strong {
   safe_state_strong [ord/first] implies safe_state [ord/last]
}


// this check finds an attack analogous to Boebert's
check no_violation_from_strong for 3 expect 1

