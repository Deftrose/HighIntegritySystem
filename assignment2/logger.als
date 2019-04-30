// ===========================================================================
// SWEN90010 2019 - Assignment 2 Submission
// by <INSERT BOTH NAMES, STUDENT NUMBERS, HERE>
// ===========================================================================

module logger
open util/ordering[State] as ord

// =========================== System State ==================================

// the type of network log messages
sig LogMessage {}

// meta information in the model that identifies the last action performed
abstract sig Action {}
one sig SendLogMessage, RecvLogMessage 
        extends Action {}

abstract sig AttackerAction extends Action {}
one sig DropMessage, FabricateMessage, ReplayMessage extends AttackerAction {}

// The system state
sig State {
  network : lone LogMessage,       // Network state: holds up to one message
  log     : seq LogMessage,        // The log: a sequence of messages
  last_action : lone Action,       // identifies the most recent action 
                                   // performed
}

// an axiom that restricts the model to never allow more than one messasge on
// the network at a time; a simplifying assumption to ease the analysis
fact {
  all s : State | lone s.network
}

// =========================== Initial State =================================

// The initial state of the system:
//   - empty network, 
//   - log is empty
pred Init[s : State] {
  no s.network and no s.log.elems and
  no s.last_action
}

// =========================== Actions =======================================

// Models the action in which a LogMessage log message is sent
// Precondition: the network is empty
// Postcondition: network contains a new message
//                last_action is SendLogMessage
//                and nothing else changes
pred send_log_message[s, s' : State] {
  no s.network and
  s'.last_action = SendLogMessage and
  s'.log = s.log and
  (some msg : LogMessage | 
    (s'.network = s.network + msg))
}

// Models the action in which a log message is received
// by the logger, causing the log to be updated
// and the message to be removed from the network.
// Precondition: exists some LogMessage message m on network
// Postcondition: contents of message m added to the log
//                message m is removed from the network
//                last_action is RecvLogMessage
pred recv_log_message[s, s' : State] {
  (some msg : LogMessage | 
       msg in s.network and s'.log = s.log.add[msg] and
       s'.network = s.network - msg) and
  s'.last_action = RecvLogMessage
}

// =========================== Attacker Actions ==============================

// Models the action in which the attacker intercepts a message and prevent it being received
// by removing it from the network
// Precondition: exists some LogMessage msg on network
// Postcondition: the messages doesn't exist 
//			and message log will be changed
pred attacker_action_drop[s, s' : State] {
  (some msg : LogMessage |
	msg in s.network and no s'.network ) and
	s'.last_action = DropMessage and
	s'.log = s.log
}

assert attack_drop {
	all s,s' : State | attacker_action_drop[s,s'] implies ( no s'.network and some s.network)
}

check attack_drop for 10 expect 0

// Models the action in which the attacker invents a new log message and injects it into the network
// Precondition: there are no messages in the network
// Postcondition: the message fabricated by attacker is added into the network
// 			and message log will be changed
pred attacker_action_fabricate[s, s' : State] {
  (no s.network and some msg : LogMessage |
	msg in s'.network ) and
	s'.last_action = FabricateMessage and
	s'.log = s.log
}

assert attack_fabricate {
	all s,s': State | attacker_action_fabricate[s,s'] implies ( some s'.network and no s.network )
}

check attack_fabricate for 10 expect 0

// Models the action in which the attacker inject an old message which already exists in the log
// Precondition: there are no messages in the network and the msg is already in some previous network of states
// Postcondition: the msg is added to the network
//			and message log will be changed
// s:the state before attack, s':the state after attack, s'':the previous state contains the replayed message
pred attacker_action_replay[s, s': State] {
  (some s'':State | 
    no s.network and 
    s'.network in s''.network and
    s'' in ord/prevs[s] ) and
    s'.last_action = ReplayMessage and
    s.log = s'.log
}

assert attack_replay {
	all s,s':State | attacker_action_replay[s,s'] implies ( 
    some s'': State | s'.network in s''.network and
    s'' in ord/prevs[s] and
    no s.network
   )
}

check attack_replay for 10 expect 0

// =========================== State Transitions and Traces ==================

// State transitions occur via the various actions of the system above
// including those of the attacker.
pred state_transition[s, s' : State] {
  send_log_message[s,s']
  or recv_log_message[s,s']
  or attacker_action_drop[s,s']
  or attacker_action_fabricate[s,s']
  or attacker_action_replay[s,s']
}

// Define the linear ordering on states to be that generated by the
// state transitions above, defining execution traces to be sequences
// of states in which each state follows in the sequence from the last
// by a state transition.
fact state_transition_ord {
  all s: State, s': ord/next[s] {
    state_transition[s,s'] and s' != s
  }
}

// The initial state is first in the order, i.e. all execution traces
// that we model begin in the initial state described by the Init predicate
fact init_state {
  all s: ord/first {
    Init[s]
  }
}

// =========================== Properties ====================================

// An example assertion and check:
// Specifies that the log only grows, i.e. new things can get
// added to it but nothing is ever removed
assert log_only_grows {
  all s : State | all s' : ord/nexts[s] |
     some (s.log.elems) implies 
     (all idx : Int | idx < #(s.log) implies  s.log[idx] = s'.log[idx])
}

check log_only_grows for 10 expect 0

// used to check the correctness of the log
// correct log means that the messages in log of any states should only been sent by the Sender instead of Attacker
// To be specific, for each message which is in the log of state s, it should be sent by at least once in previous states by the Sender
pred log_correct[s : State] {
  all msg : LogMessage |
	msg in s.log.elems implies 
  // For all the states, the message should come from previous states' network
	( all s': State | ( msg in s'.network and s' in ord/prevs[s] )  implies 
    // The msg in log should not come from attackers
		( s'.last_action not in ReplayMessage and s'.last_action not in FabricateMessage )  
	)
}

// used to specify the log_correct_* predicates below
pred attacker_only[actions : AttackerAction] {
  all s : State | s.last_action in AttackerAction implies s.last_action in actions
}

assert log_correct_when_attacker_only_drops {
  all s : State | attacker_only[DropMessage] implies log_correct[s]
}
// <Adjust these thresholds as necessary to find the smallest
//  attack you can, when such an attack exists, in each attacker model>
check log_correct_when_attacker_only_drops for 10 expect 0

assert log_correct_when_attacker_only_replays {
  all s : State | attacker_only[ReplayMessage] implies log_correct[s]
}
// <Adjust these thresholds as necessary to find the smallest
//  attack you can, when such an attack exists, in each attacker model>
check log_correct_when_attacker_only_replays for 5 expect 1
// The smallest attack in this model requires at least 5 states to exist.
// The Attacker do replay message attack, using an existing message in the log
// and inserting it into the network again. This means that there should at least 
// have one message in the log which requires a Normal Sender does a send action
// and the server receives that message. Then the Attacker could use that message and
// insert that into the network again after which the server would receive the same message.
// So the trace would be like: s0(initial)-(send)->s1-(receive)
//                              ->s2-(replay)->s3-(receive)->s4(where the attack is detected)
// Since the last action of the state s which contains this message is replayMessage
// so it is captured 

assert log_correct_when_attacker_only_fabricates {
  all s : State | attacker_only[FabricateMessage] implies log_correct[s]
}
// <Adjust these thresholds as necessary to find the smallest
//  attack you can, when such an attack exists, in each attacker model>
check log_correct_when_attacker_only_fabricates for 3 expect 1
// The smallest attack in this model requires at least 3 states to exist.
// The attacker could fabricate a fake message which the sender doesn't intend to send
// and inject it into the network
// Thus this requires 3 states to detect the attack
// The trace would be like: s0(inital)-(fabricate)->s1-(receive)->s2(where the attack is detected)
// Since the last action of the state s which contains this message is fabricateMessage
// so it is captured 

// <Describe any additional attacks that are possible but are not
//  captured by your model here>

//=======================================Other Potential Attacks====================================
// This models the action in which the attacker modifies the message from a sender
// Precondition: exsists some message on the net 
// Postcondition: the message from sender is replaced by another fake messages
one sig ModifyMessage extends AttackerAction {}

pred attack_action_modify[s,s': State]{
   some msg,msg' : LogMessage |
	msg in s.network and msg' in s'.network and
	not msg' = msg and
	s'.last_action = ModifyMessage
}

assert attack_modify {
	all s,s' : State | attack_action_modify[s,s'] implies not s.network = s'.network
}

check attack_modify for 3 expect 0

assert log_correct_when_attacker_only_modify {
  all s : State | attacker_only[ModifyMessage] implies log_correct[s]
}
check log_correct_when_attacker_only_modify for 10 expect 1

// This models the action in which the attacker replaces the new message with an old one which has already been in the log
// Precondition: exsists some message on the net
// Postcondition: the message is replaced with an message which is in the log
one sig ReplayModifyMessage extends AttackerAction {}

pred attack_action_replayModify[s,s': State]{
    some msg,msg' : LogMessage |
	msg in s.network and msg' in s.log.elems and
	not msg = msg' and
	msg in s'.network and
	s'.last_action = ReplayModifyMessage
}

assert attack_replaymodify {
	all s,s' : State | attack_action_replayModify[s,s'] implies
	( not s.network = s'.network and
	 s'.network in s.log.elems)
}

check attack_replaymodify for 3 expect 0

assert log_correct_when_attacker_only_replaymodify {
  all s : State | attacker_only[ReplayModifyMessage] implies log_correct[s]
}
check log_correct_when_attacker_only_replaymodify for 10 expect 1

// For these two attacks, they are like combination of those former three attacks
// The model we generate here can only correctly capture the attacks when there
// is only single type of attack. However, when there are combine attacks, it's
// hard for it to detect or tell whether the action is done by normal user instead of attacker.
// What's more. this model didn't simulate the condition of message of sender missing in some way.
