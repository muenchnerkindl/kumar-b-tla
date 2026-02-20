---------------------- MODULE AsyncTerminationDetection ---------------------
(***************************************************************************)
(* An abstract specification of the termination detection problem in a     *)
(* system with asynchronous communication.                                 *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT 
  \* @type: Set(NODE);
  Node

VARIABLES 
  \* @type: NODE -> Bool;
  active,               \* activation status of each node
  \* @type: NODE -> Int;
  pending,              \* number of messages pending at a node
  \* @type: Bool;
  terminationDetected   \* has termination been detected?

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ pending \in [Node -> Nat]
  /\ terminationDetected \in BOOLEAN

terminated == \A n \in Node : ~ active[n] /\ pending[n] = 0

(***************************************************************************)
(* Initial condition: the nodes can be active or inactive, no pending      *)
(* messages. Termination may (but need not) be detected immediately if all *)
(* nodes are inactive.                                                     *)
(***************************************************************************)
Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ pending = [n \in Node |-> 0]
  /\ terminationDetected \in {FALSE, terminated}

Terminate(p) ==  \* node i terminates locally
  /\ active[p]
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ pending' = pending
     (* possibly detect termination if all nodes are inactive *)
  /\ terminationDetected' \in {terminationDetected, terminated'}

SendMsg(p,q) ==  \* active node p sends a message to node q
  /\ active[p]
  /\ pending' = [pending EXCEPT ![q] = @ + 1]
  /\ UNCHANGED <<active, terminationDetected>>

RcvMsg(q) == \* node q receives a pending message
  /\ pending[q] > 0
  /\ active' = [active EXCEPT ![q] = TRUE]
  /\ pending' = [pending EXCEPT ![q] = @ - 1]
  /\ UNCHANGED terminationDetected

DetectTermination ==
  /\ terminated
  /\ terminationDetected' = TRUE
  /\ UNCHANGED <<active, pending>>

Next ==
  \/ \E p \in Node : Terminate(p) \/ RcvMsg(p)
  \/ \E p,q \in Node : SendMsg(p,q)
  \/ DetectTermination

vars == <<active, pending, terminationDetected>>
Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(DetectTermination)
           \* reasonable but not necessary for detecting termination
           \* /\ \A q \in Node : WF_vars(RcvMsg(q))


(***************************************************************************)
(* Restrict TLC model checking to a finite fragment of the state space.    *)
(***************************************************************************)
StateConstraint == \A n \in Node : pending[n] <= 3

(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)
Safe == terminationDetected => terminated

Quiescence == [](terminated => []terminated)

Live == terminated ~> terminationDetected

(***************************************************************************)
(* Auxiliary definitions for checking with Apalache.                       *)
(***************************************************************************)
\* initialize the constant for checking with Apalache
CInit == Node = {"n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE"}
\* formula to use as initial condition and as invariant for using Apalache
\* to check inductiveness of the invariant
IndInv == TypeOK /\ Safe
=============================================================================
