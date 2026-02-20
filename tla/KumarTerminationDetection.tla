-------------------- MODULE KumarTerminationDetection ------------------------
(****************************************************************************)
(* Termination detection algorithm due to D. Kumar as described in          *)
(* Kumar, Devendra. A class of termination detection algorithms for         *)
(* distributed computations. International Conference Foundations of        *)
(* Software Technology and Theoretical Computer Science. New Delhi, India,  *)
(* Springer LNCS 206, pp.73-100, 1985.                                      *)
(*                                                                          *)
(* The algorithm also appears as the "channel counting algorithm" in        *)
(* Mattern, Friedemann. Algorithms for distributed termination detection.   *)
(* Distributed Computing 2.3 (1987):161-175.                                *)
(*                                                                          *)
(* A daemon visits nodes in arbitrary order, waits for the node to become   *)
(* inactive, and then records how many messages the node has sent to and    *)
(* received from every other node. When the daemon sees that all numbers    *)
(* match, it declares that the system has terminated.                       *)
(****************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT  \* nodes of the system
    \* @type: Set(NODE);
    Node

\* We assume that the set of nodes is finite and non-empty.
ASSUME NodeFinite == IsFiniteSet(Node) /\ Node # {}

VARIABLES 
    \* active[p] is the activation status of p
    \* @type: NODE -> Bool;
    active,
    \* sent[p][q] is the number of messages sent from p to q
    \* @type: NODE -> (NODE -> Int);
    sent,
    \* rcvd[p][q] is the number of messages received by p from q
    \* @type: NODE -> (NODE -> Int);
    rcvd,
    \* visited is the set of nodes already visited by the daemon
    \* @type: Set(NODE);
    visited,
    \* ds[p][q] is the number of messages sent from p to q recorded by the daemon
    \* @type: NODE -> (NODE -> Int);
    ds,
    \* dr[p][q] is the number of messages received by p from q recorded by the daemon
    \* @type: NODE -> (NODE -> Int);
    dr

vars == <<active, sent, rcvd, visited, ds, dr>>

(****************************************************************************)
(* The system has globally terminated when all nodes are inactive and when  *)
(* all sent messages have been received.                                    *)
(****************************************************************************)
terminated == 
    /\ \A n \in Node : active[n] = FALSE 
    /\ \A p,q \in Node : sent[p][q] = rcvd[q][p]

TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ sent \in [Node -> [Node -> Nat]]
    /\ rcvd \in [Node -> [Node -> Nat]]
    /\ visited \in SUBSET Node 
    /\ ds \in [Node -> [Node -> Nat]]
    /\ dr \in [Node -> [Node -> Nat]]

(****************************************************************************)
(* The counters recorded by the daemon are consistent for a set Q of nodes  *)
(* if the numbers of sent and received messages agree. When the numbers are *)
(* consistent for all nodes and the daemon has visited all nodes then it    *)
(* declares global termination.                                             *)
(****************************************************************************)
Consistent(Q) ==
    \A p,q \in Q : ds[p][q] = dr[q][p]

terminationDetected == Consistent(Node) /\ visited = Node 

(****************************************************************************)
(* Initially some nodes are active, the daemon has not visited any node,    *)
(* and all counters are initialized to zero.                                *)
(****************************************************************************)
Init == 
    LET zero == [p \in Node |-> [q \in Node |-> 0]]
    IN  /\ active \in [Node -> BOOLEAN]
        /\ visited = {}
        /\ sent = zero 
        /\ rcvd = zero 
        /\ ds = zero 
        /\ dr = zero 

(****************************************************************************)
(* Local termination of a node.                                             *)
(****************************************************************************)
Terminate(n) ==
    /\ active[n] = TRUE
    /\ active' = [active EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<sent, rcvd, visited, ds, dr>>

(****************************************************************************)
(* Node p sends a message to node q.                                        *)
(****************************************************************************)
Send(p,q) ==
    /\ active[p] = TRUE
    /\ sent' = [sent EXCEPT ![p][q] = @+1]
    /\ UNCHANGED <<active, rcvd, visited, ds, dr>>

(****************************************************************************)
(* Node q receives a message from node p.                                   *)
(****************************************************************************)
Recv(p,q) ==
    /\ sent[p][q] > rcvd[q][p]
    /\ active' = [active EXCEPT ![q] = TRUE]
    /\ rcvd' = [rcvd EXCEPT ![q][p] = @+1]
    /\ UNCHANGED <<sent, visited, ds, dr>>

(****************************************************************************)
(* When termination has not yet been detected, the daemon visits a node n   *)
(* and records its counters provided that n is inactive.                    *)
(****************************************************************************)
Record(n) == 
\*    /\ ~ terminationDetected
    /\ active[n] = FALSE 
    /\ visited' = visited \union {n}
    /\ ds' = [ds EXCEPT ![n] = sent[n]]
    /\ dr' = [dr EXCEPT ![n] = rcvd[n]]
    /\ UNCHANGED <<active, sent, rcvd>> 

(****************************************************************************)
(* The overall specification.                                               *)
(****************************************************************************)
Next == 
    \/ \E n \in Node : Terminate(n) \/ Record(n)
    \/ \E p,q \in Node : Send(p,q) \/ Recv(p,q)

Spec == Init /\ [][Next]_vars /\ \A n \in Node : WF_vars(Record(n))

------------------------------------------------------------------------------
(****************************************************************************)
(* Invariant about counter values:                                          *)
(* - rcvd counters are bounded by the corresponding sent counters,          *)
(* - daemon counters are bounded by the counters of the processes.          *)
(****************************************************************************)
CounterInv == \A p,q \in Node :
    /\ rcvd[q][p] <= sent[p][q]
    /\ ds[p][q] <= sent[p][q]
    /\ dr[p][q] <= rcvd[p][q]

(****************************************************************************)
(* A set Q of nodes is stale if it either contains an active node or some   *)
(* node that has sent or received more messages than the daemon has seen.   *)
(* The following invariant asserts that if a set Q of visited nodes is      *)
(* consistent and stale then some node in Q must have received a message    *)
(* from some node outside Q that was not recorded by the daemon.            *)
(****************************************************************************)
Stale(Q) == \E q \in Q :
    \/ active[q] = TRUE
    \/ \E n \in Node : ds[q][n] # sent[q][n]
    \/ \E n \in Node : dr[q][n] # rcvd[q][n]

StaleInv == \A Q \in SUBSET visited : 
    Consistent(Q) /\ Stale(Q)
    => \E q \in Q : \E n \in Node \ Q : dr[q][n] # rcvd[q][n]

(****************************************************************************)
(* The main correctness property of the algorithm.                          *)
(****************************************************************************)
Safe == terminationDetected => terminated

\* non-invariants
NeverTD == ~ terminationDetected
NeverSent == terminationDetected => \A p,q \in Node : ds[p][q] = 0

(****************************************************************************)
(* Liveness property: termination will eventually be detected.              *)
(****************************************************************************)
Live == terminated ~> terminationDetected

------------------------------------------------------------------------------

\* state constraint for TLC: bound number of sent messages
StateConstraint == \A p,q \in Node : sent[p][q] <= 2

\* Check inductiveness of StaleInv w.r.t. TypeOK and CounterInv using Apalache.
\* Unfortunately, this currently fails due to a missing rewrite in Apalache's
\* pre-processing pipeline.
CInit == Node = {"n1_OF_NODE", "n2_OF_NODE", "n3_OF_NODE"}
IndInv == TypeOK /\ CounterInv /\ StaleInv

==============================================================================
