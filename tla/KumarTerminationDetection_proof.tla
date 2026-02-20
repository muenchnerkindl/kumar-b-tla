------------------- MODULE KumarTerminationDetection_proof -------------------
EXTENDS KumarTerminationDetection, FiniteSetTheorems, Functions, FunctionTheorems, TLAPS

(****************************************************************************)
(* Proof of type correctness.                                               *)
(****************************************************************************)
THEOREM Typing == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  BY DEF TypeOK, Next, vars, Terminate, Send, Recv, Record
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

------------------------------------------------------------------------------

(****************************************************************************)
(* Proof of the counter invariant.                                          *)
(****************************************************************************)
THEOREM CounterInvariant == Spec => []CounterInv
<1>1. Init => CounterInv 
  BY DEF Init, CounterInv
<1>2. TypeOK /\ CounterInv /\ [Next]_vars => CounterInv'
  BY DEF TypeOK, CounterInv, Next, vars, Terminate, Send, Recv, Record
<1>. QED  BY <1>1, <1>2, Typing, PTL DEF Spec

------------------------------------------------------------------------------
(****************************************************************************)
(* Proof of the invariant about consistent and stale sets of visited nodes. *)
(****************************************************************************)
THEOREM StaleInvariant == Spec => []StaleInv 
<1>1. Init => StaleInv 
  BY DEF Init, StaleInv, Consistent, Stale 
<1>2. TypeOK /\ CounterInv /\ StaleInv /\ [Next]_vars => StaleInv'
  <2>. SUFFICES ASSUME TypeOK, CounterInv, StaleInv, Next
                PROVE  StaleInv'
    BY DEF StaleInv, Consistent, Stale, vars
  <2>. USE DEF TypeOK
  <2>1. ASSUME NEW n \in Node, Terminate(n) PROVE StaleInv'
    BY <2>1 DEF Terminate, StaleInv, Consistent, Stale
  <2>2. ASSUME NEW n \in Node, Record(n) PROVE StaleInv'
    <3>1. /\ active[n] = FALSE 
          /\ visited' = visited \union {n}
          /\ ds' = [ds EXCEPT ![n] = sent[n]]
          /\ dr' = [dr EXCEPT ![n] = rcvd[n]]
          /\ UNCHANGED <<active, sent, rcvd>> 
      BY <2>2 DEF Record
    <3>. SUFFICES ASSUME NEW Q \in SUBSET visited', Consistent(Q)', 
                         Stale(Q)'
                  PROVE  \E q \in Q : \E p \in Node \ Q : dr'[q][p] # rcvd'[q][p]
      BY DEF StaleInv 
    <3>. Q \in SUBSET Node
      BY <3>1
    <3>2. CASE n \in Q
      <4>. DEFINE QQ == Q \ {n}
      <4>1. /\ QQ \in SUBSET visited
            /\ Consistent(QQ)
            /\ Consistent(QQ)'
        BY <3>1, Zenon DEF Consistent
      <4>2. Stale(QQ)
        BY <3>1 DEF Stale
      <4>3. PICK q \in QQ, p \in Node \ QQ : dr[q][p] # rcvd[q][p]
        BY <4>1, <4>2 DEF StaleInv
      <4>. SUFFICES ASSUME p = n PROVE FALSE 
        BY <3>1, <4>3
      <4>4. rcvd[q][n] > dr[q][n]
        BY <4>3 DEF CounterInv 
      <4>5. @ = dr'[q][n]
        BY <3>1
      <4>6. @ = ds'[n][q]
        BY <3>2 DEF Consistent
      <4>7. @ = sent[n][q]
        BY <3>1
      <4>. QED  BY <4>4, <4>5, <4>6, <4>7, q \in Node DEF CounterInv
    <3>3. CASE n \notin Q
      <4>1. /\ Q \subseteq visited
            /\ Consistent(Q)
        BY <3>1, <3>3, Zenon DEF Consistent
      <4>2. Stale(Q)
        BY <3>1, <3>3 DEF Stale
      <4>3. PICK q \in Q, p \in Node \ Q : dr[q][p] # rcvd[q][p]
        BY <4>1, <4>2 DEF StaleInv 
      <4>. QED  BY <3>1, <3>3, <4>3
    <3>. QED  BY <3>2, <3>3
  <2>3. ASSUME NEW p \in Node, NEW q \in Node, Send(p, q) PROVE StaleInv'
    BY <2>3 DEF Send, StaleInv, Consistent, Stale, CounterInv 
(* -- detailed proof
    <3>1. /\ active[p] = TRUE
          /\ sent' = [sent EXCEPT ![p][q] = @+1]
          /\ UNCHANGED <<active, rcvd, visited, ds, dr>>
      BY <2>3 DEF Send
    <3>. SUFFICES ASSUME NEW Q \in SUBSET visited', 
                         Consistent(Q)', Stale(Q)'
                  PROVE  \E qq \in Q : \E n \in Node \ Q : dr'[qq][n] # rcvd'[qq][n]
      BY DEF StaleInv 
    <3>2. /\ Q \in SUBSET visited
          /\ Consistent(Q)
      BY <3>1 DEF Consistent
    <3>3. Stale(Q)
      BY <3>1 DEF Stale
    <3>4. PICK qq \in Q, n \in Node \ Q : dr[qq][n] # rcvd[qq][n]
      BY <3>2, <3>3 DEF StaleInv 
    <3>. QED  BY <3>1, <3>4 DEF Stale, CounterInv
*)
  <2>4. ASSUME NEW p \in Node, NEW q \in Node, Recv(p, q) PROVE StaleInv'
    BY <2>4 DEF Recv, StaleInv, Consistent, Stale, CounterInv 
  <2>. QED BY <2>1, <2>2, <2>3, <2>4 DEF Next
<1>. QED  BY <1>1, <1>2, Typing, CounterInvariant, PTL DEF Spec

------------------------------------------------------------------------------
(****************************************************************************)
(* The main safety property follows as a simple corollary.                  *)
(****************************************************************************)
THEOREM Safety == Spec => []Safe
<1>1. TypeOK /\ StaleInv /\ terminationDetected => terminated
  <2>. SUFFICES ASSUME TypeOK, StaleInv, terminationDetected, ~terminated 
                PROVE  FALSE
    OBVIOUS
  <2>. USE DEF TypeOK
  <2>1. Consistent(Node) /\ visited = Node
    BY DEF terminationDetected
  <2>2. Stale(Node)
    BY <2>1 DEF Consistent, Stale, terminated
  <2>. QED  BY <2>1, <2>2 DEF StaleInv 
<1>. QED  BY <1>1, Typing, StaleInvariant, PTL DEF Safe

(****************************************************************************)
(* Moreover, termination detection is stable.                               *)
(****************************************************************************)
LEMMA TDStaysTrue ==
    ASSUME TypeOK, StaleInv, Safe, [Next]_vars, 
           terminationDetected
    PROVE  terminationDetected'
<1>. USE DEF TypeOK
<1>1. terminated
  BY DEF Safe
<1>2. ASSUME NEW n \in Node, Terminate(n) PROVE terminationDetected'
  BY <1>1, <1>2 DEF terminated, Terminate 
<1>3. ASSUME NEW n \in Node, Record(n) PROVE terminationDetected' 
  <2>1. /\ Consistent(Node)
        /\ visited = Node
    BY <1>1 DEF terminationDetected
  <2>2. ASSUME Stale(Node) PROVE FALSE 
    BY <2>1, <2>2 DEF StaleInv
  <2>3. /\ ds[n] = sent[n]
        /\ dr[n] = rcvd[n]
    BY <2>2 DEF Stale
  <2>4. UNCHANGED vars
    BY <1>3, <2>1, <2>3, Zenon DEF Record, vars
  <2>. QED  BY <2>4 DEF terminationDetected, Consistent, vars
<1>4. ASSUME NEW p \in Node, NEW q \in Node, Send(p,q) PROVE terminationDetected' 
  BY <1>1, <1>4 DEF terminated, Send
<1>5. ASSUME NEW p \in Node, NEW q \in Node, Recv(p,q) PROVE terminationDetected' 
  BY <1>5 DEF Recv, terminationDetected, Consistent
<1>6. CASE UNCHANGED vars
  BY <1>6 DEF vars, terminationDetected, Consistent
<1>. QED  BY <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

THEOREM TDStable == Spec => [][~terminationDetected]_terminationDetected
<1>1. /\ TypeOK /\ StaleInv /\ Safe
      /\ ~(UNCHANGED terminationDetected) /\ [Next]_vars
      => ~terminationDetected 
  BY TDStaysTrue
<1>. QED  BY <1>1, Typing, StaleInvariant, Safety, PTL DEF Spec

------------------------------------------------------------------------------
(****************************************************************************)
(* Proof of liveness.                                                       *)
(*                                                                          *)
(* As a preparation, we establish when Record(n) is enabled.                *)
(****************************************************************************)
LEMMA RecordEnabled == 
    ASSUME TypeOK, NEW n \in Node
    PROVE  (ENABLED <<Record(n)>>_vars)
           <=>  /\ active[n] = FALSE 
                /\ \/ n \notin visited
                   \/ ds[n] # sent[n]
                   \/ dr[n] # rcvd[n]
<1>. USE DEF TypeOK
<1>1. (ENABLED <<Record(n)>>_vars)
      => /\ active[n] = FALSE 
         /\ \/ n \notin visited
            \/ ds[n] # sent[n]
            \/ dr[n] # rcvd[n]
  BY ExpandENABLED, ZenonT(20) DEF Record, vars
<1>2. ASSUME /\ active[n] = FALSE 
             /\ \/ n \notin visited
                \/ ds[n] # sent[n]
                \/ dr[n] # rcvd[n]
      PROVE  ENABLED <<Record(n)>>_vars
  <2>. DEFINE activep == active
              visitedp == visited \union {n}
              dsp == [ds EXCEPT ![n] = sent[n]]
              drp == [dr EXCEPT ![n] = rcvd[n]]
              sentp == sent 
              rcvdp == rcvd 
  <2>1. /\ active[n] = FALSE 
        /\ visitedp = visited \union {n}
        /\ dsp = [ds EXCEPT ![n] = sent[n]]
        /\ drp = [dr EXCEPT ![n] = rcvd[n]]
        /\ activep = active
        /\ sentp = sent
        /\ rcvdp = rcvd
        /\ <<activep, sentp, rcvdp, visitedp, dsp, drp>>
           # <<active, sent, rcvd, visited, ds, dr>>
    BY <1>2
  <2>2. \E activepp, visitedpp, dspp, drpp, activepp, sentpp, rcvdpp :
           /\ active[n] = FALSE 
           /\ visitedpp = visited \union {n}
           /\ dspp = [ds EXCEPT ![n] = sent[n]]
           /\ drpp = [dr EXCEPT ![n] = rcvd[n]]
           /\ activepp = active
           /\ sentpp = sent
           /\ rcvdpp = rcvd
           /\ <<activepp, sentpp, rcvdpp, visitedpp, dspp, drpp>>
              # <<active, sent, rcvd, visited, ds, dr>>
    BY <2>1
  <2>. QED  BY <2>2, ExpandENABLED, Isa DEF Record, vars
<1>. QED  BY <1>1, <1>2

(****************************************************************************)
(* Define the set of nodes that have been visited and for which the         *)
(* correct numbers of sent and received messages have been recorded.        *)
(****************************************************************************)
GoodNodes == {n \in Node : /\ n \in visited 
                           /\ ds[n] = sent[n]
                           /\ dr[n] = rcvd[n]}

\* specification used for the liveness proof
LSpec ==
    /\ []TypeOK
    /\ [][Next]_vars
    /\ \A n \in Node : WF_vars(Record(n))

(****************************************************************************)
(* If termination has occurred then eventually all nodes are good.          *)
(****************************************************************************)
THEOREM AllGood == LSpec => [](terminated => <>(terminated /\ GoodNodes = Node))
<1>. DEFINE P(S) == LSpec => [](terminated => <>(terminated /\ S \subseteq GoodNodes))
<1>2. P({})
  <2>. {} \subseteq GoodNodes 
    OBVIOUS
  <2>. QED  BY PTL
<1>3. ASSUME NEW T \in SUBSET Node, NEW n \in Node \ T 
      PROVE  P(T) => P(T \union {n})
  <2>. DEFINE A == terminated /\ T \subseteq GoodNodes
              B == terminated /\ T \subseteq GoodNodes /\ ~(T \union {n} \subseteq GoodNodes)
              C == terminated /\ T \union {n} \subseteq GoodNodes
              RecN == Record(n)
  <2>0. A => B \/ C
    OBVIOUS
  <2>1. B /\ TypeOK /\ [Next]_vars => B' \/ C'
    <3>. USE DEF TypeOK
    <3>1. ASSUME NEW self \in Node, Terminate(self), TypeOK, B 
          PROVE  B'
      BY <3>1 DEF Terminate, terminated, GoodNodes
    <3>2. ASSUME NEW self \in Node, Record(self), TypeOK, B 
          PROVE  B' \/ C'
      BY <3>2 DEF Record, terminated, GoodNodes
    <3>3. ASSUME NEW p \in Node, NEW q \in Node, Send(p,q), TypeOK, B 
          PROVE  B'
      BY <3>3 DEF Send, terminated, GoodNodes
    <3>4. ASSUME NEW p \in Node, NEW q \in Node, Recv(p,q), TypeOK, B 
          PROVE  B'
      <4>. ~(sent[p][q] > rcvd[q][p])
        BY <3>4 DEF terminated
      <4>. QED BY <3>4, Zenon DEF Recv
    <3>5. ASSUME UNCHANGED vars, B 
          PROVE  B'
      BY <3>5 DEF vars, terminated, GoodNodes
    <3>. QED  BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF Next
  <2>2. B /\ TypeOK /\ <<RecN>>_vars => C'
    BY DEF TypeOK, Record, GoodNodes, terminated
  <2>3. B /\ TypeOK => ENABLED <<RecN>>_vars
    BY RecordEnabled DEF TypeOK, GoodNodes, terminated
  <2>4. LSpec => WF_vars(RecN)
    BY Isa DEF LSpec
  <2>. QED
    BY <2>0, <2>1, <2>2, <2>3, <2>4, PTL DEF LSpec
<1>. HIDE DEF P
<1>4. P(Node)
  BY NodeFinite, <1>2, <1>3, FS_Induction, IsaM("blast")
<1>. QED
  <2>1. /\ Node \in SUBSET Node 
        /\ (Node \subseteq GoodNodes) <=> (GoodNodes = Node)
    BY DEF GoodNodes
  <2>. QED  BY <1>4, <2>1, PTL DEF P

(****************************************************************************)
(* The liveness property follows immediately.                               *)
(****************************************************************************)
THEOREM Liveness == Spec => Live
<1>1. TypeOK /\ terminated /\ GoodNodes = Node => terminationDetected 
  BY Zenon DEF TypeOK, terminated, GoodNodes, terminationDetected, Consistent
<1>. QED  BY <1>1, Typing, AllGood, PTL DEF Spec, LSpec, Live

------------------------------------------------------------------------------
(****************************************************************************)
(* Finally, we prove that the algorithm refines the abstract specification. *)
(****************************************************************************)

\* the number of messages sent to a node but not yet received
Diff(p,q) == sent[p][q] - rcvd[q][p]
pnd(n) == SumFunction([p \in Node |-> Diff(p,n)])
pending == [n \in Node |-> pnd(n)]

ATD == INSTANCE AsyncTerminationDetection

(****************************************************************************)
(* Prove that the termination conditions are equivalent in both specs.      *)
(****************************************************************************)

LEMMA Termination == 
    ASSUME TypeOK, CounterInv 
    PROVE  terminated <=> ATD!terminated
<1>. USE DEF TypeOK 
<1>1. \A q \in Node : [p \in Node |-> Diff(p,q)] \in [Node -> Nat]
  BY DEF Diff, CounterInv 
<1>2. ASSUME terminated PROVE ATD!terminated
  BY <1>1, <1>2, SumFunctionZero, NodeFinite 
     DEF terminated, Diff, ATD!terminated, pending, pnd, Diff
<1>3. ASSUME ATD!terminated PROVE terminated
  <2>1. \A n \in Node : active[n] = FALSE
    BY <1>3 DEF ATD!terminated
  <2>2. \A q \in Node : pnd(q) = 0
    BY <1>3 DEF ATD!terminated, pending
  <2>3. \A p, q \in Node : Diff(p,q) = 0
    BY <1>1, <2>2, SumFunctionZero, NodeFinite DEF pnd 
  <2>. QED  BY <2>1, <2>3 DEF terminated, Diff
<1>. QED  BY <1>2, <1>3

(****************************************************************************)
(* Now we prove that Kumar's algorithm refines the high-level spec.         *)
(****************************************************************************)
THEOREM Refinement == Spec => ATD!Spec
<1>1. Init => ATD!Init 
  <2>. SUFFICES ASSUME Init PROVE ATD!Init 
    OBVIOUS
  <2>1. active \in [Node -> BOOLEAN]
    BY DEF Init
  <2>2. \A n \in Node : 
           /\ [p \in Node |-> sent[p][n] - rcvd[n][p]] \in [Node -> Int]
           /\ \A p \in Node : sent[p][n] - rcvd[n][p] = 0
    BY DEF Init
  <2>3. \A n \in Node : pnd(n) = 0
    BY <2>2, SumFunctionZero, NodeFinite DEF pnd, Diff
  <2>4. terminationDetected = FALSE 
    BY NodeFinite DEF Init, terminationDetected
  <2>. QED  BY <2>1, <2>3, <2>4 DEF ATD!Init, pending
<1>2. /\ TypeOK /\ CounterInv /\ StaleInv /\ Safe /\ Safe'
      /\ [Next]_vars 
      => [ATD!Next]_(ATD!vars)
  <2>. SUFFICES ASSUME TypeOK, CounterInv, StaleInv, Safe, Safe',
                       [Next]_vars
                PROVE  [ATD!Next]_(ATD!vars)
    OBVIOUS 
  <2>. USE DEF TypeOK
  <2>0. \A n \in Node : [p \in Node |-> Diff(p,n)] \in [Node -> Nat]
    BY DEF Diff, CounterInv
  <2>1. ASSUME NEW n \in Node, Terminate(n)
        PROVE  [ATD!Next]_(ATD!vars)
    <3>1. /\ active[n] = TRUE 
          /\ active' = [active EXCEPT ![n] = FALSE]
          /\ UNCHANGED <<sent, rcvd, visited, ds, dr>>
      BY <2>1 DEF Terminate 
    <3>2. pending' = pending 
      BY <3>1 DEF pending, pnd, Diff
    <3>3. terminationDetected' = terminationDetected
      BY <3>1 DEF terminationDetected, Consistent
    <3>. QED  BY <3>1, <3>2, <3>3 DEF ATD!Next, ATD!Terminate 
  <2>2. ASSUME NEW n \in Node, Record(n)
        PROVE  [ATD!Next]_(ATD!vars)
    <3>1. /\ active[n] = FALSE 
          /\ visited' = visited \union {n}
          /\ ds' = [ds EXCEPT ![n] = sent[n]]
          /\ dr' = [dr EXCEPT ![n] = rcvd[n]]
          /\ UNCHANGED <<active, sent, rcvd>> 
      BY <2>2 DEF Record 
    <3>2. pending' = pending 
      BY <3>1 DEF pending, pnd, Diff 
    <3>3. CASE terminationDetected' = terminationDetected
      BY <3>1, <3>2, <3>3 DEF ATD!vars
    <3>4. CASE terminationDetected' # terminationDetected
      <4>1. ~terminationDetected /\ terminationDetected'
        BY <3>4, TDStaysTrue DEF terminationDetected
      <4>2. terminated'
        BY <4>1 DEF Safe
      <4>3. terminated
        BY <3>1, <4>2 DEF terminated
      <4>4. ATD!terminated
        BY <4>3, Termination
      <4>5. pending' = pending 
        BY <3>1 DEF pending, pnd, Diff
      <4>. QED  BY <3>1, <4>1, <4>4, <4>5 DEF ATD!DetectTermination, ATD!Next
    <3>. QED  BY <3>3, <3>4
  <2>3. ASSUME NEW p \in Node, NEW q \in Node, Send(p,q)
        PROVE  [ATD!Next]_(ATD!vars)
    <3>1. /\ active[p] = TRUE
          /\ sent' = [sent EXCEPT ![p][q] = @+1]
          /\ UNCHANGED <<active, rcvd, visited, ds, dr>>
      BY <2>3 DEF Send
    <3>2. pending' = [pending EXCEPT ![q] = @ + 1]
      <4>. DEFINE AllDiff(qq) == [n \in Node |-> Diff(n,qq)]
      <4>1. \A qq \in Node : 
               /\ AllDiff(qq) \in [Node -> Nat]
               /\ pnd(qq) = SumFunction(AllDiff(qq))
               /\ pnd(qq)' = SumFunction(AllDiff(qq))'
        BY <2>0 DEF pnd
      <4>2. AllDiff(q)' = [AllDiff(q) EXCEPT ![p] = @ + 1]
        BY <3>1, SMTT(30) DEF Diff
      <4>3. \A qq \in Node \ {q} : AllDiff(qq)' = AllDiff(qq)
        BY <3>1, Zenon DEF Diff
      <4>. HIDE DEF AllDiff
      <4>4. SumFunction(AllDiff(q))' = SumFunction(AllDiff(q)) + 1
        BY <4>1, <4>2, AllDiff(q) \in [Node -> Int], SumFunctionExcept, NodeFinite, Isa
      <4>. QED  BY <4>1, <4>3, <4>4 DEF pending
    <3>3. terminationDetected' = terminationDetected
      BY <3>1 DEF terminationDetected, Consistent
    <3>. QED  BY <3>1, <3>2, <3>3 DEF ATD!Next, ATD!SendMsg
  <2>4. ASSUME NEW p \in Node, NEW q \in Node, Recv(p,q)
        PROVE  [ATD!Next]_(ATD!vars)
    <3>1. /\ sent[p][q] > rcvd[q][p]
          /\ active' = [active EXCEPT ![q] = TRUE]
          /\ rcvd' = [rcvd EXCEPT ![q][p] = @+1]
          /\ UNCHANGED <<sent, visited, ds, dr>>
      BY <2>4 DEF Recv
    <3>. DEFINE AllDiff(qq) == [n \in Node |-> Diff(n,qq)]
    <3>2. \A qq \in Node : 
             /\ AllDiff(qq) \in [Node -> Nat]
             /\ pnd(qq) = SumFunction(AllDiff(qq))
             /\ pnd(qq)' = SumFunction(AllDiff(qq))'
        BY <2>0 DEF pnd
    <3>3. pending[q] > 0
      <4>1. AllDiff(q)[p] # 0
        BY <3>1 DEF Diff
      <4>. HIDE DEF AllDiff
      <4>2. SumFunction(AllDiff(q)) > 0
        BY <3>2, <4>1, SumFunctionZero, SumFunctionNat, NodeFinite
      <4>. QED  BY <3>2, <4>2 DEF pending
    <3>4. pending' = [pending EXCEPT ![q] = @ - 1]
      <4>1. AllDiff(q)' = [AllDiff(q) EXCEPT ![p] = @  - 1]
        BY <3>1 DEF Diff
      <4>2. \A qq \in Node \ {q} : AllDiff(qq)' = AllDiff(qq)
        BY <3>1 DEF Diff 
      <4>. HIDE DEF AllDiff
      <4>3. AllDiff(q) \in [Node -> Int]
        BY <3>2
      <4>4. SumFunction(AllDiff(q))' = SumFunction(AllDiff(q)) - 1
        BY <3>2, <4>1, <4>3, SumFunctionExcept, SumFunctionInt, NodeFinite
      <4>. QED  BY <3>2, <4>2, <4>4 DEF pending
    <3>5. terminationDetected' = terminationDetected
      BY <3>1 DEF terminationDetected, Consistent
    <3>. QED  BY <3>1, <3>3, <3>4, <3>5 DEF ATD!Next, ATD!RcvMsg
  <2>5. CASE UNCHANGED vars 
    BY <2>5 DEF vars, ATD!vars, pending, pnd, Diff, 
                terminationDetected, Consistent
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>3. Spec => WF_(ATD!vars)(ATD!DetectTermination)
  <2>1. (ENABLED <<ATD!DetectTermination>>_(ATD!vars)) =>
        ATD!terminated /\ ~terminationDetected
    \* ExpandENABLED succeeds but requires all operators to be expanded,
    \* even the low-level constant operators underlying SumFunction ...
    BY ExpandENABLED, Zenon
       DEF ATD!DetectTermination, ATD!vars, ATD!terminated,
           terminationDetected, Consistent, pending, pnd, Diff, 
           SumFunction, SumFunctionOnSet, FoldFunctionOnSet, MapThenFoldSet
  <2>2. TypeOK /\ CounterInv => 
        (ENABLED <<ATD!DetectTermination>>_(ATD!vars)) => terminated
    BY <2>1, Termination
  <2>3. Spec => []<>~(ENABLED <<ATD!DetectTermination>>_(ATD!vars))
    BY <2>1, <2>2, Typing, CounterInvariant, Liveness, PTL DEF Live
  <2>. QED  BY <2>3, PTL
<1>. QED  
  BY <1>1, <1>2, <1>3, Typing, CounterInvariant, StaleInvariant, Safety, PTL
     DEF Spec, ATD!Spec

==============================================================================
