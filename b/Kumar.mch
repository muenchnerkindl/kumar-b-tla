/* Kumar
 * Author: 
 * Creation date: 16/02/2026
 */
MACHINE
    Kumar

SETS
    Node

VARIABLES
    active,
    sent,
    rcvd,
    ds,
    dr,
    visited
    
DEFINITIONS
    Consistent(Q) == ∀(pp,qq). (pp ∈ Q ∧ qq ∈ Q ⇒ ds(pp,qq) = dr(qq,pp));
    Stale(Q) == ∃(qq). (qq ∈ Q ∧ (qq ∈ active ∨ (∃(nn). (nn ∈ Node ∧ ds(qq,nn) ≠ sent(qq,nn))) ∨ (∃(nn). (nn ∈ Node ∧ dr(qq,nn) ≠ rcvd(qq,nn)))))

INVARIANT
    active ⊆ Node   ∧
    sent ∈ (Node * Node) → ℕ   ∧
    rcvd ∈ (Node * Node) → ℕ   ∧
    ds ∈ (Node * Node) → ℕ   ∧
    dr ∈ (Node * Node) → ℕ    ∧
    visited ⊆ Node  ∧
    ∀(pp, qq). (pp ∈ Node ∧ qq ∈ Node ⇒ sent(pp,qq) ≥ rcvd(qq,pp))  ∧
    ∀(pp, qq). (pp ∈ Node ∧ qq ∈ Node ⇒ sent(pp,qq) ≥ ds(pp,qq))  ∧
    ∀(pp, qq). (pp ∈ Node ∧ qq ∈ Node ⇒ rcvd(pp,qq) ≥ dr(pp,qq))  ∧
    ∀(QQ). (QQ ∈ ℙ(visited) ∧ Consistent(QQ) ∧ Stale(QQ) ⇒ ∃(qq,nn). (qq ∈ QQ ∧ nn ∈ Node - QQ ∧ dr(qq,nn) ≠ rcvd(qq,nn)))

INITIALISATION
    active := ∅  ||
    sent := (Node * Node) * {0}  ||
    rcvd := (Node * Node) * {0}  ||
    ds := (Node * Node) * {0}  ||
    dr := (Node * Node) * {0}  ||
    visited := ∅

OPERATIONS
    terminate =
    ANY pp WHERE
        pp ∈ active
     THEN
         active := active - {pp}
      END;

      send =
      ANY pp, qq WHERE
          pp ∈ active ∧
         qq ∈ Node
      THEN
          sent := sent ⋖ {(pp,qq) ↦ sent(pp,qq)+1}
       END;
       
       receive =
       ANY pp, qq WHERE
           pp ∈ Node  ∧
          qq ∈ Node  ∧
          sent(pp,qq) > rcvd(qq,pp)
       THEN
           rcvd := rcvd ⋖ {(qq,pp) ↦ rcvd(qq,pp)+1} ||
           active := active ∪ {qq}
        END;
        
        record =
        ANY pp WHERE
            pp ∈ Node - active
         THEN
             ds := ds ⋖ (λ(ppp,qq). (ppp = pp ∧ qq ∈ Node | sent(ppp,qq)))  ||
             dr := dr ⋖ (λ(ppp,qq). (ppp = pp ∧ qq ∈ Node | rcvd(ppp, qq)))  ||
             visited := visited ∪ {pp}
          END

END
