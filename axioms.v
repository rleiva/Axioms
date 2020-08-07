(*
 Axioms v4
*)

Require Import Arith.

(* Helper lemmas *)

Lemma less_or_equal (n m : nat):
  n <= m <-> (n < m \/ n = m).
Proof.
  split.
  intros.
  induction H.
  right.
  reflexivity.
  left.
  assert (m < S m).
  auto.
  firstorder.
  intros.
  destruct H as [H1 | H2].
  induction H1.
  auto.
  auto.
  induction H2.
  auto.
Qed.

(* Oracle function: Description -> nat *)
Parameter O : nat -> nat.

(* Oracle equivalence relation: Description x Description -> bool *)
Parameter R : nat -> nat -> Prop.
Axiom reflexive:  forall r     : nat, R r r.
Axiom symmetric:  forall r s   : nat, R r s -> R s r.
Axiom transitive: forall r s t : nat, R r s -> R s t -> R r t.

(* Nescience function: Description -> Nescience *)
Parameter N : nat -> nat.

(* Axioms *)

(* Axiom: non-negativity of nescience *)
Axiom non_negativity: forall d : nat, N(d) >= 0.

(* Axiom of surfeit *)
Axiom surfeit: forall s t : nat, R s t /\ O s <= O t /\ Nat.log2 s < Nat.log2 t -> N s < N t.

(* Axiom of inaccuracy *)
Axiom inaccuracy: forall s t : nat, R s t /\ O s < O t /\ Nat.log2 s <= Nat.log2 t -> N s < N t.

(* Axiom of equality *)
Axiom equality: forall s t : nat, R s t /\ O s = O t /\ Nat.log2 s = Nat.log2 t -> N s = N t.

(* Axiom perfect_knowledge *)
Axiom perfect_knowledge: forall s : nat, N s = 0 <-> ( O s = 0 )
  /\ ( ~ exists t : nat, s <> t /\ R s t /\ O t = 0 /\ Nat.log2 t < Nat.log2 s ).

(* zero uknown *)
Axiom zero_unknown: forall s : nat, exists t : nat, R s t /\ N t = 0.

Lemma zero_inaccuracy (d : nat) :
  N d = 0 -> O d = 0.
Proof.
  intros.
  apply perfect_knowledge.
  assumption.
  Qed.

(* l(s) < l(t) & O(s) < O(t) => N(s) < N(t) *)
Lemma property_ll:
  forall s t : nat, R s t -> Nat.log2 s < Nat.log2 t -> O s < O t -> N s < N t.
Proof.
  intros s t H1 H2 H3.
  apply surfeit.
  split.
  assumption.
  split.
  apply less_or_equal.
  left.
  apply H3.
  apply H2.
Qed.

(* l(s) < l(t) & O(s) = O(t) => N(s) < N(t) *)
Lemma property_le:
  forall s t : nat, R s t -> Nat.log2 s < Nat.log2 t -> O s = O t -> N s < N t.
Proof.
  intros s t H1 H2 H3.
  apply surfeit.
  split.
  assumption.
  split.
  apply less_or_equal.
  right.
  apply H3.
  apply H2.
Qed.

(* l(s) = l(t) & O(s) < O(t) => N(s) < N(t) *)
Lemma property_el:
  forall s t : nat, R s t -> Nat.log2 s = Nat.log2 t -> O s < O t -> N s < N t.
Proof.
  intros s t H1 H2 H3.
  apply inaccuracy.
  split.
  assumption.
  split.
  assumption.
  apply less_or_equal.
  right.
  apply H2.
Qed.

(* l(s) = l(t) & O(s) = O(t) => N(s) = N(t) *)
(* axiom equality *)

(* l(s) = l(t) & O(s) > O(t) => N(s) > N(t) *)
Lemma property_eg:
  forall s t : nat, R s t -> Nat.log2 s = Nat.log2 t -> O s > O t -> N s > N t.
Proof.
  intros s t H1 H2 H3.
  apply property_el.
  apply symmetric.
  assumption.
  auto.
  auto.
Qed.

(* l(s) > l(t) & O(s) = O(t) => N(s) > N(t) *)
Lemma property_ge:
  forall s t : nat, R s t -> Nat.log2 s > Nat.log2 t -> O s = O t -> N s > N t.
Proof.
  intros s t H1 H2 H3.
  apply property_le.
  apply symmetric.
  assumption.
  auto.
  auto.
  Qed.

(* l(s) > l(t) & O(s) > O(t) => N(s) > N(t) *)
Lemma property_gg:
  forall s t : nat, R s t -> Nat.log2 s > Nat.log2 t -> O s > O t -> N s > N t.
Proof.
  intros s t H1 H2 H3.
  apply property_ll.
  apply symmetric.
  assumption.
  auto.
  auto.
  Qed.

(* l(s) < l(t) & O(s) > O(t) => unknown *)
(* l(s) > l(t) & O(s) < O(t) => unknown *)
