Require Import Nat.
Require Export ZArith.
Require Export FunInd.
Open Scope nat_scope.

(* ------------------------------------------------------------------ *)
(* ------------------------ Inductive types ------------------------- *)
(* ------------------------------------------------------------------ *)
Inductive BTree : Set :=
| Empty : BTree
| Node : nat -> BTree -> BTree -> BTree.

(* if value is in tree *)
Inductive IsNode : BTree -> nat -> Prop :=
| CheckSelf : forall (n : nat) (left right : BTree),
  (IsNode (Node n left right) n)
| CheckLeft : forall (n_node n_left : nat) (left right : BTree),
  (IsNode left n_left) -> (IsNode (Node n_node left right) n_left)
| CheckRight : forall (n_node n_right : nat) (left right : BTree),
  (IsNode right n_right) -> (IsNode (Node n_node left right) n_right).

Inductive IsBTreeLowerThan : BTree -> nat -> Prop :=
| CheckLowerEmpty : forall (value : nat), (IsBTreeLowerThan Empty value)
| CheckLower : forall (value : nat) (node : BTree),
  (forall (n : nat), (IsNode node n) -> (n < value)) -> (IsBTreeLowerThan node value).

Inductive IsBTreeGreaterThan : BTree -> nat -> Prop :=
| CheckGreaterEmpty : forall (value : nat), (IsBTreeGreaterThan Empty value)
| CheckGreater : forall (value : nat) (node : BTree),
  (forall (n : nat), (IsNode node n) -> (n > value)) -> (IsBTreeGreaterThan node value).

Inductive IsABR : BTree -> Prop :=
| CheckEmptyABR : (IsABR Empty)
| CheckLeafABR : forall (n : nat), (IsABR (Node n Empty Empty))
| CheckNodeABR : forall (n : nat) (left right : BTree),
  (IsABR left) -> (IsABR right)
  -> (IsBTreeLowerThan left n) -> (IsBTreeGreaterThan right n)
  -> (IsABR (Node n left right)).

(* Compare 2 ABR *)

Inductive CompareDiffBTree : BTree -> BTree -> Prop :=
| CheckDiffEmpty_1 : forall (tree : BTree),
  (CompareDiffBTree tree Empty)
| CheckDiffEmpty_2 : forall (tree : BTree),
   (CompareDiffBTree Empty tree)
| CheckDiff : forall (n1 n2 : nat) (left1 left2 right1 right2 : BTree),
  (n1 <> n2 \/ (CompareDiffBTree left1 left2) \/ (CompareDiffBTree right1 right2))
  -> CompareDiffBTree (Node n1 left1 right1) (Node n2 left2 right2).

Inductive CompareEqualBTree : BTree -> BTree -> Prop :=
| CheckEqualEmpty : (CompareEqualBTree Empty Empty)
| CheckReflexif : forall (tree : BTree),
  CompareEqualBTree tree tree
| CheckEqual : forall (n : nat) (left1 left2 right1 right2 : BTree),
  (CompareEqualBTree left1 left2)
  -> (CompareEqualBTree right1 right2)
  -> (CompareEqualBTree (Node n left1 right1) (Node n left2 right2)).

(*| H: (?n0 ?= ?n1) = Gt |- False => solve [inversion H; clear H]*)
(*apply nat_compare_le; intro*)
(*apply nat_compare_gt; auto*)

Ltac TacIsABR :=
repeat
(auto || omega ||
  match goal with
    | |- (IsABR Empty) => apply CheckEmptyABR
    | |- (IsABR (Node ?n Empty Empty)) => apply CheckLeafABR
    | |- (IsABR (Node ?n ?left ?right)) => apply CheckNodeABR
    | |- (IsBTreeLowerThan Empty ?value) => apply CheckLowerEmpty
    | |- (IsBTreeLowerThan (Node ?n ?left ?right) ?value) => apply CheckLower; intros
    | |- (IsBTreeGreaterThan Empty ?value) => apply CheckGreaterEmpty
    | |- (IsBTreeGreaterThan (Node ?n ?left ?right) ?value) => apply CheckGreater; intros
    | H: IsNode Empty ?n1 |- _ => inversion H; clear H
    | H: IsNode (Node ?n1 ?left ?right) ?n0 |- _ => inversion H; clear H
  end
).

Lemma proof_abr_left : forall (n : nat) (left right : BTree),
  (IsABR (Node n left right)) -> (IsBTreeLowerThan left n).
intros.
inversion H;subst.
apply CheckLowerEmpty.
assumption.
Qed.

Lemma proof_abr_right : forall (n : nat) (left right : BTree),
  (IsABR (Node n left right)) -> (IsBTreeGreaterThan right n).
intros.
inversion H;subst.
apply CheckGreaterEmpty.
assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* ----------------------- Functions to test ------------------------ *)
(* ------------------------------------------------------------------ *)
Fixpoint SizeAbin (tree : BTree) : nat :=
match tree with
| Empty => 0
| (Node n Empty Empty)  => 1
| (Node n l r) => 1 + (max (SizeAbin l) (SizeAbin r))
end.

Fixpoint CountAbin (tree : BTree) : nat :=
match tree with
| Empty => 0
| (Node n Empty Empty)  => 1
| (Node n l r) => 1 + (CountAbin l) + (CountAbin r)
end.

(* ------------------------------------------------------------------ *)
(* ----------------------- Functions to do -------------------------- *)
(* ------------------------------------------------------------------ *)
Fixpoint searchMinABR (tree : BTree) : BTree :=
match tree with
| Empty => Empty
| (Node n Empty r) => (Node n Empty r)
| (Node n l r) => (searchMinABR l)
end.

Fixpoint searchABR (tree : BTree) (value : nat) : Prop :=
match tree with
| Empty => False
| (Node n l r) =>
  match (Nat.eq_dec value n) with
  | left _ => True
  | right _ =>
    match (lt_dec value n) with
    | left _ => (searchABR l value)
    | right _ => (searchABR r value)
    end
  end
end.

Fixpoint insertABR (tree : BTree) (value : nat) : BTree :=
match tree with
| Empty => (Node value Empty Empty)
| (Node n l r) =>
  match (Nat.eq_dec value n) with
  | left _ => (Node n l r)
  | right _ =>
    match (lt_dec value n) with
    | left _ => (Node n (insertABR l value) r)
    | right _ => (Node n l (insertABR r value))
    end
  end
end.

Fixpoint removeABR (tree : BTree) (value : nat) : BTree :=
match tree with
| Empty => Empty
| (Node n l r) =>
  match (Nat.eq_dec value n) with
  | left _ =>
    match (searchMinABR r) with
    | (Node x a b) => (Node x l (removeABR r x))
    | Empty => l
    end
  | right _ =>
    match (lt_dec value n) with
    | left _ => (Node n (removeABR l value) r)
    | right _ => (Node n l (removeABR r value))
    end
  end
end.

(* ------------------------------------------------------------------ *)
(* ----------------------------- TEST ------------------------------- *)
(* ------------------------------------------------------------------ *)
Definition test_abr1 : BTree := (Node 50 (Node 48 Empty Empty) (Node 52 Empty Empty)).
Definition test_abr2 : BTree := (Node 10 (Node 8 Empty (Node 9 Empty Empty)) (Node 12 (Node 11 Empty Empty) Empty)).
Definition test_abr3 : BTree :=
(Node 50
  (Node 40 (Node 20 Empty Empty) (Node 45 Empty Empty))
  (Node 80
    (Node 60 (Node 55 Empty Empty) (Node 70 Empty Empty))
    (Node 200
      (Node 100 (Node 90 Empty (Node 95 Empty Empty)) (Node 150 Empty Empty))
      (Node 500 (Node 400 (Node 300 Empty (Node 350 Empty Empty)) (Node 450 Empty Empty)) Empty)
))).

Compute (searchABR test_abr2 9).
Compute (insertABR test_abr2 12).
Compute (insertABR test_abr2 11).
Compute (insertABR test_abr2 900).

Compute (insertABR test_abr1 47).
Compute (insertABR test_abr1 49).
Compute (insertABR test_abr1 51).
Compute (insertABR test_abr1 53).
Compute (insertABR test_abr1 50).
Compute (insertABR test_abr1 48).
Compute (insertABR test_abr1 52).

Compute (removeABR test_abr3 50).
Compute (removeABR test_abr3 40).
Compute (removeABR test_abr3 20).
Compute (removeABR test_abr3 80).
Compute (removeABR test_abr3 200).

Goal (IsABR (Node 10 (Node 8 Empty (Node 9 Empty Empty)) (Node 12 (Node 11 Empty Empty) Empty))).
TacIsABR.
Abort.

Goal (IsABR (insertABR test_abr1 47)).
simpl.
TacIsABR.
Abort.

Goal (IsABR (insertABR test_abr1 49)).
simpl.
TacIsABR.
Abort.

Goal (IsABR (insertABR test_abr1 51)).
simpl.
TacIsABR.
Abort.

Goal (IsABR (insertABR test_abr1 53)).
simpl.
TacIsABR.
Abort.

(*
Goal (IsABR (Node 50
  (Node 40 (Node 20 Empty Empty) (Node 45 Empty Empty))
  (Node 80
    (Node 60 (Node 55 Empty Empty) (Node 70 Empty Empty))
    (Node 200
      (Node 100 (Node 90 Empty (Node 95 Empty Empty)) (Node 150 Empty Empty))
      (Node 500 (Node 400 (Node 300 Empty (Node 350 Empty Empty)) (Node 450 Empty Empty)) Empty)
)))).
TacIsABR.
Abort.

Goal (IsABR (removeABR test_abr3 50)).
simpl.
TacIsABR.
Abort.

Goal (IsABR (removeABR test_abr3 40)).
simpl.
TacIsABR.
Abort.

Goal (IsABR (removeABR test_abr3 20)).
simpl.
TacIsABR.
Abort.

Goal (IsABR (removeABR test_abr3 80)).
simpl.
TacIsABR.
Abort.

Goal (IsABR (removeABR test_abr3 200)).
simpl.
TacIsABR.
Abort.
*)

(* ------------------------------------------------------------------ *)
(* --------------------- functional induction ----------------------- *)
(* ------------------------------------------------------------------ *)
(* functional induction (insertABR tree value) using insertABRInd *)
Functional Scheme insertABRInd := Induction for insertABR Sort Prop.
Functional Scheme searchABRInd := Induction for searchABR Sort Prop.
Functional Scheme removeABRInd := Induction for removeABR Sort Prop.
Functional Scheme searchMinABRInd := Induction for searchMinABR Sort Prop.

(* ------------------------------------------------------------------ *)
(* ------------------------- Proof Search --------------------------- *)
(* ------------------------------------------------------------------ *)
Lemma proof_search_correction : forall (tree : BTree) (n : nat),
  (searchABR tree n) -> (IsNode tree n).
intro.
intro.
functional induction (searchABR tree n) using searchABRInd;intros.
inversion H.
apply CheckSelf.
apply CheckLeft.
apply IHP.
assumption.
apply CheckRight.
apply IHP.
assumption.
Qed.

Lemma proof_search_completude : forall (n : nat) (tree : BTree),
  (IsABR tree) -> (IsNode tree n) -> (searchABR tree n).
do 3 intro.
functional induction (searchABR tree n) using searchABRInd;intros.
inversion H0.
auto.

inversion H;subst.
apply IHP.
TacIsABR.
inversion H0;subst.
omega.
inversion H5.
inversion H5.
inversion H7;subst.
inversion H0;subst.
omega.
apply IHP;assumption.
inversion H9.
inversion H0;subst.
omega.
apply IHP;assumption.
apply IHP.
assumption.
apply (H1 value) in H10.
omega.

inversion H;subst.
apply IHP.
TacIsABR.
inversion H0;subst.
omega.
inversion H5.
inversion H5.
inversion H6;subst.
inversion H0;subst.
omega.
inversion H9.
apply IHP;assumption.
inversion H0;subst.
omega.
apply (H1 value) in H10.
apply IHP.
assumption.
omega.
apply IHP;assumption.

Qed.

(* ------------------------------------------------------------------ *)
(* ------------------------- Proof Insert --------------------------- *)
(* ------------------------------------------------------------------ *)
Lemma proof_insert_empty : forall (n : nat), (IsABR (insertABR Empty n)).
intros.
simpl.
TacIsABR.
Qed.

Lemma proof_insert_leaf : forall (value n : nat),
  (IsABR (insertABR (Node n Empty Empty) value)).
intros.
simpl.
elim (lt_dec value n); elim (Nat.eq_dec value n); intros;
TacIsABR.
Qed.

Lemma proof_insert_is_node : forall (n : nat) (tree : BTree),
  (IsNode (insertABR tree n) n).
intros.
functional induction (insertABR tree n) using insertABRInd.
apply CheckSelf.
apply CheckSelf.
apply CheckLeft.
assumption.
apply CheckRight.
assumption.
Qed.

Lemma proof_insert_missing_correction : forall (n m : nat) (tree : BTree),
  (IsNode (insertABR tree n) m) -> (n <> m) -> (IsNode tree m).
do 3 intro.
functional induction (insertABR tree n) using insertABRInd;intros.
inversion H;subst.
omega.
assumption.
assumption.
assumption.
inversion H;subst.
apply CheckSelf.
apply CheckLeft.
apply IHb.
assumption.
assumption.
apply CheckRight.
assumption.
inversion H;subst.
apply CheckSelf.
apply CheckLeft.
assumption.
apply CheckRight.
apply IHb.
assumption.
assumption.
Qed.

Lemma proof_insert_missing_completude : forall (n m : nat) (tree : BTree),
  (IsNode tree m) -> (IsNode (insertABR tree n) m).
intros.
elim H;intros.
simpl.
elim (lt_dec n n0); elim (Nat.eq_dec n n0);intros;
apply CheckSelf.
simpl.
elim (lt_dec n n_node); elim (Nat.eq_dec n n_node);intros;
apply CheckLeft;
assumption.
simpl.
elim (lt_dec n n_node); elim (Nat.eq_dec n n_node);intros;
apply CheckRight;
assumption.
Qed.

Lemma proof_insert_unexpected_correction : forall (n m : nat) (tree : BTree),
  ~(IsNode (insertABR tree n) m) -> (n <> m) -> ~(IsNode tree m).
do 3 intro.
functional induction (insertABR tree n) using insertABRInd;intros.
intro.
inversion H1.
intro.
inversion H1;subst.
omega.
apply H.
assumption.
apply H.
apply CheckRight.
assumption.
intro.
inversion H1;subst.
apply H.
apply CheckSelf.
apply IHb.
intro.
apply H.
apply CheckLeft.
assumption.
assumption.
assumption.
apply H.
apply CheckRight.
assumption.
intro.
inversion H1;subst.
apply H.
apply CheckSelf.
apply H.
apply CheckLeft.
assumption.
apply IHb.
intro.
apply H.
apply CheckRight.
assumption.
assumption.
assumption.
Qed.

Lemma proof_insert_unexpected_completude : forall (n m : nat) (tree : BTree),
  ~(IsNode tree m) -> (n <> m) -> ~(IsNode (insertABR tree n) m).
do 3 intro.
functional induction (insertABR tree n) using insertABRInd;intros.
intro.
inversion H1;subst.
omega.
inversion H6.
inversion H6.
assumption.
intro.
inversion H1;subst.
apply H.
apply CheckSelf.
apply H.
apply CheckLeft.
apply proof_insert_missing_correction with value;
assumption.
apply H.
apply CheckRight.
assumption.
intro.
inversion H1;subst.
apply H.
apply CheckSelf.
apply H.
apply CheckLeft.
assumption.
apply H.
apply CheckRight.
apply proof_insert_missing_correction with value;
assumption.
Qed.

Lemma insert_left_abr_correction : forall (n m : nat) (left : BTree),
  (IsBTreeLowerThan (insertABR left n) m) -> (n < m) -> (IsBTreeLowerThan left m).
do 3 intro.
functional induction (insertABR left n) using insertABRInd;intros.
TacIsABR.
assumption.
inversion H;subst.
TacIsABR.
apply H1.
rewrite <- H3.
apply CheckSelf.
apply H1.
apply CheckLeft.
apply proof_insert_missing_completude.
assumption.
apply H1.
apply CheckRight.
assumption.
inversion H;subst.
TacIsABR.
apply H1.
apply CheckLeft.
assumption.
apply H1.
apply CheckRight.
apply proof_insert_missing_completude.
assumption.
Qed.

Lemma insert_left_abr_completude : forall (n m : nat) (left : BTree),
  (IsBTreeLowerThan left m) -> (n < m) -> (IsBTreeLowerThan (insertABR left n) m).
do 3 intro.
functional induction (insertABR left n) using insertABRInd;intros.
TacIsABR.
assumption.
inversion H;subst.
TacIsABR.
apply H1.
rewrite <- H3.
apply CheckSelf.
apply H1.
apply CheckLeft.
apply proof_insert_missing_correction with value.
assumption.

Abort.


Lemma insert_right_abr_correction : forall (n m : nat) (right : BTree),
  (IsBTreeGreaterThan (insertABR right n) m) -> (n > m) -> (IsBTreeGreaterThan right m).
do 3 intro.
functional induction (insertABR right n) using insertABRInd;intros.
TacIsABR.
assumption.
inversion H;subst.
TacIsABR.
apply H1.
apply CheckLeft.
apply proof_insert_missing_completude.
assumption.
apply H1.
apply CheckRight.
assumption.
inversion H;subst.
TacIsABR.
apply H1.
rewrite <- H3.
apply CheckSelf.
apply H1.
apply CheckLeft.
assumption.
apply H1.
apply CheckRight.
apply proof_insert_missing_completude.
assumption.
Qed.

Lemma insert_right_abr_completude : forall (n m : nat) (right : BTree),
  (IsBTreeGreaterThan right m) -> (n > m) -> (IsBTreeGreaterThan (insertABR right n) m).
do 3 intro.
functional induction (insertABR right n) using insertABRInd;intros.
TacIsABR.
assumption.
inversion H;subst.
TacIsABR.
apply H1.

Abort.

Lemma insert_is_abr_correction : forall (n : nat) (tree : BTree),
  (IsABR (insertABR tree n)) -> (IsABR tree).
do 2 intro.
functional induction (insertABR tree n) using insertABRInd;intros.
TacIsABR.
assumption.
inversion H;subst.
TacIsABR.
apply IHb.
rewrite <- H2.
TacIsABR.
apply insert_left_abr_correction with value.
rewrite <- H2.
TacIsABR.
assumption.
TacIsABR.
apply insert_left_abr_correction with value;
assumption.
inversion H;subst.
TacIsABR.
apply IHb.
rewrite <- H3.
TacIsABR.
apply insert_right_abr_correction with value.
rewrite <- H3.
TacIsABR.
omega.
TacIsABR.
apply insert_right_abr_correction with value.
assumption.
omega.
Qed.

Lemma insert_is_abr_completude : forall (n : nat) (tree : BTree),
  (IsABR tree) -> (IsABR (insertABR tree n)).
intros.
elim H;intros.
apply proof_insert_empty.
apply proof_insert_leaf.
simpl.
elim (Nat.eq_dec n n0); elim (lt_dec n n0); intros.
TacIsABR.
TacIsABR.
TacIsABR.
inversion H4.
simpl.
TacIsABR.
apply CheckLower;intros.
apply H6.
subst.
apply proof_insert_missing_correction with n.
assumption.


Abort.

Theorem insert_correction : forall (n m : nat) (tree : BTree),
  ((IsABR (insertABR tree n)) /\ ~(IsNode (insertABR tree n) m) /\ (IsNode (insertABR tree n) m) /\ (n <> m))
  -> ((IsABR tree) /\ ~(IsNode tree m) /\ (IsNode tree m) /\ (IsNode (insertABR tree n) n)).
intros.
split.
apply insert_is_abr_correction with n.
elim H;intros.
assumption.
split.
apply proof_insert_unexpected_correction with n.
elim H;intros.
elim H1;intros.
assumption.
elim H;intros.
elim H1;intros.
elim H3;intros.
assumption.
split.
elim H;intros.
elim H1;intros.
elim H3;intros.
apply proof_insert_missing_correction with n.
assumption.
assumption.
apply proof_insert_is_node.
Qed.

Theorem insert_completude : forall (n m1 m2 : nat) (tree : BTree),
  ((IsABR tree) /\ ~(IsNode tree m1) /\ (IsNode tree m2) /\ (n <> m1))
  -> (
    (IsABR (insertABR tree n))
    /\ ~(IsNode (insertABR tree n) m1)
    /\ (IsNode (insertABR tree n) m2)
    /\ (IsNode (insertABR tree n) n)
  ).

Abort.

(* ------------------------------------------------------------------ *)
(* ------------------------- Proof Delete --------------------------- *)
(* ------------------------------------------------------------------ *)

Lemma delete_value : forall (n : nat) (tree : BTree),
  (IsABR tree) -> ~(IsNode (removeABR tree n) n).
intros.
elim H;intros.
simpl.
intro.
inversion H0.
simpl.
elim (Nat.eq_dec n n0) ; elim (lt_dec n n0) ;intros.
intro.
inversion H0.
intro.
inversion H0.
intro.
inversion H0.
omega.
inversion H5.
inversion H5.
intro.
inversion H0.
omega.
inversion H5.
inversion H5.

Abort.

Lemma delete_missing : forall (n m : nat) (tree : BTree),
  (IsNode tree m) -> (m <> n) -> (IsNode (removeABR tree n) m).


Abort.

Lemma delete_unexpected : forall (n m : nat) (tree : BTree),
  ((m <> n) /\ ~(IsNode (removeABR tree n) m)) -> ~(IsNode tree m).

Abort.

Lemma delete_is_abr_correction : forall (n : nat) (tree : BTree),
  (IsABR (removeABR tree n)) -> (IsABR tree).

Abort.

Lemma delete_is_abr_completude : forall (n : nat) (tree : BTree),
  (IsABR tree) -> (IsABR (removeABR tree n)).

Abort.
