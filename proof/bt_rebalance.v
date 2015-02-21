Require Import Arith NPeano Omega.

Notation k := 4.

Definition balanced (a b : nat) := b < k * a /\ a < k * b.

Inductive lbst : nat -> Set :=
  | Leaf : lbst 1
  | Node (a b : nat) : balanced a b -> lbst a -> lbst b -> lbst (1 + a + b).

Theorem rebalance_one a b (la : lbst a) (lb : lbst b) (H : a = k * b) : lbst (1 + a + b).
Proof.
  destruct la as [ H | al ar bal alt art ].
  
  * subst.
    destruct b; simpl in H.
    inversion H.
    rewrite plus_comm in H.
    inversion H.

  * destruct (le_dec al b).
  
    + destruct art as [ | arl arr rbal arlt arrt ].
      omega. (* Impossible case : (node alt art) > b, but (b < alt) and art is leaf *)

      replace (1 + (1 + al + (1 + arl + arr)) + b) with (1 + (1 + al + arl) + (1 + arr + b)); [| omega].
      
      destruct bal, rbal.
      refine (Node _ _ _ (Node _ _ _ alt arlt) (Node _ _ _ arrt lb)); split; omega.
   
    + replace (1 + (1 + al + ar) + b) with (1 + al + (1 + ar + b)); [| omega].
      destruct bal.
      refine (Node al _ _ alt (Node ar b _ art lb)); split; intuition.
Qed.

(* Right rebalance *)

Theorem rebalance_right_double
  sll slr sr 
  (tll : lbst sll) (tlr : lbst slr) (bl : balanced sll slr)
  (tr : lbst sr)
  (H0 : ~balanced (1 + sll + slr) sr)
  (H1 : (1 + sll + slr) > sr)
  (H2 : sll <= sr)
  : lbst (1 + (1 + sll + slr) + sr).
Proof.
  destruct tlr as [ | slrl slrr blr tlrl tlrr ].
  
  (* Impossible case : (node ll lr) > r, but (r < ll) and lr is leaf *)
  destruct bl, H0; split; omega.

  replace (1 + (1 + sll + (1 + slrl + slrr)) + sr) with (1 + (1 + sll + slrl) + (1 + slrr + sr)); [| omega].
  destruct bl, blr. unfold balanced in H0.
  refine (Node _ _ _ (Node _ _ _ tll tlrl) (Node _ _ _ tlrr tr)); split; omega.
Qed.

Theorem rebalance_right_simple
  sll slr sr 
  (tll : lbst sll) (tlr : lbst slr) (bl : balanced sll slr)
  (tr : lbst sr)
  (H0 : ~balanced (1 + sll + slr) sr)
  (H1 : (1 + sll + slr) > sr)
  (H2 : sll > sr)
  (H3 : slr <= ((pred k) * sr))
  : lbst (1 + (1 + sll + slr) + sr).
Proof.
  replace (1 + (1 + sll + slr) + sr) with (1 + sll + (1 + slr + sr)); [| omega].
  destruct bl; unfold balanced in H0.
  refine (Node _ _ _ tll (Node _ _ _ tlr tr)).

  split; try omega.
  split; try omega.
Qed.

(*Theorem rebalance_right
  sll slr sr 
  (tll : lbst sll) (tlr : lbst slr) (bl : balanced sll slr)
  (tr : lbst sr)
  (H0 : ~balanced (1 + sll + slr) sr)
  (H1 : (1 + sll + slr) > sr)
  (H3 : slr <= ((pred k) * sr))
  : lbst (1 + (1 + sll + slr) + sr).
Proof.
  destruct (le_dec sll sr).
  apply rebalance_right_double; intuition.
  apply rebalance_right_simple; intuition.
Qed.*)

(* Left rebalance *)
Theorem rebalance_left_double
  sl srl srr 
  (tl : lbst sl)
  (trl : lbst srl) (trr : lbst srr) (br : balanced srl srr)
  (H0 : ~balanced sl (1 + srl + srr))
  (H1 : sl < (1 + srl + srr))
  (H2 : srr <= sl)
  : lbst (1 + sl + (1 + srl + srr)).
Proof.
  destruct trl as [ | srll srlr brl trll trlr ].
  
  (* Impossible case : (node rl rr) > l, but (l < rr) and rl is leaf *)
  destruct br, H0; split; omega.

  replace (1 + sl + (1 + (1 + srll + srlr) + srr)) with (1 + (1 + sl + srll) + (1 + srlr + srr)); [| omega].
  destruct br, brl. unfold balanced in H0.
  refine (Node _ _ _ (Node _ _ _ tl trll) (Node _ _ _ trlr trr)); split; omega.
Qed.

Theorem rebalance_left_simple
  sl srl srr 
  (tl : lbst sl)
  (trl : lbst srl) (trr : lbst srr) (br : balanced srl srr)
  (H0 : ~balanced sl (1 + srl + srr))
  (H1 : srr > sl)
  (H2 : srl <= ((pred k) * sl))
  : lbst (1 + sl + (1 + srl + srr)).
Proof.
  replace (1 + sl + (1 + srl + srr)) with (1 + (1 + sl + srl) + srr); [| omega].
  destruct br; unfold balanced in H0.
  refine (Node _ _ _ (Node _ _ _ tl trl) trr).

  split; try omega.
  split; try omega.
Qed.

(*Theorem rebalance_left
  sl srl srr 
  (tl : lbst sl)
  (trl : lbst srl) (trr : lbst srr) (br : balanced srl srr)
  (H0 : ~balanced sl (1 + srl + srr))
  (H1 : (1 + srl + srr) > sl)
  (H2 : srl <= ((pred k) * sl))
  : lbst (1 + sl + (1 + srl + srr)).
Proof.
  destruct (le_dec srr sl).
  apply rebalance_left_double; intuition.
  apply rebalance_left_simple; intuition.
Qed.*)

Theorem rebalance_merge_right
  sll slr sr 
  (tll : lbst sll) (tlr : lbst slr) (bl : balanced sll slr)
  (tr : lbst sr)
  (H0 : ~balanced (1 + sll + slr) sr)
  (H2 : sll > sr)
  (H3 : slr > ((pred k) * sr))
  (tlrtr : lbst (1 + slr + sr))
  : lbst (1 + (1 + sll + slr) + sr).
Proof.
  replace (1 + (1 + sll + slr) + sr) with (1 + sll + (1 + slr + sr)); [| omega].
  
  destruct tll as [| slll sllr bll tlll tllr].
  exfalso.
  inversion H2.
  subst. inversion tr.
  inversion H1.

  destruct (lt_dec (1 + slr + sr) (4 * (1 + slll + sllr))).

  - apply Node; intuition.
    unfold balanced; unfold balanced in bl; intuition.
    apply Node; intuition.

  - destruct (le_dec (3 * (1 + slll + sllr)) slr).
    unfold balanced; unfold balanced in bl, bll, H0.
    apply rebalance_left_double; unfold balanced; trivial.

    apply Node; auto. unfold balanced; auto.
    unfold balanced; unfold balanced in bl.
    elim tlrtr.
    admit. intros; auto.
    
    intuition.
    intuition.
    intuition.
    apply Node; intuition.

    unfold balanced; unfold balanced in bl.
    split. intuition. intuition.
    apply Node; intuition.
Qed.


Theorem rebalance_merge_left
  sl srl srr 
  (tl : lbst sl)
  (trl : lbst srl) (trr : lbst srr) (br : balanced srl srr)
  (H0 : ~balanced sl (1 + srl + srr))
  (H2 : srr > sl)
  (H3 : srl > ((pred k) * sl))
  (trltl : lbst (1 + sl + srl))
  : lbst (1 + sl + (1 + srl + srr)).
Proof.
  replace (1 + sl + (1 + srl + srr)) with (1 + (1 + sl + srl) + srr); [| omega].
  
  destruct trr as [| srrl srrr brr trrl trrr].
  exfalso.
  inversion H2.
  subst. inversion tl.
  inversion H1. 
    
  destruct (lt_dec (1 + sl + srl) (4 * (1 + srrl + srrr))).

  - apply Node; intuition.
    unfold balanced; unfold balanced in br; intuition.
    apply Node; intuition.

  - destruct (le_dec (3 * (1 + srrl + srrr)) srl).
    unfold balanced; unfold balanced in br, brr, H0.
    apply rebalance_right_double; unfold balanced; trivial.

    unfold balanced; unfold balanced in br.
    elim trltl.
    admit. intros; auto.
    apply Node; auto. unfold balanced; auto.

    intuition.
    intuition.
    intuition.
    apply Node; intuition.

    unfold balanced; unfold balanced in br.
    split. intuition. intuition.
    apply Node; intuition.
Qed.

Theorem node_right sl sr 
  (H : sr <= sl)
  (tl : lbst sl) (tr : lbst sr)
  : lbst (1 + sl + sr).
Proof.
  generalize dependent sr.
  induction tl as [| sll slr bl tll IHll tlr IHlr ].
  
  intros.
  apply Node; intuition.
  destruct sr.
  inversion tr.
  unfold balanced; intuition.
  apply Leaf.

  intros.
  destruct (lt_dec (1 + sll + slr) (4 * sr)).
  
  assert (balanced (1 + sll + slr) sr).
  split; intuition.
  apply Node; intuition.
  apply Node; intuition.
  
  assert (~ balanced (1 + sll + slr) sr).
  unfold balanced; intuition.
  
  destruct (le_dec sll sr).
  apply rebalance_right_double; intuition.

  destruct (le_dec slr (pred 4 * sr)).
  apply rebalance_right_simple; intuition.

  apply rebalance_merge_right; intuition.
Qed.

Theorem node_left sl sr 
  (H : sl < sr)
  (tl : lbst sl) (tr : lbst sr)
  : lbst (1 + sl + sr).
Proof.
  generalize dependent sl.
  induction tr as [| srl srr br trl IHrl trr IHrr ].
  
  intros.
  exfalso.
  inversion H; subst; intuition.
  inversion tl.

  intros.
  destruct (lt_dec (1 + srl + srr) (4 * sl)).
  
  assert (balanced sl (1 + srl + srr)).
  split; intuition.
  apply Node; intuition.
  apply Node; intuition.
  
  assert (~ balanced sl (1 + srl + srr)).
  unfold balanced; intuition.
  
  destruct (le_dec srr sl).
  apply rebalance_left_double; intuition.

  destruct (le_dec srl (pred 4 * sl)).
  apply rebalance_left_simple; intuition.

  apply rebalance_merge_left; intuition.
Qed.

Theorem node sl sr (tl : lbst sl) (tr : lbst sr)
  : lbst (1 + sl + sr).
Proof.
  destruct (lt_dec sl sr).
  apply node_left; intuition.
  apply node_right; intuition.
Qed.

(*Fixpoint rebalance_rot_right
  sl sr 
  (tl : lbst sl) (tr : lbst sr)
  (H0 : ~balanced sl sr)
  (H1 : sl > sr)
  (H2 : slr <= ((pred k) * sr))
  : lbst (1 + sl + sr) :=*)
