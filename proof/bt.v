Require Import Arith NPeano Omega.

Definition balanced (a b : nat) := b < 4 * a /\ a < 4 * b.

Inductive lbst : nat -> Set :=
  | Leaf : lbst 1
  | Node (a b : nat) : balanced a b -> lbst a -> lbst b -> lbst (1 + a + b).

Theorem bounded_disbalance a b (node : lbst (1 + a + b)) bal (la : lbst a) (lb : lbst b) :
  (node = Node a b bal la lb) -> (max a b) * 5 < (1 + a + b) * 4.
Proof.
  intro H.
  inversion bal.
   
  destruct (lt_dec a b).
  rewrite max_r; intuition.
  rewrite max_l; intuition.
Qed.

Fixpoint depth {n} f (l : lbst n) : nat :=
  match l with
  | Leaf => 0
  | Node _ _ _ l r => S (f (depth f l) (depth f r))
  end.

Theorem bounded_max {n} (l : lbst n) : 5 ^ (depth max l) <= 4 ^ (depth max l) * n.
Proof.
  remember l.
  induction l.
  subst; compute; intuition.

  assert (Hl1 := IHl1 l1 eq_refl).
  assert (Hl2 := IHl2 l2 eq_refl).
  clear IHl1 IHl2.

  assert ((max a b) * 5 < (1 + a + b) * 4).
  apply (bounded_disbalance a b l0 b0 l1 l2 Heql0).

  assert (depth max l0 = S (max (depth max l1) (depth max l2))).
  rewrite Heql0. reflexivity.

  destruct (lt_dec (depth max l1) (depth max l2)).
  * rewrite max_r in H0; intuition.
    rewrite H0.
    
    assert (5 * 5 ^ depth max l2 <= 4 * 4 ^ depth max l2 * (1 + a + b)).
    apply (le_trans _ (5 * (4 ^ depth max l2 * b)) _).
    apply mult_le_compat_l. intuition.
    rewrite mult_assoc.
    
    assert (5 * b <= 4 * (1 + a + b)).
    assert (b <= max a b). intuition.
    apply (le_trans _ (5 * max a b) _); intuition.
    rewrite Nat.mul_shuffle0.
    rewrite (Nat.mul_shuffle0 4).
    apply mult_le_compat; auto.
    exact H1.
    
  * rewrite max_l in H0; intuition.
    rewrite H0.
    
    assert (5 * 5 ^ depth max l1 <= 4 * 4 ^ depth max l1 * (1 + a + b)).
    apply (le_trans _ (5 * (4 ^ depth max l1 * a)) _).
    apply mult_le_compat_l. intuition.
    rewrite mult_assoc.
    
    assert (5 * a <= 4 * (1 + a + b)).
    assert (a <= max a b). intuition.
    apply (le_trans _ (5 * max a b) _); intuition.
    rewrite Nat.mul_shuffle0.
    rewrite (Nat.mul_shuffle0 4).
    apply mult_le_compat; auto.
    exact H1.
Qed.