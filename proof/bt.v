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

Theorem bounded_step n n' d total 
  (Hn : n <= n')
  (Htotal : n' * 5 < total * 4)
  (Hd : 5 ^ d <= 4 ^ d * n)
  : 5 ^ (S d) <= 4 ^ (S d) * total.
Proof.
  do 2 rewrite (pow_succ_r _ _ (le_0_n _)).
  rewrite <- mult_assoc.

  (* <= weakens ?! *)
  assert ((4 ^ d) * (n' * 5) <= (4 ^ d) * (total * 4)).
  apply mult_le_compat_l.
  intuition.

  rewrite <- Nat.mul_shuffle3.
  apply (le_trans _ (4 ^ d * (n' * 5)) _); intuition.
  
  rewrite (mult_comm n').
  rewrite Nat.mul_shuffle3.
  apply mult_le_compat_l.

  apply (le_trans _ (4 ^ d * n) _).
  trivial.
  
  apply mult_le_compat_l; auto.
Qed.

Theorem bounded_max {n} (l : lbst n) : 5 ^ (depth max l) <= 4 ^ (depth max l) * n.
Proof.
  remember l.
  induction l.
  subst; compute; intuition.

  assert ((max a b) * 5 < (1 + a + b) * 4).
  apply (bounded_disbalance a b l0 b0 l1 l2 Heql0).

  rewrite Heql0.
  simpl (depth max _).
 
  destruct (lt_dec (depth max l1) (depth max l2)).
  * rewrite max_r; intuition.
    apply (bounded_step b (max a b)); intuition.
  * rewrite max_l; intuition.
    apply (bounded_step a (max a b)); intuition.
Qed.