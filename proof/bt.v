Require Import Arith NPeano Omega.

Definition balanced (k a b : nat) := b < k * a /\ a < k * b.

Inductive lbst (k : nat) : nat -> Set :=
  | Leaf : lbst k 1
  | Node (a b : nat) : balanced k a b -> lbst k a -> lbst k b -> lbst k (1 + a + b).

Theorem balanced_kpos (k a b : nat) : balanced k a b -> k > 1.
Proof.
  intro H.
  destruct H.

  destruct k.
  inversion H.
  destruct k.

  intuition.
  intuition.
Qed.

Theorem bounded_disbalance k a b (node : lbst k (1 + a + b)) bal (la : lbst k a) (lb : lbst k b) :
  (node = Node k a b bal la lb) -> (max a b) * (S k) < (1 + a + b) * k.
Proof.
  intro H.
  inversion bal.
  assert (k > 1). apply (balanced_kpos k a b bal).
   
  destruct (lt_dec a b);
    [rewrite max_r | rewrite max_l];
    intuition;
    rewrite mult_comm; simpl;
    rewrite mult_plus_distr_r, plus_assoc, (mult_comm b), (mult_comm a);
    omega.
Qed.

Fixpoint depth {k n} f (l : lbst k n) : nat :=
  match l with
  | Leaf => 0
  | Node _ _ _ l r => S (f (depth f l) (depth f r))
  end.

Theorem bounded_step k n n' d total 
  (Hn : n <= n')
  (Htotal : n' * (S k) < total * k)
  (Hd : (S k) ^ d <= k ^ d * n)
  : (S k) ^ (S d) <= k ^ (S d) * total.
Proof.
  do 2 rewrite (pow_succ_r _ _ (le_0_n _)).
  rewrite <- mult_assoc.

  (* <= weakens ?! *)
  assert ((k ^ d) * (n' * (S k)) <= (k ^ d) * (total * k)).
  apply mult_le_compat_l.
  intuition.

  rewrite <- Nat.mul_shuffle3.
  apply (le_trans _ (k ^ d * (n' * (S k))) _); intuition.
  
  rewrite (mult_comm n').
  rewrite Nat.mul_shuffle3.
  apply mult_le_compat_l.

  apply (le_trans _ (k ^ d * n) _).
  trivial.
  
  apply mult_le_compat_l; auto.
  rewrite (mult_comm k). auto.
Qed.

Theorem bounded_max {k n} (l : lbst k n) : (S k) ^ (depth max l) <= k ^ (depth max l) * n.
Proof.
  remember l.
  induction l.
  subst; compute; intuition.

  assert ((max a b) * (S k) < (1 + a + b) * k).
  apply (bounded_disbalance k a b l0 b0 l1 l2 Heql0).

  rewrite Heql0.
  simpl (depth max _).
 
  destruct (lt_dec (depth max l1) (depth max l2)).
  * rewrite max_r; intuition.
    apply (bounded_step k b (max a b)); intuition.
  * rewrite max_l; intuition.
    apply (bounded_step k a (max a b)); intuition.
Qed.