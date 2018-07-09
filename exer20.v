Require Import exer19.
Require Import Arith_base.
   Fixpoint times (n m : nat) : nat :=
      match n with
      | 0    => 0
      | S n' => m + (times n' m)
      end.
    Lemma zero_identity_add_right : forall n, n + 0 = n.
    Proof.
      intro n.
      induction n as [ | n' IHn'].
      +
        simpl.
        reflexivity.
      +
        simpl.
        rewrite IHn'.
        reflexivity.
    Qed.
Lemma mult_zero: forall n, n * 0 = 0.
  Proof.
  intro n.
  induction n as [ | n' IHn'].
  +
    simpl.
    reflexivity.
  +
    simpl.
    rewrite IHn'.
    reflexivity.
Qed.




 
Lemma mult_um_esquerda: forall n, 1*n=n.
  Proof.
  intro n.
  simpl.
  apply zero_identity_add_right.
Qed.

Lemma mult_um_direita: forall n, n*1=n.
  Proof.
  intro n.
   induction n as [ | n' IHn'].
  +
    simpl.
    reflexivity.
  +
    simpl.
    rewrite IHn'.
    reflexivity.
Qed.

 Lemma mult_s : forall m n, m + m * n = m * S n.
 Proof.
   induction m ; simpl ; intros ; try reflexivity.
   assert (m + (n + m * n) = n + (m + m * n)).
   +
          rewrite  add_associative.
          rewrite  add_associative.
          assert (m + n = n + m) by apply plus_comm.
          rewrite H.
          reflexivity.
    +
          rewrite H.
          rewrite (IHm n).
          reflexivity.
Qed.

Lemma mult_commut: forall n m , n * m = m * n.
  Proof.
    induction n.
    +
      intros m.
      simpl.
      rewrite (mult_zero).
      reflexivity.
    +
      intros m.
      simpl.
      rewrite (IHn m).
      apply mult_s.
Qed.

Lemma mult_aux: forall p m n, m * p + n * m * p = (m + n * m) * p.
    induction m;simpl ; intros ; try reflexivity.
    assert (p + m * p + n * S m * p = p + (m + n * S m) * p).
     +
      rewrite plus_comm.
      rewrite plus_assoc.
      rewrite plus_comm.
      rewrite plus_assoc.
      
      reflexivity.
      
    +
      intros.
      simpl.
      
      
      
      

Lemma mul_associative:forall n m p, n * (m * p) = (n * m) * p.
  induction n.
  +
    intros.
    simpl.
    reflexivity.
  +
    intros.
    simpl.
    rewrite (IHn m).
