Require Import Coq.Lists.ListSet.


Definition set_eq {A} (s t : set A) := forall x, set_In x s <-> set_In x t.
Lemma empty_elim {A} (s : A) : ~ set_In s (empty_set A).
intro.
unfold set_In, empty_set in *.
destruct H.
Qed.

Definition set_disjoint {A} (H : forall x y : A, {x=y} + {x <> y}) (s t : set A) := set_inter H s t = empty_set A.


Lemma set_inter_symm {A} (eqA : forall x y : A, {x = y} + {x <> y}) (s t : set A) : forall x, set_In x (set_inter eqA s t) -> set_In x (set_inter eqA t s).
  admit.
Admitted.


Lemma diff_disjoint {A} {H : forall x y : A, {x = y} + {x <> y}} :
  forall s t, set_disjoint H s t <-> (forall x, set_In x s -> ~ set_In x t) /\ (forall x, set_In x t -> ~ set_In x s).
  split.
  intro.
  unfold set_disjoint in *.
  split; intros.
  intro.
  pose proof (set_inter_intro H x s t H1 H2).
  rewrite H0 in H3.
  apply (empty_elim x H3).

  intro.
  pose proof (set_inter_intro H x t s H1 H2).
  apply set_inter_symm in H3.
  rewrite H0 in H3.
  apply (empty_elim x H3).
  intros.
  admit.
Admitted.

Lemma diff_disjoint' {A} {H : forall x y : A, {x = y} + {x <> y}} :
  forall s t : set A, set_disjoint H (set_diff H s t) t.
  admit.
Admitted.

Lemma union_assoc {A} {H : forall x y : A, {x = y} + {x <> y}} {a b c : set A} : set_eq (set_union H a (set_union H b c)) (set_union H (set_union H a b) c).
  admit.
Admitted.