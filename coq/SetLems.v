Require Import Coq.Lists.ListSet.
Require Import CpdtTactics.


Definition set_eq {A} (s t : set A) := forall x, set_In x s <-> set_In x t.
Lemma empty_elim {A} (s : A) : ~ set_In s (empty_set A).
intro.
unfold set_In, empty_set in *.
destruct H.
Qed.

Definition set_disjoint {A} (H : forall x y : A, {x=y} + {x <> y}) (s t : set A) :=
  forall x, ~ (set_In x (set_inter H s t)).

  Lemma set_union_assoc {A : Set} {eqA : forall (x y : A), {x = y} + {x <> y}} : forall (s1 s2 s3 : set A),
      set_eq (set_union eqA s1 (set_union eqA s2 s3)) (set_union eqA (set_union eqA s1 s2) s3).
    intros.
    unfold set_eq.
    split.
    intros.
    apply set_union_elim in H; destruct H.
    apply set_union_intro.
    left; apply set_union_intro; left; crush.
    apply set_union_elim in H; destruct H.
    apply set_union_intro; left; apply set_union_intro; right; crush.
    apply set_union_intro; right; crush.
    intros.
    apply set_union_elim in H; destruct H as [H1 | H2]; [apply set_union_elim in H1; destruct H1 | idtac].
    apply set_union_intro; left; crush.
    apply set_union_intro; right; apply set_union_intro; left; crush.
    apply set_union_intro; right; apply set_union_intro; right; crush.
  Qed.


  Lemma set_union_not_in {A : Set} {eqA : forall (x y : A), {x = y} + {x <> y}} : forall (s1 s2 : set A) x,
      ~ (set_In x (set_union eqA s1 s2)) -> (~ set_In x s1) /\ (~ set_In x s2).
    intros.
    split; intro.
    apply H.
    apply set_union_intro; left; crush.
    apply H.
    apply set_union_intro; right; crush.
 Qed.


  Lemma set_union_cong_l {A : Set} {eqA : forall (x y : A), {x = y} + {x <> y}} : forall (s1 s2 s3 : set A),
      set_eq s1 s2 -> set_eq (set_union eqA s1 s3) (set_union eqA s2 s3).
    intros; unfold set_eq in *.
    intros; split; intros;
    apply set_union_elim in H0; destruct H0 as [H01 | H02].
    apply H in H01.
    apply set_union_intro; crush.
    apply set_union_intro; crush.
    apply H in H01.
    apply set_union_intro; crush.
    apply set_union_intro; crush.
 Qed.
  Lemma set_union_cong_r {A : Set} {eqA : forall (x y : A), {x = y} + {x <> y}} : forall (s1 s2 s3 : set A),
      set_eq s1 s2 -> set_eq (set_union eqA s3 s1) (set_union eqA s3 s2).
    intros; unfold set_eq in *.
    intros; split; intros;
    apply set_union_elim in H0; destruct H0 as [H01 | H02].
    apply set_union_intro; crush.
    apply set_union_intro; crush.
    apply H in H02; crush.
    apply set_union_intro; crush.
    apply H in H02; apply set_union_intro; crush.
 Qed.
