Require Import Coq.Lists.ListSet.
Require Import CpdtTactics.
Require Import List.


Definition set_eq {A} (s t : set A) := forall x, set_In x s <-> set_In x t.
Lemma empty_elim {A} (s : A) : ~ set_In s (empty_set A).
intro.
unfold set_In, empty_set in *.
destruct H.
Qed.

Definition set_disjoint {A} (H : forall x y : A, {x=y} + {x <> y}) (s t : set A) :=
  forall x, ~ (set_In x (set_inter H s t)).

Fixpoint allpairs {A} (xs : list A) : list (A * A) :=
  match xs with
  | nil => nil
  | h :: t =>
    map (fun y => (h,y)) t ++ allpairs t
  end.
    
           

Definition set_pairwise_disjoint {A} (H : forall x y : A, {x=y} + {x <> y}) (xs : list (set A)) :=
  fold_left (fun acc p => acc /\ set_disjoint H (fst p) (snd p)) (allpairs xs) True.

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


  Lemma set_union_cong {A : Set} {eqA : forall (x y : A), {x = y} + {x <> y}} : forall (s1 s2 s3 s4 : set A),
      set_eq s1 s2 -> set_eq s3 s4 -> set_eq (set_union eqA s1 s3) (set_union eqA s2 s4).
    intros; unfold set_eq in *.
    intros; split; intros.
    apply set_union_elim in H1; destruct H1.
    apply set_union_intro; left; apply H; crush.
    apply set_union_intro; right; apply H0; crush.

    apply set_union_elim in H1; destruct H1.
    apply set_union_intro; left; apply H; crush.
    apply set_union_intro; right; apply H0; crush.
  Qed.

  Lemma set_union_symm {A : Set} {eqA : forall (x y : A), {x = y} + {x <> y}} : forall (s1 s2 : set A), set_eq (set_union eqA s1 s2) (set_union eqA s2 s1).
    intros.
    unfold set_eq.
    intros; split; intros H; apply set_union_elim in H; destruct H; apply set_union_intro; crush.
  Qed.

  Lemma set_diff_cong {A : Set} {eqA : forall (x y : A), {x = y} + {x <> y}} : forall (s1 s2 s3 s4 : set A),
      set_eq s1 s2 -> set_eq s3 s4 -> set_eq (set_diff eqA s1 s3) (set_diff eqA s2 s4).
    intros.
    unfold set_eq; intros; split; intros G; apply set_diff_iff in G; destruct G; apply set_diff_iff.
    split; [apply H | intro; apply H2; apply H0]; crush.
    split; [apply H | intro; apply H2; apply H0]; crush.
  Qed.

  Lemma set_eq_refl : forall {A : Set} (s : set A), set_eq s s.
    unfold set_eq; crush.
  Qed.

  Lemma set_eq_trans : forall {A : Set} (s1 s2 s3 : set A), set_eq s1 s2 -> set_eq s2 s3 -> set_eq s1 s3.
    intros; unfold set_eq in *.
    split; intros.
    apply H0; apply H; crush.
    apply H; apply H0; crush.
  Qed.
