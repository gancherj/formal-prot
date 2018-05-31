Add LoadPath "~/fcf/src".
Add LoadPath "../".
Require Import FCF.Rat.
Require Import FCF.Fold.
Require Import CpdtTactics.
Require Import Ring.
Require Import List.
Require Import Coq.Classes.Equivalence.
Require Import Relation_Definitions.
Require Import FcfLems.
Open Scope rat_scope.



Lemma sr_rat : @semi_ring_theory Rat 0 1 ratAdd ratMult eqRat.
  econstructor.
  intros; rewrite <- ratAdd_0_l; auto.
  crush.
  intros; rewrite ratAdd_comm; crush.
  intros; rewrite ratAdd_assoc; crush.
  intros; rewrite ratMult_1_l; crush.
  intros; rewrite ratMult_0_l; crush.
  intros; rewrite ratMult_comm; crush.
  intros; rewrite ratMult_assoc; crush.
  intros; rewrite ratMult_comm; rewrite ratMult_distrib; rewrite ratMult_comm; apply ratAdd_eqRat_compat; [crush | apply ratMult_comm; crush].
  Defined.


Add Ring ratring : sr_rat.

Class DecEquiv {A : Type} (R : relation A) :=
  {
    REquiv :> Equivalence R;
    eqb : A -> A -> bool;
    eqb_equiv : forall a b : A, eqb a b = true <-> R a b
  }.

Definition Dist (A : Set) : Set := list (Rat * A).

Definition ratDisp (r : Rat) : nat * nat :=
  match r with
  | RatIntro n1 p =>
    match p with
    | exist _ n2 _ => (n1, n2)
    end
  end.

Definition distDisp {A} (d : Dist A) : list ((nat * nat) * A) :=
  map (fun p => (ratDisp (fst p), snd p)) d.

Section DistOps.
  Context {A : Set}.
  Definition distMass (d : Dist A) := sumList (map fst d) (fun x => x).
  Definition wf_Dist (d : Dist A) :=
    (distMass d == 1) /\
    (forall r, In r (map fst d) -> ~ (r == 0)).
  Definition distSupport (d : Dist A) := map snd d.
  Definition integ (d : Dist A) (f : A -> Rat) :=
    sumList d (fun p => (fst p) * (f (snd p))).

  Definition distEquiv (d1 d2 : Dist A) := forall f, integ d1 f == integ d2 f.

End DistOps.

Section DistMonad.
  Context {A B : Set}.

  Definition distRet (a : A) : Dist A := (1, a) :: nil.
  Lemma distRet_wf : forall a, wf_Dist (distRet a).
    intros.
    unfold wf_Dist, distRet.
    split.

    unfold distMass; unfold sumList; crush; ring.
    intros.
    inversion H; crush.
  Qed.


  Definition distScale (r : Rat) (d : Dist B) :=
    map (fun p => (r * (fst p), snd p)) d.

  Definition distSum (ds : list (Dist B)) := concat ds.
  
  Definition distJoin (d : Dist (Dist B)) : Dist B :=
    distSum (map (fun p => distScale (fst p) (snd p)) d).

  Definition distBind (d : Dist A) (f : A -> Dist B) : Dist B :=
    distJoin (map (fun p => (fst p, f (snd p))) d).
   
  Definition dist_fmap (d : Dist A) (f : A -> B) : Dist B :=
    map (fun p => (fst p, f (snd p))) d.
End DistMonad.

Notation "'ret' x" := (@distRet  _ x) (at level 75).
Notation "x <- c1 ; c2" := (@distBind _ _ c1 (fun x => c2))
   (right associativity, at level 81, c1 at next level).                       



Notation "x ~~ y" := (@distEquiv _ x y) (at level 60).

Require Import Setoid.

Lemma equiv_symm {A : Set} : forall (d1 d2 : Dist A),
    d1 ~~ d2 -> d2 ~~ d1.
  intros; unfold distEquiv in *; intros; crush.
Qed.

Lemma equiv_trans {A : Set} : forall (d1 d2 d3 : Dist A),
    d1 ~~ d2 -> d2 ~~ d3 -> d1 ~~ d3.
  intros; unfold distEquiv in *; intros; crush.
Qed.

Lemma equiv_refl {A : Set} : forall (d : Dist A), d ~~ d.
  intros; unfold distEquiv; intros; crush.
Qed.

Add Parametric Relation (A : Set) : (Dist A) (@distEquiv A)
   symmetry proved by equiv_symm
   transitivity proved by equiv_trans
   as dist_eq
.

(* Lemmas about monadic operations and ~~ *)

  Lemma bindAssoc {A B C : Set} : forall (c1 : Dist A) (c2 : A -> Dist B) (c3 : B -> Dist C),
    (x <- (y <- c1; c2 y); c3 x) ~~ (y <- c1; x <- c2 y; c3 x).
    intros.
    unfold distEquiv.
    intros.
    unfold distBind.
    unfold integ.
    unfold distJoin.
    unfold distSum.
    rewrite sumList_concat.
    rewrite sumList_map.
    rewrite sumList_map.
    rewrite sumList_concat.
    rewrite sumList_map.
    rewrite sumList_map.
    rewrite sumList_concat.
    rewrite sumList_map.
    rewrite sumList_map.
    apply sumList_body_eq; intros.

    unfold distScale.
    simpl.
    rewrite sumList_map.
    rewrite sumList_map.
    rewrite sumList_concat.
    rewrite sumList_map.
    rewrite sumList_map.
    apply sumList_body_eq; intros.
    rewrite sumList_map.
    rewrite sumList_map.
    simpl.
    apply sumList_body_eq; intros.
    ring.
Qed.

  Lemma bind_ret {A B : Set} (x : A) (c : A -> Dist B) :
    (z <- (ret x); c z) ~~ c x.
    intros; unfold distEquiv; intros; simpl.
    unfold integ.
    unfold distBind.
    unfold distJoin.
    unfold distSum.
    rewrite sumList_concat.
    rewrite sumList_map.
    rewrite sumList_map.
    unfold distRet.
    simpl.
    rewrite sumList_cons.
    rewrite sumList_nil.
    unfold distScale; simpl.
    rewrite sumList_map.
    rewrite <- ratAdd_0_r.
    apply sumList_body_eq; intros.
    simpl.
    ring.
  Qed.


Ltac in_sumList_l := eapply eqRat_trans; [ apply sumList_body_eq; intros; simpl | idtac] .

Lemma distBind_cong_l {A B : Set} (d d' : Dist A) (c : A -> Dist B) :
  d ~~ d' ->
  distBind d c ~~ distBind d' c.
  intros.
  unfold distBind, distEquiv in *.
  unfold distJoin.
  unfold distSum.
  intros.

  rewrite map_map.
  rewrite map_map.
  unfold distScale.
  unfold integ in H.
  unfold integ.
  rewrite sumList_concat.
  rewrite sumList_concat.
  rewrite sumList_map.
  rewrite sumList_map.
  simpl.
  in_sumList_l.
  apply sumList_map.
  simpl.
  eapply eqRat_trans.
  in_sumList_l.
  in_sumList_l.
  apply ratMult_assoc.
  apply sumList_factor_constant_l.
  apply (H (fun a => sumList (c a) (fun a0 => fst a0 * f (snd a0)))).
  apply sumList_body_eq.
  intros.
  rewrite sumList_map.
  simpl.
  symmetry.
  in_sumList_l.
  apply ratMult_assoc.
  rewrite sumList_factor_constant_l.
  crush.
Qed.

Lemma distBind_cong_r {A B : Set} (d : Dist A) (c c' : A -> Dist B) :
  (forall x, In x (distSupport d) -> c x ~~ c' x) ->
  distBind d c ~~ distBind d c'.
  intros.
  unfold distBind, distEquiv in *.
  unfold distJoin; unfold distSum; intros.
  rewrite map_map.
  unfold integ; intros.
  rewrite map_map.
  rewrite sumList_concat.
  rewrite sumList_concat.
  repeat rewrite sumList_map.
  apply sumList_body_eq; intros.
  simpl.
  unfold distScale; simpl.
  repeat rewrite sumList_map.
  simpl.
  unfold integ in H.
  destruct a; simpl.
  in_sumList_l.
  apply ratMult_assoc.
  rewrite sumList_factor_constant_l.
  rewrite H.
  symmetry; in_sumList_l.
  apply ratMult_assoc.
  rewrite sumList_factor_constant_l.
  crush.
  unfold distSupport.
  apply in_map_iff.
  exists (r,a); crush.
Qed.  

Lemma distBind_cong_r_weak {A B : Set} (d : Dist A) (c c' : A -> Dist B) :
  (forall x, c x ~~ c' x) ->
  distBind d c ~~ distBind d c'.
  intros.
  unfold distBind, distEquiv in *.
  unfold distJoin; unfold distSum; intros.
  rewrite map_map.
  unfold integ; intros.
  rewrite map_map.
  rewrite sumList_concat.
  rewrite sumList_concat.
  repeat rewrite sumList_map.
  apply sumList_body_eq; intros.
  simpl.
  unfold distScale; simpl.
  repeat rewrite sumList_map.
  simpl.
  unfold integ in H.
  destruct a; simpl.
  in_sumList_l.
  apply ratMult_assoc.
  rewrite sumList_factor_constant_l.
  rewrite H.
  symmetry; in_sumList_l.
  apply ratMult_assoc.
  rewrite sumList_factor_constant_l.
  crush.
Qed.

Lemma ret_equiv_elim {A : Set} {H : forall (x y : A), {x = y} + {x <> y}} (x y : A) :
  (ret x) ~~ (ret y) -> x = y.
  intros.
  destruct (H x y).
  auto.

  unfold distEquiv in H0.
  unfold distRet in H.
  unfold integ in H; simpl in H.
  unfold sumList in H; simpl in H.
  pose proof (H0 (fun a => if H a x then 1 else 0)).
  unfold integ in H1.
  unfold sumList in H1; unfold distRet in H1; simpl in *.
  repeat rewrite <- ratAdd_0_l in H1.
  repeat rewrite ratMult_1_l in H1.
  destruct (H x x); destruct (H y x); crush.
Qed.

Lemma bind_symm {A B C: Set} (d11 d12 : Dist A) (d21 d22 : Dist B) (c1 c2 : A -> B -> Dist C) :
  (forall x y, c1 x y ~~ c2 x y) -> 
  d11 ~~ d12 ->
  d21 ~~ d22 ->
  (x <- d11; y <- d21; c1 x y) ~~
  (y <- d22; x <- d12; c2 x y).
  admit.
Admitted.

  
(* Lemmas about well-formedness *)

Lemma join_distmass {A : Set} (d : Dist (Dist A)) : distMass d == 1 -> (forall p, In p (map snd d) -> distMass p == 1) -> distMass (distJoin d) == 1.
  intros.
  unfold distJoin.
  unfold distSum.
  unfold distMass.
  rewrite sumList_map.
  rewrite sumList_concat.
  rewrite sumList_map.
  unfold distMass in H.
  rewrite sumList_map in H.
  rewrite <- H.
  apply sumList_body_eq.
  intros.
  simpl.
  unfold distScale; simpl.
  rewrite sumList_map.
  simpl.
  rewrite sumList_factor_constant_l.
  unfold distMass in H0.
  cut (sumList (snd a) fst == 1).
  intro H2; rewrite H2; ring.
  rewrite <- H0.
  rewrite sumList_map.
  reflexivity.
  apply in_map.
  crush.
Qed.


Lemma join_in {A : Set} (d : Dist (Dist A)) :
  forall r, In r (map fst (distJoin d)) ->
            exists p r',
              In p d /\ In r' (map fst (snd p)) /\ r == (fst p) * r'.
  induction d.
  intros.
  unfold distJoin in H; simpl in H; crush.
  intros.
  unfold distJoin in H.
  simpl in H.
  rewrite map_app in H.
  apply in_app_or in H.
  destruct H.
  exists a.
  destruct a; simpl in H.
  unfold distScale in H.
  rewrite map_map in H.
  simpl in H.
  simpl.
  apply in_map_iff in H.
  destruct H.
  exists (fst x).
  crush.
  apply in_map; crush.

  destruct (IHd r H).
  destruct H0.
  exists x,x0.
  crush.
Qed.


Lemma join_neq_0 {A : Set} (d : Dist (Dist A)) : (forall r, In r (map fst d) -> ~ (r == 0)) /\
                                                 (forall p r, In p (map snd d) -> In r (map fst p) -> ~ (r == 0)) ->
                                                 (forall r, In r (map fst (distJoin d)) -> ~ (r == 0)).
  intros.
  apply join_in in H0.
  repeat destruct H0.
  destruct H1.
  rewrite H2.
  apply ratMult_nz.
  destruct H.
  split.
  apply H.
  apply in_map; auto.
  eapply H3.
  apply in_map.
  apply H0.
  auto.
Qed.
  
Lemma wf_DistJoin {A : Set} (d : Dist (Dist A)) : wf_Dist d -> (forall p, In p d -> wf_Dist (snd p)) -> wf_Dist  (distJoin d).
  intros.
  unfold wf_Dist in H; destruct H.
  unfold wf_Dist.
  split.
  apply join_distmass.
  crush.
  intros.
  apply in_map_iff in H2.
  
  destruct H2.
  destruct H2.
  destruct (H0 x).
  crush.
  rewrite <- H2; crush.

  apply join_neq_0.
  split.
  apply H1.
  intros.
  apply in_map_iff in H2.
  destruct H2.
  destruct H2; subst.
  destruct (H0 _ H4).
  apply H5.
  crush.
Qed.

Lemma wf_DistBind {A B : Set} (d : Dist A) (f : A -> Dist B) : wf_Dist d -> (forall a, wf_Dist (f a)) -> wf_Dist (distBind d f).
  intros.
  unfold distBind.
  apply wf_DistJoin.
  unfold wf_Dist.
  split.
  unfold distMass.
  rewrite map_map.
  simpl.
  destruct H.
  apply H.
  destruct H.
  intros.
  apply H1.
  rewrite map_map in H2.
  simpl in H2.
  auto.

  intros.
  apply in_map_iff in H1.
  destruct H1.
  destruct H1; subst.
  simpl.
  apply H0.
Qed.  

