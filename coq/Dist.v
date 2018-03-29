
Add LoadPath "~/fcf/src".
Require Import FCF.FCF.
Require Import List.
Require Import CpdtTactics.
Require Import Program.

Definition Dist := Comp.

Notation "c1 ~~ c2" := (forall x, evalDist c1 x == evalDist c2 x) (at level 90).

(* I don't know if this is true. It would be true for a list-based implementation of distributions. *)
Lemma evalDist_getSupport  {A : Set} : forall (c1 c2 : Comp A), c1 ~~ c2 -> Permutation.Permutation (getSupport c1)  (getSupport c2).
  admit.
Admitted.

  
Definition comp_fmap {A B : Set} `{EqDec B} (c : Comp A) (f : A -> B) := x <-$ c; ret (f x).

Lemma comp_fmap_cong {A B : Set} `{EqDec B} (c c' : Comp A) (f : A -> B) :
  c ~~ c' -> (comp_fmap c f) ~~ (comp_fmap c' f).
  intros.
  simpl.
  rewrite sumList_body_eq.
  apply sumList_permutation.
  apply evalDist_getSupport.
  auto.
  intros.
  simpl.
  rewrite H0.
  reflexivity.
Qed.


Lemma fmap_ret {A1 A2 B : Set} `{EqDec A1} `{EqDec A2} `{EqDec B} (f1 : A1 -> B) (f2 : A2 -> B) (x : A1) (y : A2) : 
  f1 x = f2 y ->
  (comp_fmap (ret x) f1) ~~ (comp_fmap (ret y) f2).
    intros.
    unfold comp_fmap.
  crush.
  unfold sumList; unfold fold_left.
  rewrite H2.
  destruct (EqDec_dec H x x).
  destruct (EqDec_dec H0 y y).
  destruct (EqDec_dec H1 (f2 y) x0).
  crush.
  crush.
  crush.
  crush.
Qed.

Section Dist2.
  Context (A : Set).
  Context {eqA : forall x y : A, {x = y} + {x <> y}}.

  Definition Dist2 : Set := list (Rat * A) .

  Definition distMass (d : Dist2) := sumList (map fst d) (fun x => x).

  Definition wf_DistBy (r : Rat) (d : Dist2) :=
  (distMass d == r) /\
  (forall r, In r (map fst d) -> ~ (r == 0)).

  Definition wf_Dist (d : Dist2) := wf_DistBy 1 d.
  

  Lemma wf_DistBy_cons (r r' : Rat) (a : A) (d : Dist2) :
    wf_DistBy r' ((r,a) :: d) -> (~ (r == 0) /\ wf_DistBy (ratSubtract r' r) d).
  intros.
  unfold wf_Dist in H.
  unfold wf_DistBy in H.
  destruct H.
  split.
  apply H0; crush.
  unfold wf_DistBy.
  split.
  unfold distMass in H.
  rewrite map_cons in H.
  rewrite sumList_cons in H.
  simpl in H.
  fold (@distMass d) in H.
  
  admit.
  intros.
  apply H0.
  rewrite map_cons.
  simpl.
  right; crush.
  Admitted.

  Lemma wf_DistBy_app (r : Rat) (d1 d2 : Dist2) :
    wf_DistBy r (d1 ++ d2) <-> wf_DistBy (distMass d1) d1 /\ wf_DistBy (ratSubtract r (distMass d1)) d2.
    admit.
  Admitted.

  
  Definition distSupport (d : Dist2) := map snd d.

  Definition distScale (r : Rat) (d : Dist2) := map (fun p => (r * fst p, snd p)) d.
                           

  Definition distProb  (d : Dist2) (a : A) :=
    fold_left (fun acc p => if eqA (snd p) a then acc + (fst p) else acc) d 0.

End Dist2.

Section Dist2Monad.
  Definition distRet {A} (a : A) := (1, a) :: nil.
Lemma wf_ret : forall {A : Set} (a : A), wf_Dist _ (distRet a).
  intros; unfold wf_Dist, distRet.
  split.
  unfold distMass; unfold sumList; simpl.
  unfold id; rewrite <- ratAdd_0_l; reflexivity.
  simpl.
  intros r H; destruct H; subst; crush.
Qed.


Definition distJoin {A} (eqA: eq_dec A) (eta : Dist2 (Dist2 A)) : Dist2 A :=
  flatten (map (fun p => distScale _ (fst p) (snd p)) eta).

Lemma distJoin_cons {A} (eqA: eq_dec A) (eta : Dist2 (Dist2 A)) (r : Rat) (d : Dist2 A) :
  distJoin eqA ((r, d) :: eta) = (distScale _ r d) ++ (distJoin eqA eta).
  unfold distJoin.
  simpl.
  auto.
Qed.

Lemma wf_join {A : Set} {eqA : forall x y : A, {x = y} + {x <> y}} : forall (d : Dist2 (Dist2 A)) r,
    (forall x, In x (map snd d) -> wf_Dist _ x) -> wf_DistBy _ r d -> wf_DistBy _ r (distJoin eqA d).
  intros.
  induction d.
  unfold distJoin; simpl.
  auto.

  destruct a.
  apply wf_DistBy_cons in H0.
  destruct H0.
  rewrite distJoin_cons.
  
  apply wf_DistBy_app.
  auto.
  split.
  admit.
  admit.
  admit.

Admitted.


End Dist2Monad.