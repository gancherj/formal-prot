Add LoadPath "~/fcf/src".
Add LoadPath "../".
Add LoadPath ".".
Require Import FCF.Rat.
Require Import FCF.Fold.
Require Import FcfLems.
Require Import CpdtTactics.
Require Import Dist.
Require Import List.


Definition rel {A B : Set} (P : A -> A -> Prop) (d1 d2 : A -> Dist B) (Q : B -> B -> Prop) :=
  exists (mu : (A * A) -> Dist (B * B)), forall x y, P x y ->
      (d1 x) ~~ (p <- mu (x,y); ret (fst p)) /\
      (d2 y) ~~ (p <- mu (x,y); ret (snd p)) /\
      forall p, In p (distSupport (mu (x, y))) -> Q (fst p) (snd p).

Lemma relCase {A B : Set} (P : A -> A -> Prop) (d1 d2 : A -> Dist B) (Q : B -> B -> Prop) (b : A -> A -> bool) :
  rel (fun x y => (P x y) /\ (b x y) = true) d1 d2 Q /\
  rel (fun x y => (P x y) /\ (b x y) = false) d1 d2 Q ->
  rel P d1 d2 Q.
  intros.
  unfold rel; intros.
  unfold rel in H; destruct H.
  destruct H as [C H].
  destruct H0 as [C' H'].
  exists (fun p => if (b (fst p) (snd p)) then C p else C' p).
  intros.
  remember (b x y) as b0; destruct b0; simpl; subst; symmetry in Heqb0.
  rewrite Heqb0.
  apply H; crush.
  rewrite Heqb0;
  apply H'; crush.
Qed.



  Lemma in_concat_iff {A : Set} : forall (x : A) (ls : list (list A)),
      In x (concat ls) <-> exists l, In l ls /\ In x l.
    intros.
    split.
    induction ls.
    intros.
    inversion H.
    intros.
    simpl in H.
    apply in_app_or in H.
    destruct H.
    exists a.
    crush.
    destruct (IHls H).
    exists x0.
    crush.

    intros.
    destruct H.
    induction ls.
    crush.
    simpl.
    destruct H.
    apply in_app_iff.
    crush.
  Qed.

Lemma distBind_in {A B : Set} (d : Dist A) (d' : A -> Dist B) :
  forall y, In y (distSupport (distBind d d')) -> exists x,
      In x (distSupport d) /\ In y (distSupport (d' x)).
  unfold distBind, distSupport, distJoin. 
  unfold distSum.
  rewrite map_map.
  simpl.
  intros.
  apply in_map_iff in H.
  destruct H.
  destruct H.
  apply in_concat_iff in H0.
  destruct H0.
  destruct H0.
  apply in_map_iff in H0.
  destruct H0.
  exists (snd x1).
  split.
  apply in_map_iff.
  exists x1; crush.
  subst.
  crush.
  apply in_map_iff.
  unfold distScale in H1.
  apply in_map_iff in H1.
  destruct H1.
  destruct H.
  subst.
  simpl.
  exists x0; crush.
 Qed.

Lemma relBind {A B C : Set} (P : A -> A -> Prop) (d1 d2 : A -> Dist B) (d1' d2' : B -> Dist C) (Q : B -> B -> Prop) (R : C -> C -> Prop) :
  rel P d1 d2 Q ->
  rel Q d1' d2' R ->
  rel P (fun a => x <- d1 a; d1' x) (fun a => x <- d2 a; d2' x) R.
  intros.
  unfold rel in H, H0.
  unfold rel; intros.
  destruct H as [c H].
  destruct H0 as [c' H'].
  exists (fun p => x <- c p; c' x).
  intros.
  destruct (H x y H0).
  destruct H2.
  split.

  rewrite bindAssoc.
  etransitivity.
  apply distBind_cong_l.
  apply H1.
  rewrite bindAssoc.
  apply distBind_cong_r; intros.
  rewrite bind_ret.
  destruct x0.
  simpl.
  destruct (H' b b0 (H3 (b,b0) H4)).
  apply H5.

  split.
  rewrite bindAssoc.
  etransitivity.
  apply distBind_cong_l.
  apply H2.
  rewrite bindAssoc.
  apply distBind_cong_r; intros.
  rewrite bind_ret.
  destruct x0.
  simpl.
  destruct (H' b b0 (H3 (b,b0) H4)).
  destruct H6.
  apply H6.

  intros.
  apply distBind_in in H4.
  destruct H4.
  destruct H4.
  destruct (H' (fst x0) (snd x0) (H3 x0 H4)).
  destruct H7.
  apply H8.
  rewrite <- surjective_pairing.
  crush.
Qed.  

Lemma relSound {A B : Set} (d1 d2 : A -> Dist B) :
  rel (fun _ _ => True) d1 d2 eq ->
  forall x, (d1 x) ~~ (d2 x).
  unfold rel.
  intro H; destruct H.
  intros.
  destruct (H x0 x0).
  crush.
  rewrite H0.
  destruct H1.
  rewrite H1.
  apply distBind_cong_r.
  intros.
  unfold distEquiv; crush.
Qed.

Definition unif {A : Set} (xs : list A) `{StdNat.nz (length xs)} : Dist A :=
  map (fun x => (1 / (length xs), x)) xs.

Lemma wf_unif {A : Set} : forall (xs : list A) `{StdNat.nz (length xs)}, wf_Dist (unif xs).
    intros.
    unfold wf_Dist.
    split.
    unfold unif.
    unfold distMass.
    rewrite sumList_map.
    rewrite sumList_map.
    simpl.
    rewrite sumList_body_const.
    apply ratMult_eq_rat1.
    intros.
    unfold unif in H0.
    apply in_map_iff in H0; repeat destruct H0.
    apply in_map_iff in H1; repeat destruct H1.
    crush.
Qed.


Definition unifNats (n : nat) `{StdNat.nz n} : Dist (nat).
  eapply (@unif _ (allNatsLt n)).
  rewrite allNatsLt_length.
  auto.
Defined.

Lemma relConseq {A B : Set} (P P' : A -> A -> Prop) (d1 d2 : A -> Dist B) (Q Q' : B -> B -> Prop) :
  rel P d1 d2 Q ->
  (forall x y, P' x y -> P x y) ->
  (forall x y, Q x y -> Q' x y) ->
  rel P' d1 d2 Q'.
  intros.
  unfold rel in *.
  destruct H.
  exists x; intros.
  destruct (H x0 y (H0 _ _ H2)) as [G1 [G2 G3]].
  split.
  apply G1.
  split.
  apply G2.
  intros; apply H1; apply G3.
  crush.
Qed.

Lemma relFalse {A B : Set} (d1 d2 : A -> Dist B) (Q : B -> B -> Prop) :
  rel (fun _ _ => False) d1 d2 Q.
  unfold rel.
  exists (fun _ => nil).
  intros; crush.
Qed.