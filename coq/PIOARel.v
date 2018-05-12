(* Change from Comp to finitely supported distribution, carried by a list of pairs *)

Add LoadPath "~/fcf/src".
Add LoadPath "./Dist".
Require Import FCF.EqDec.
Require Import CpdtTactics.
Require Import List.
Require Import FCF.Rat.
Require Import FCF.Fold.

Require Import Coq.Lists.ListSet.
Require Import SetLems.
Require Import PIOA.
Require Import Dist.
Require Import Program.
Require Import Bool.


Section PIOARel.

  Definition refinement {L : Set} (P1 P2 : @PIOA L) := forall acts, exists acts',
        (f <- (run P1 acts); ret (traceOf P1 f)) ~~ (f <- (run P2 acts'); ret (traceOf P2 f)).

  Lemma refinement_refl : forall {L  : Set} (P : @PIOA L), refinement P P.
    unfold refinement.
    intros.
    exists acts.
    unfold distEquiv; crush.
  Qed.

  Lemma refinement_trans : forall {L : Set} (P Q R : @PIOA L), refinement P Q -> refinement Q R -> refinement P R.
    intros.
    unfold refinement in *.
    intro.
    destruct (H acts).
    destruct (H0 x).
    exists x0.
    rewrite H1.
    crush.
  Qed.

  Add Parametric Relation {L : Set} : (@PIOA L) refinement
  reflexivity proved by refinement_refl
  transitivity proved by refinement_trans
                           as refine_rel.



(* Without convex combination. *)
Section SyncSim.
  Context {L : Set}.
  Context (P1 P2 : @PIOA L).
  Context (c : act_lab P1 -> act_lab P2).


  Record SyncSimR (R : Dist (Frag P1) -> Dist (Frag P2) -> Prop) :=
    {
      sync_obs : (forall e1 e2, R e1 e2 -> (f <- e1; ret (traceOf P1 f)) ~~ (f <- e2; ret (traceOf P2 f)));
      sync_startcond: (R (ret (FragStart _ (start P1))) (ret (FragStart _ (start  P2))));
      sync_stepcond: 
        (forall gamma a, R (run P1 gamma) (run P2 (map c gamma)) -> R (appAction P1 a (run P1 gamma))
                                                      (appAction P2 (c a) (run P2 (map c gamma))))}.
      
      
  Lemma SyncSimObs : forall R (xs : list (act_lab P1)) a, SyncSimR R ->
                                   R (run P1 xs) (run P2 (map c xs)) ->
                                   R (run P1 (a :: xs)) (run P2 ((c a) :: (map c xs))).
    intros.
    rewrite run_cons.
    rewrite run_cons.
    apply (sync_stepcond _ H).
    auto.
  Qed.

  Lemma SyncSymInd : forall R (xs : list (act_lab P1)), SyncSimR R -> R (run P1 xs) (run P2 (map c xs)).
    intros.
    induction xs.
    simpl.
    unfold run.
    unfold appList.
    apply (sync_startcond _ H).
    simpl.
    apply SyncSimObs.
    apply H.
    auto.
  Qed.
  
  Lemma SyncSimSound : forall R, SyncSimR R -> refinement P1 P2.
    intros.
    unfold refinement.
    intros; exists (map c acts).
    apply (sync_obs _ H).
    apply SyncSymInd.
    auto.
  Qed.

End SyncSim.


  Section CompSymm.
    Context {L : Set}.
    Context (P1 P2 : @PIOA L).

    Lemma symm_comp_ins : forall l, comp_ins P1 P2 l = comp_ins P2 P1 l.
    unfold comp_ins.
    crush.
    rewrite orb_comm.
    rewrite (orb_comm (pO P2 l) (pO P1 l)).
    crush.
    Qed.

    Lemma symm_comp_outs : forall l, comp_outs P1 P2 l = comp_outs P2 P1 l.
      unfold comp_outs; crush.
      rewrite orb_comm.
      rewrite (orb_comm (pI P2 l) (pI P1 l)).
      crush.
    Qed.

    Lemma symm_comp_hiddens : forall l, comp_hiddens P1 P2 l = comp_hiddens P2 P1 l.
    unfold comp_hiddens; crush.
    rewrite (orb_comm (pH P1 l)).
    destruct (pH P2 l); crush.
    destruct (pH P1 l); crush.
    rewrite orb_comm.
    rewrite andb_comm.
    rewrite (andb_comm (pI P1 l)).
    crush.
    Qed.

    Definition symm_lab_corr (l : act_lab (P1 |+| P2)) : act_lab (P2 |+| P1).
      unfold act_lab in *; simpl in *; unfold action in *; simpl in *.
      destruct l; econstructor; instantiate (1 := x).
      rewrite <- symm_comp_ins.
      rewrite <- symm_comp_outs.
      rewrite <- symm_comp_hiddens.
      apply e.
    Defined.

    Fixpoint symm_fragCorr (xs : Frag (P2 |+| P1)) : Frag (P1  |+| P2) :=
      match xs with
      | FragStart _ (p2,p1) => FragStart (compPIOA P1 P2) (p1,p2)
      | FragStep _ l (p2,p1) f =>
        FragStep (compPIOA P1 P2) l (p1,p2) (symm_fragCorr f)
      end.

    Lemma symm_refine : refinement (P1 |+| P2) (P2 |+| P1).
    apply (SyncSimSound _ _ symm_lab_corr (fun x y => x ~~ (y0 <- y; ret symm_fragCorr y0))).
    assert (forall x, traceOf (P1 |+| P2) (symm_fragCorr x) = traceOf (P2 |+| P1) x).
    induction x; simpl; destruct p; crush.
    unfold ext_action; simpl.
    rewrite <- symm_comp_ins.
    rewrite <- symm_comp_outs.
    crush.
    crush.

    econstructor.
    intros.
    rewrite (distBind_cong_l _ _ _ H0).
    rewrite bindAssoc.
    apply distBind_cong_r; intros.
    rewrite bind_ret.
    rewrite H.
    unfold distEquiv; crush.
    simpl.
    rewrite bind_ret.
    simpl.
    unfold comp_start; simpl.
    unfold distEquiv; crush.

    intros.
    unfold appAction.
    rewrite (distBind_cong_l _ _ _ H0).
    repeat rewrite bindAssoc.
    apply distBind_cong_r; intros.
    rewrite bind_ret.
    simpl.
    unfold comp_trans; simpl.
    destruct a; simpl.
    assert (forall x, lastState (P2 |+| P1) x = (fun p => (snd p, fst p)) (lastState (P1 |+| P2) (symm_fragCorr x))).
    induction x1; destruct p; crush.
    rewrite H2; simpl.
    destruct (lastState (P1 |+| P2) (symm_fragCorr x)); simpl.

    
    destruct (trans P1 p x0); destruct (trans P2 p0 x0).
    assert ((x0 <- d; y <- d0; ret (x0, y)) ~~ (y <- d0; x0 <- d; ret (x0, y))).
    apply bind_symm; intros; unfold distEquiv; crush.
    rewrite (distBind_cong_l _ _ _ H3).
    repeat rewrite bindAssoc.
    apply distBind_cong_r; intros.
    repeat rewrite bindAssoc.
    apply distBind_cong_r; intros.
    repeat rewrite bind_ret.
    simpl; unfold distEquiv; crush.

    repeat rewrite bindAssoc.
    apply distBind_cong_r; intros.
    repeat rewrite bind_ret.
    simpl; unfold distEquiv; crush.

    repeat rewrite bindAssoc.
    apply distBind_cong_r; intros.
    repeat rewrite bind_ret.
    simpl; unfold distEquiv; crush.

    repeat rewrite bind_ret.
    simpl; unfold distEquiv; crush.
    Qed.

End CompSymm.

Section CompAssoc.
  Context {L : Set}.
  Context (P1 P2 P3 : @PIOA L).


    Lemma assocRefR : refinement (P1 |+| (P2 |+| P3)) ((P1 |+| P2) |+| P3).
      admit.
    Admitted.

    Lemma assocRefL : refinement ((P1 |+| P2) |+| P3) (P1 |+| (P2 |+| P3)).
      admit.
    Admitted.

End CompAssoc.
      
(* Without convex combination. *)
Section SimPIOA.
  Context {L : Set}.
  Context (P1 P2 : @PIOA L).
  Context (c : list (act_lab P1) -> (act_lab P1) -> list (act_lab P2)).

  
  Fixpoint runC (acts : list (act_lab P1)) : list (act_lab P2) :=
    match acts with
    | nil => nil
    | a :: acts' =>
      (c acts' a) ++ (runC acts')
    end.

  Record SimR (R : Dist (Frag P1) -> Dist (Frag P2) -> Prop) :=
    {
      obs : (forall e1 e2, R e1 e2 -> (f <- e1; ret (traceOf P1 f)) ~~ (f <- e2; ret (traceOf P2 f)));
      startcond: (R (ret (FragStart _ (start P1))) (ret (FragStart _ (start  P2))));
      stepcond: 
    (forall gamma a, R (run P1 gamma) (run P2 (runC gamma)) -> R (appAction P1 a (run P1 gamma)) (appList P2 (run P2 (runC gamma)) (c gamma a)))}.
      
      
  Lemma simInd : forall R (xs : list (act_lab P1)) a, SimR R ->
                                   R (run P1 xs) (run P2 (runC xs)) ->
                                   R (run P1 (a :: xs)) (run P2 ((c xs a) ++ (runC xs))).
    intros.
    rewrite run_cons.
    rewrite run_app.
    apply (stepcond _ H).
    auto.
  Qed.

  Lemma simInv : forall R xs, SimR R -> R (run P1 xs) (run P2 (runC xs)).
    intros.
    induction xs.
    simpl.
    unfold run.
    unfold appList.
    apply (startcond _ H).
    simpl.
    apply simInd.
    apply H.
    auto.
  Qed.
  
  Lemma simSound : forall R, SimR R -> refinement P1 P2.
    intros.
    unfold refinement.
    intros; exists (runC acts).
    apply (obs _ H).
    apply simInv.
    auto.
  Qed.

End SimPIOA.


    
Section ImplPIOA.
  Context {L : Set}.
  Context (P1 P2 : @PIOA L).

  
  Definition implement := forall (P : PIOA),
      refinement (compPIOA P1 P) (compPIOA P2 P).

End ImplPIOA.

Section CompImpl.
  Context {L : Set}.
  Context (P1 P2 P3 : @PIOA L).

  Lemma implrefl :
    implement P1 P1.
    intros; unfold implement; intros.
    reflexivity.
  Qed.

  Lemma impltrans :
    implement P1 P2 -> implement P2 P3 -> implement P1 P3.
    intros; unfold implement in *; intros.
    rewrite (H P).
    apply H0.
  Qed.
    

  Lemma implementcomp :
    implement P1 P2 -> implement (compPIOA P1 P3) (compPIOA P2 P3).
    intros.
    unfold implement in *.
    intros.
    rewrite (assocRefL P1 P3 P).
    rewrite (H (compPIOA P3 P)).
    rewrite assocRefR.
    reflexivity.
  Qed.


End CompImpl.

Definition option_lift {A B} (P : A -> B -> Prop) (x : option A) (y : option B) :=
  (x = None /\ y = None) \/
  (exists c1 c2,
      x = Some c1 /\ y = Some c2 /\ P c1 c2).

Section SimplImplement.
  Context {L : Set}.
  Context (P1 P2 : @PIOA L).
  Context (lab_eq1 : pI P1 = pI P2).
  Context (lab_eq2 : pO P1 = pO P2).
  Context (lab_eq3 : pH P1 = pH P2).
  Context (st_corr : pQ P1 -> pQ P2).
  Context (start_corr : st_corr (start P1) = start P2).
  Context (trans_corr :
             forall s l,
               option_lift (fun d1 d2 => (x <- d1; ret (st_corr x)) ~~ d2) (trans P1 s l) (trans P2 (st_corr s) l)
               ).

  

  Definition simpl_lab_corr : forall P, act_lab (P1 |+| P) -> act_lab (P2 |+| P).
    intros.
    destruct H.
    econstructor.
    unfold action in *; simpl in *; unfold comp_ins, comp_hiddens, comp_outs in *.
  repeat rewrite lab_eq1 in e.
  repeat rewrite lab_eq2 in e.
  repeat rewrite lab_eq3 in e.
  apply e.
  Defined.

  Fixpoint simpl_actlist_corr (P : PIOA) (al : list (act_lab (P1 |+| P))) :=
    map (simpl_lab_corr P) al.

  Definition simpl_frag_corr (P : PIOA) (f : Frag (P1 |+| P)) : Frag (P2 |+| P).
    induction f.
    apply FragStart.
    simpl in p.
    simpl.
    split.
    apply (st_corr (fst p)).
    apply (snd p).

    apply FragStep.
    apply l.
    simpl in *.
    apply (st_corr (fst p), snd p).
    apply IHf.
  Defined.

  Lemma simpl_frag_corr_correct (P : PIOA) (f : Frag (P1 |+| P)) :
    traceOf _ (simpl_frag_corr _ f) = traceOf _ f.
  induction f.
  simpl; unfold distEquiv; crush.
  simpl.
  rewrite IHf.
  unfold ext_action; simpl; unfold comp_ins, comp_outs.
  rewrite lab_eq1.
  rewrite lab_eq2.
  auto.
  Qed.

  Definition simpl_simR : forall P, Dist (Frag (P1 |+| P)) -> Dist (Frag (P2 |+| P)) -> Prop :=
    fun _ e1 e2 =>
      (x <- e1; ret (simpl_frag_corr _ x)) ~~ e2.

  Lemma simpl_sim : forall P, SyncSimR (P1 |+| P) (P2 |+| P) (simpl_lab_corr P) (simpl_simR P).
  intros; constructor.
  intros.
  unfold simpl_simR in H.
  symmetry in H.
  rewrite (distBind_cong_l _ _ _ H).
  rewrite bindAssoc.
  apply distBind_cong_r; intros.
  rewrite bind_ret; simpl.
  rewrite simpl_frag_corr_correct.
  unfold distEquiv; crush.
  unfold simpl_simR; simpl.
  rewrite bind_ret.
  simpl.
  unfold comp_start; simpl.
  rewrite start_corr.
  unfold distEquiv; crush.
  intros.
  unfold simpl_simR in *.
  unfold appAction.
  symmetry; symmetry in H.
  rewrite (distBind_cong_l _ _ _ H).
  repeat rewrite bindAssoc.
  apply distBind_cong_r; intros.
  rewrite bind_ret.
  simpl.
  unfold comp_trans; simpl.
  assert (forall x, lastState (P2 |+| P) (simpl_frag_corr P x) =
          ((st_corr (fst (lastState _ x)), snd (lastState _ x)))).
  induction x0; crush.
  rewrite H1; simpl.
  destruct (lastState (P1 |+| P) x); simpl.
  destruct a; simpl.
  unfold option_lift in trans_corr.
  destruct (trans_corr p x0).
  destruct H2.
  rewrite H2, H3.
  destruct (trans P p0 x0).
  repeat rewrite bindAssoc.
  apply distBind_cong_r; intros; repeat rewrite bind_ret; simpl.
  unfold distEquiv; crush.
  rewrite bind_ret; unfold distEquiv; crush.
  destruct H2.
  destruct H2.
  destruct H2.
  destruct H3.
  rewrite H2, H3.
  destruct (trans P p0 x0).
  repeat rewrite bindAssoc.
  symmetry in H4.
  rewrite (distBind_cong_l _ _ _ H4).
  repeat rewrite bindAssoc.
  apply distBind_cong_r; intros.
  rewrite bind_ret; repeat rewrite bindAssoc.
  apply distBind_cong_r; intros.
  repeat rewrite bind_ret.
  simpl.
  unfold distEquiv; crush.
  rewrite bindAssoc.
  symmetry in H4.
  rewrite (distBind_cong_l _ _ _ H4).
  repeat rewrite bindAssoc.
  apply distBind_cong_r; intros.
  repeat rewrite bind_ret; simpl.
  unfold distEquiv; crush.
Qed.  
  
  Lemma simpl_implement : implement P1 P2.
    unfold implement.
    intros.
    eapply SyncSimSound.
    apply simpl_sim.
  Qed.
    
End SimplImplement. 

  
  Add Parametric Relation {L : Set} : (@PIOA L) implement
  reflexivity proved by implrefl 
  transitivity proved by impltrans
                           as implement_rel.

End PIOARel.
    


