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


Module PIOARel (L : LAB).

  Module P := PIOADef L.
  Import P.
  Import L.

  Definition refinement (P1 P2 : PIOA) := forall acts, exists acts',
        (f <- (run P1 acts); ret (traceOf P1 f)) ~~ (f <- (run P2 acts'); ret (traceOf P2 f)).

  Lemma refinement_refl : forall P, refinement P P.
    unfold refinement.
    intros.
    exists acts.
    unfold distEquiv; crush.
  Qed.

  Lemma refinement_trans : forall P Q R, refinement P Q -> refinement Q R -> refinement P R.
    intros.
    unfold refinement in *.
    intro.
    destruct (H acts).
    destruct (H0 x).
    exists x0.
    rewrite H1.
    crush.
  Qed.

  Add Parametric Relation : PIOA refinement
  reflexivity proved by refinement_refl
  transitivity proved by refinement_trans
                           as refine_rel.

  Section CompSymm.
    Context (P1 P2 : PIOA).
    Context {eqP1 : EqDec (pQ P1)}.
    Context {eqP2 : EqDec (pQ P2)}.
    Check compPIOA.

    Definition symm_loc_lab_corr (l : act_lab (compPIOA P1 P2)) : act_lab (compPIOA P2 P1).
      unfold act_lab in *; simpl in *; unfold action in *; simpl in *.
      unfold comp_ins, comp_outs, comp_hiddens in *.
      destruct l.
      econstructor.

      apply set_union_elim in s; destruct s.
      apply set_diff_iff in H; destruct H.
      apply set_union_intro; left; apply set_diff_iff; split.
      apply set_union_elim in H; destruct H; apply set_union_intro; [right | left]; apply H.
      intro; apply H0.
      apply set_union_elim in H1; destruct H1; apply set_union_intro; crush.
      apply set_union_elim in H; destruct H.
      apply set_union_elim in H; destruct H; apply set_union_intro; right; apply set_union_intro; left; apply set_union_intro; crush.
      apply set_union_elim in H; destruct H; apply set_union_intro; right; apply set_union_intro; right; apply set_union_intro; crush.
    Defined.

    
    Fixpoint symm_fragCorr (xs : Frag (compPIOA P2 P1)) : Frag (compPIOA P1 P2) :=
      match xs with
      | FragStart _ (p2,p1) => FragStart (compPIOA P1 P2) (p1,p2)
      | FragStep _ l (p2,p1) f =>
        FragStep (compPIOA P1 P2) l (p1,p2) (symm_fragCorr f)
      end.


    Fixpoint symm_actCorr (xs : ActList (compPIOA P1 P2)) : ActList (compPIOA P2 P1) :=
      match xs with
      | ActNil _ => ActNil _
      | ActCons _ xs x => ActCons _ (symm_actCorr xs) (symm_loc_lab_corr x)
      end.
                      
    
    Lemma refSymm : refinement (compPIOA P1 P2) (compPIOA P2 P1).
      unfold refinement; intros.


      cut ((run (compPIOA P1 P2) acts) ~~ (f <- run (compPIOA P2 P1) (symm_actCorr acts); ret (symm_fragCorr f))).

      intros.
      
      exists (symm_actCorr acts).
      rewrite (distBind_cong_l _ _ _ H).
      rewrite bindAssoc.

      apply distBind_cong_r_weak; intros.
      rewrite bind_ret.
      induction x.
      unfold symm_fragCorr.
      destruct p; simpl; unfold distEquiv; crush.
      Check frag_eq.


      pose proof (@ret_equiv_elim _ (EqDec_dec (list_EqDec eqd_lab))).
      apply H0 in IHx.
      simpl.
      destruct p.
      simpl.
      rewrite IHx.
      destruct (set_In_dec (EqDec_dec eqd_lab) l (ext_action (compPIOA P1 P2)));
      destruct (set_In_dec (EqDec_dec eqd_lab) l (ext_action (compPIOA P2 P1))).
      unfold distEquiv;
      crush.
      unfold ext_action in *.
      simpl in *.

      unfold comp_ins, comp_outs in *.

      exfalso.
      apply n.
      apply set_union_elim in s; destruct s.
      apply set_diff_iff in H1; destruct H1.
      apply set_union_intro; left; apply set_diff_iff; split.
      apply set_union_elim in H1; destruct H1; apply set_union_intro; crush.
      intro.
      apply H2.
      apply set_union_elim in H3; destruct H3; apply set_union_intro; crush.
      apply set_union_elim in H1; apply set_union_intro; right; crush.
      apply set_union_intro; crush.
      apply set_union_intro; crush.

      exfalso.
      apply n.
      unfold ext_action in *; simpl in *; unfold comp_ins, comp_outs in *; simpl in *.
      apply set_union_elim in s; destruct s.
      apply set_diff_iff in H1; destruct H1.
      apply set_union_intro; left; apply set_diff_iff; split.
      apply set_union_elim in H1; destruct H1; apply set_union_intro; crush.
      intro.
      apply H2.
      apply set_union_elim in H3; destruct H3; apply set_union_intro; crush.
      apply set_union_elim in H1; apply set_union_intro; right; crush.
      apply set_union_intro; crush.
      apply set_union_intro; crush.
      unfold distEquiv; crush.

      induction acts.
      unfold run; simpl.
      rewrite bind_ret.
      simpl.
      unfold comp_start.
      unfold distEquiv; crush.
      rewrite run_cons.
      unfold appAction.
      simpl.
      rewrite (distBind_cong_l _ _ _ IHacts).
      rewrite bindAssoc.
      rewrite run_cons.
      unfold appAction.
      rewrite bindAssoc.
      apply distBind_cong_r_weak; intros.
      rewrite bind_ret.
      simpl.
      unfold comp_trans.
      destruct a.
      simpl.
      assert (trans P1 (fst (lastState (compPIOA P1 P2) (symm_fragCorr x))) x0 =
              trans P1 (snd (lastState (compPIOA P2 P1) x)) x0).
      induction x; simpl; destruct p; simpl; auto.

      assert (trans P2 (snd (lastState (compPIOA P1 P2) (symm_fragCorr x))) x0 =
              trans P2 (fst (lastState (compPIOA P2 P1) x)) x0).
      induction x; simpl; destruct p; simpl; auto.

      repeat rewrite H; repeat rewrite H0.
      destruct (trans P1 (snd (lastState (compPIOA P2 P1) x)) x0).
      destruct (trans P2 (fst (lastState (compPIOA P2 P1) x)) x0).
      repeat rewrite bindAssoc.

      cut ((y <- d; (y0 <- d0; ret (y, y0))) ~~ (y <- d0; (y0 <- d; ret (y0, y)))).
      intro.
      rewrite <- bindAssoc.
      rewrite (distBind_cong_l _ _ _ H1).
      rewrite bindAssoc.
      apply distBind_cong_r; intros.
      repeat rewrite bindAssoc.
      apply distBind_cong_r; intros.
      repeat rewrite bind_ret.
      simpl.
      unfold distEquiv; crush.
      apply bind_symm.
      intros; unfold distEquiv; crush.
      intros; unfold distEquiv; crush.
      intros; unfold distEquiv; crush.
      Ltac dsimp := try apply distBind_cong_r; intros; repeat rewrite bindAssoc; try rewrite bind_ret.
      repeat dsimp.
      simpl.
      induction x; simpl; destruct p; simpl; auto.
      unfold distEquiv; crush.
      unfold distEquiv; crush.
      destruct (trans P2 (fst (lastState (compPIOA P2 P1) x)) x0).
      repeat rewrite bindAssoc.
      apply distBind_cong_r; intros.
      repeat rewrite bind_ret.
      simpl.
      induction x; simpl; destruct p; simpl; auto.
      unfold distEquiv; crush.
      unfold distEquiv; crush.

      rewrite bind_ret; unfold distEquiv; crush.

      Qed.

End CompSymm.

Section CompAssoc.
  Context (P1 P2 P3 : PIOA).


  Definition assoc_loc_lab_corr (l : act_lab (compPIOA P1 (compPIOA P2 P3))) : act_lab (compPIOA P1 (compPIOA P2 P3)).
    admit.
  Admitted.

    Lemma assocRefR : refinement (compPIOA P1 (compPIOA P2 P3)) (compPIOA (compPIOA P1 P2) P3).
      admit.
    Admitted.

    Lemma assocRefL : refinement  (compPIOA (compPIOA P1 P2) P3) (compPIOA P1 (compPIOA P2 P3)).
      admit.
    Admitted.

End CompAssoc.
      
(* Without convex combination. *)
Section SimPIOA.
  Context (P1 P2 : PIOA).
  Context (c : ActList P1 -> act_lab P1 -> ActList P2).

  
  Fixpoint runC (acts : ActList P1) : ActList P2 :=
    match acts with
    | ActNil _ => ActNil P2
    | ActCons _ acts' a =>
      ActList_app P2 (runC acts') (c acts' a)
    end.

  Record SimR (R : Dist (Frag P1) -> Dist (Frag P2) -> Prop) :=
    {
      obs : (forall e1 e2, R e1 e2 -> (f <- e1; ret (traceOf P1 f)) ~~ (f <- e2; ret (traceOf P2 f)));
      startcond: (R (ret (FragStart _ (start P1))) (ret (FragStart _ (start  P2))));
      stepcond: 
    (forall gamma a, R (run P1 gamma) (run P2 (runC gamma)) -> R (appAction P1 a (run P1 gamma)) (appList P2 (run P2 (runC gamma)) (c gamma a)))}.
      
      
  Lemma simInd : forall R (xs : ActList P1) a, SimR R ->
                                   R (run P1 xs) (run P2 (runC xs)) ->
                                   R (run P1 (xs ::> a)) (run P2 ((runC xs) +++ (c xs a))).
    intros.
    rewrite run_cons.
    rewrite run_app.
    apply (stepcond _ H).
    auto.
  Qed.

  Lemma simInv : forall R (xs : ActList P1), SimR R -> R (run P1 xs) (run P2 (runC xs)).
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
  Context (P1 P2 : PIOA).

  
  Definition impl := forall (P : PIOA),
      refinement (compPIOA P1 P) (compPIOA P2 P).

End ImplPIOA.

Section CompImpl.
  Context (P1 P2 P3 : PIOA).

  Lemma implcomp :
    impl P1 P2 -> impl (compPIOA P1 P3) (compPIOA P2 P3).
    intros.
    unfold impl in *.
    intros.
    rewrite (assocRefL P1 P3 P).
    rewrite (H (compPIOA P3 P)).
    rewrite assocRefR.
    reflexivity.
  Qed.
End CompImpl.
  

End PIOARel.
    
