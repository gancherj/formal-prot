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


Module PIOARel (L : LAB).

  Module P := PIOADef L.
  Import P.
  Import L.

Section RefinePIOADef.
  Context {Q1 Q2 : Set}.
  Context `{EqDec Q1}.
  Context `{EqDec Q2}.
  Context {I1 I2 O1 O2 H1 H2 : set Lab}.
  Context (P1 : @PIOA Q1 I1 O1 H1).
  Context (P2 : @PIOA Q2 I2 O2 H2).

  Definition refinement := forall acts, exists acts',
        (f <- (run P1 acts); ret (traceOf P1 f)) ~~ (f <- (run P2 acts'); ret (traceOf P2 f)).


End RefinePIOADef.

(* Without convex combination. *)
Section SimPIOA.
  
  Context {Q1 Q2 : Set}.
  Context `{EqDec Q1}.
  Context `{EqDec Q2}.
  Context {I1 I2 O1 O2 H1 H2 : set L.Lab}.
  Context (P1 : @PIOA Q1 I1 O1 H1).
  Context (P2 : @PIOA Q2 I2 O2 H2).
  Context (c : ActList P1 -> loc_lab P1 -> ActList P2).

  
  Fixpoint runC (acts : ActList P1) : ActList P2 :=
    match acts with
    | ActNil _ => ActNil P2
    | ActCons _ acts' a =>
      ActList_app P2 (runC acts') (c acts' a)
    end.

  Record SimR (R : Dist (@Frag Q1) -> Dist (@Frag Q2) -> Prop) :=
    {
      obs : (forall e1 e2, R e1 e2 -> (f <- e1; ret (traceOf P1 f)) ~~ (f <- e2; ret (traceOf P2 f)));
      startcond: (R (ret (FragStart (start P1))) (ret (FragStart (start  P2))));
      stepcond: 
    (forall gamma a, R (run P1 gamma) (run P2 (runC gamma)) -> R (appAction P1 a (run P1 gamma)) (appList P2 (run P2 (runC gamma)) (c gamma a)))}.
      
      
  Lemma simInd : forall R (xs : ActList P1) a, SimR R ->
                                   R (run P1 xs) (run P2 (runC xs)) ->
                                   R (run P1 (xs ::> a)) (run P2 ((runC xs) +++ (c xs a))).
    intros.
    rewrite run_cons.
    rewrite run_app.
    apply (stepcond _ H3).
    auto.
  Qed.

  Lemma simInv : forall R (xs : ActList P1), SimR R -> R (run P1 xs) (run P2 (runC xs)).
    intros.
    induction xs.
    simpl.
    unfold run.
    unfold appList.
    apply (startcond _ H3).
    simpl.
    apply simInd.
    apply H3.
    auto.
  Qed.
  
  Lemma simSound : forall R, SimR R -> refinement P1 P2.
    intros.
    unfold refinement.
    intros; exists (runC acts).
    apply (obs _ H3).
    apply simInv.
    auto.
  Qed.

End SimPIOA.

Fixpoint Frag_fmap {A B : Set} (f : @Frag A) (g : A -> B) : @Frag B :=
  match f with
  | FragStart q => FragStart (g q)
  | FragStep l q f' => FragStep l (g q) (Frag_fmap f' g)
  end.


  Definition prodassoc {A B C} (e : (A * B) * C) :=
    match e with
    | ((a, b), c) => (a, (b, c))
    end.

Section RefineAssoc.
  Context {Q1 Q2 Q3 : Set}.
  Context `{EqDec Q1}.
  Context `{EqDec Q2}.
  Context `{EqDec Q3}.
  Context {I1 I2 I3 O1 O2 O3 Hi1 Hi2 Hi3 : set L.Lab}.
  Context (P1 : @PIOA Q1 I1 O1 Hi1).
  Context (P2 : @PIOA Q2 I2 O2 Hi2).
  Context (P3 : @PIOA Q3 I3 O3 Hi3).

  

  Context `{Compatible _ _ _ _ _ _ _ _ P1 P2}.
  Context `{Compatible _ _ _ _ _ _ _ _ P2 P3}.
  Context `{Compatible _ _ _ _ _ _ _ _ P1 (compPIOA P2 P3)}.
  Context `{Compatible _ _ _ _ _ _ _ _ (compPIOA P1 P2) P3}.


  Definition A1 := compPIOA P1 (compPIOA P2 P3).
  Definition A2 := compPIOA (compPIOA P1 P2) P3.
  
  Definition AssocR (e1 : Dist (@Frag (Q1 * (Q2 * Q3)))) (e2 : Dist (@Frag ((Q1 * Q2) * Q3))) :=
    e1 ~~ (f <- e2; ret (Frag_fmap f prodassoc)).

  Compute (disjoint A1).
  Check @comp_ins.


  Lemma corr11 : forall x, In x (Pins A1) <-> (In x I1 \/ In x I2 \/ In x I3) /\ (~ (In x O1 \/ In x O2 \/ In x O3)).
    unfold Pins.
    unfold comp_ins.
    unfold comp_outs.
    intros; split; intros.
    split.
    apply set_diff_iff in H6.
    destruct H6.
    apply set_union_elim in H6; destruct H6.
    crush.
    apply set_diff_iff in H6; destruct H6.
    apply set_union_elim in H6; crush.
    intro.
    apply set_diff_iff in H6; destruct H6.
    apply H8.
    destruct H7.
    apply set_union_intro; crush.
    destruct H7.
    apply set_union_intro; right; apply set_union_intro; crush.
    apply set_union_intro; right; apply set_union_intro; crush.
    destruct H6.
    apply set_diff_iff; split.
    destruct H6 as [H61 | [H62 | H63]].
    apply set_union_intro; crush.
    apply set_union_intro; right; apply set_diff_iff.
    split.
    apply set_union_intro; crush.
    intro.
    apply H7.
    apply set_union_elim in H6.
    crush.
    apply set_union_intro; right; apply set_diff_iff; split.
    apply set_union_intro; crush.
    intro.
    apply H7.
    apply set_union_elim in H6; crush.
    intro.
    apply H7.
    apply set_union_elim in H8; destruct H8.
    crush.
    apply set_union_elim in H8; destruct H8.
    crush.
    crush.
 Qed.
    
  Lemma corr12 : forall x, In x (Pins A2) <-> (In x I1 \/ In x I2 \/ In x I3) /\ (~ (In x O1 \/ In x O2 \/ In x O3)).
    unfold Pins.
    unfold comp_ins.
    unfold comp_outs.
    intros; split; intros.
    split.
    apply set_diff_iff in H6.
    destruct H6.
    apply set_union_elim in H6; destruct H6.
    apply set_diff_iff in H6; destruct H6.
    apply set_union_elim in H6; crush.
    crush.
    intro.
    apply set_diff_iff in H6; destruct H6.
    apply H8.
    destruct H7.
    apply set_union_intro; left; apply set_union_intro; crush.
    destruct H7.
    apply set_union_intro; left; apply set_union_intro; crush.
    apply set_union_intro; right; crush.
    destruct H6.
    apply set_diff_iff; split.
    destruct H6 as [H61 | [H62 | H63]].
    apply set_union_intro; left; apply set_diff_iff.
    split.
    apply set_union_intro; left; crush.
    intro; apply H7.
    apply set_union_elim in H6; crush.
    apply set_union_intro; left; apply set_diff_iff; split.
    apply set_union_intro; crush.
    intro; apply H7.
    apply set_union_elim in H6; crush.
    apply set_union_intro; right; crush.
    intro; apply H7.
    apply set_union_elim in H8.
    destruct H8.
    apply set_union_elim in H8; crush.
    crush.
  Qed.

  Lemma corr1 : set_eq (Pins A1) (Pins A2).
    unfold set_eq.
    intros.
    rewrite corr11.
    rewrite corr12.
    crush.
  Qed.

  Lemma corr2 : set_eq (Pouts A1) (Pouts A2).
    unfold Pouts.
    unfold comp_outs.
    unfold set_eq; intros; split; intros; apply set_union_assoc; crush.
  Qed.

  Lemma corr3 : set_eq (Phidden A1) (Phidden A2).
    unfold Phidden.
    unfold comp_hiddens.
    unfold set_eq; intros; split; intros; apply set_union_assoc; crush.
  Qed.
    

  Lemma loc_corr : set_eq (loc_action A1) (loc_action A2).
    unfold set_eq.
    unfold loc_action.
    intros; split; intros.
    unfold comp_outs in *.
    unfold comp_hiddens in *.
    apply set_union_elim in H6.
    destruct H6.
    apply corr2 in H6.
    apply set_union_intro; left.
    auto.
    apply set_union_intro; right.
    apply corr3; crush.
    unfold comp_outs, comp_hiddens in *.
    apply set_union_elim in H6; destruct H6.
    apply set_union_intro; left; apply corr2; crush.
    apply set_union_intro; right; apply corr3; crush.
 Qed.



  Lemma ext_action_corr : set_eq (ext_action A1) (ext_action A2).
  unfold set_eq, ext_action.
  intros; unfold comp_ins, comp_outs; split.
  intros.
  apply set_union_elim in H6; destruct H6.
  apply corr1 in H6.
  apply set_union_intro; left; auto.
  apply set_union_intro; right; apply corr2; auto.
  intros.
  apply set_union_elim in H6; destruct H6.
  apply corr1 in H6.
  apply set_union_intro; left; auto.
  apply set_union_intro; right; apply corr2; auto.
  Qed.


  Definition corr_act (l : loc_lab A1) : loc_lab A2.
  destruct l.
  unfold loc_lab in *.
  econstructor.
  apply loc_corr in s.
  apply s.
  Defined.

  Fixpoint corr_actlist (a : ActList A1) : ActList A2 :=
    match a with
      | ActNil _ => ActNil A2
      | ActCons _ f a => ActCons A2 (corr_actlist f) (corr_act a)
    end.

  Definition corr (xs : ActList (compPIOA P1 (compPIOA P2 P3))) (a : loc_lab (compPIOA P1 (compPIOA P2 P3))) := ActCons (compPIOA (compPIOA P1 P2) P3) (ActNil _) (corr_act a).

  Lemma corr_act_R : forall (e1 : Dist (@Frag (Q1 * (Q2 * Q3)))) (e2 : Dist (@Frag ((Q1 * Q2) * Q3))) a,
      AssocR e1 e2 -> AssocR (appAction A1 a e1) (appAction A2 (corr_act a) e2).
  intros.
  unfold AssocR in *.
  unfold appAction.
  rewrite bindAssoc.
  rewrite (distBind_cong_l _ _ _ H6).
  rewrite bindAssoc.
  apply distBind_cong_r.
  intros.
  rewrite bind_ret.
  simpl.
  unfold comp_trans.
  simpl.
  unfold comp_trans.
  simpl.
  assert (trans P1 (fst (lastState (Frag_fmap x prodassoc))) (proj1_sig a) = 
trans P1 (fst (fst (lastState x))) (proj1_sig (corr_act a))).
  induction x.
  destruct q as [[q1 q2] q3].
  destruct a.
  unfold prodassoc, corr_act.
  simpl.
  auto.
  simpl.
  destruct q as [[q1 q2] q3].
  unfold prodassoc, corr_act.
  destruct a.
  simpl.
  auto.

  assert (trans P2 (fst (snd (lastState (Frag_fmap x prodassoc)))) (proj1_sig a) =
          trans P2 (snd (fst (lastState x))) (proj1_sig (corr_act a))).
  induction x.
  destruct q as [[q1 q2] q3].
  destruct a.
  unfold prodassoc, corr_act.
  simpl.
  auto.
  simpl.
  destruct q as [[q1 q2] q3].
  unfold prodassoc, corr_act.
  destruct a.
  simpl.
  auto.

  assert (trans P3 (snd (snd (lastState (Frag_fmap x prodassoc)))) (proj1_sig a) =
trans P3 (snd (lastState x)) (proj1_sig (corr_act a))).
  induction x.
  destruct q as [[q1 q2] q3].
  destruct a.
  unfold prodassoc, corr_act.
  simpl.
  auto.
  simpl.
  destruct q as [[q1 q2] q3].
  unfold prodassoc, corr_act.
  destruct a.
  simpl.
  auto.

  rewrite H8, H9, H10.
  clear H8 H9 H10.
  destruct (trans P1 (fst (fst (lastState x))) (proj1_sig (corr_act a))).
  destruct ( trans P2 (snd (fst (lastState x))) (proj1_sig (corr_act a))).
  destruct ( trans P3 (snd (lastState x)) (proj1_sig (corr_act a))).
  Ltac dsimp := try apply distBind_cong_r; intros; repeat rewrite bindAssoc; try rewrite bind_ret.
  repeat dsimp.
  destruct a; simpl; unfold distEquiv; crush.
  repeat dsimp.
  destruct a; simpl.
  induction x.
  destruct q as [[q1 q2] q3]; simpl.
  simpl.
  unfold distEquiv; crush.
  destruct q as [[q1 q2] q3].
  simpl.
  unfold distEquiv; crush.
  destruct ( trans P3 (snd (lastState x)) (proj1_sig (corr_act a))).
  repeat dsimp.
  repeat dsimp; induction x; destruct q as [[q1 q2] q3]; destruct a; simpl; unfold distEquiv; crush.
  repeat dsimp.
  induction x; destruct q as [[q1 q2] q3]; destruct a; simpl; unfold distEquiv; crush.
  destruct ( trans P2 (snd (fst (lastState x))) (proj1_sig (corr_act a))).
  destruct ( trans P3 (snd (lastState x)) (proj1_sig (corr_act a))).
  repeat dsimp; induction x; destruct q as [[q1 q2] q3]; destruct a; simpl; unfold distEquiv; crush.
  repeat dsimp; induction x; destruct q as [[q1 q2] q3]; destruct a; simpl; unfold distEquiv; crush.
  destruct ( trans P3 (snd (lastState x)) (proj1_sig (corr_act a))).
  repeat dsimp; induction x; destruct q as [[q1 q2] q3]; destruct a; simpl; unfold distEquiv; crush.
  rewrite bind_ret.
  unfold distEquiv; crush.

  Qed.

  Lemma corr_act_list : forall gamma a,
      AssocR (run A1 gamma) (run A2 (runC A1 A2 corr gamma)) ->
  AssocR (appAction A1 a (run A1 gamma))
    (appList A2 (run A2 (runC A1 A2 corr gamma)) (corr gamma a)).

  intros.

  apply corr_act_R.
  auto.
  Qed.

  Definition SimAssocR: SimR A1 A2 corr AssocR.
    assert (forall x, traceOf A1 (Frag_fmap x prodassoc) = traceOf A2 x).
    intros.
    induction x.
    crush.
    simpl.
    destruct (set_In_dec (EqDec_dec eqd_lab) l (ext_action A1)).
    destruct (set_In_dec (EqDec_dec eqd_lab) l (ext_action A2)).
    rewrite IHx; crush.
    apply ext_action_corr in s; crush.
    destruct (set_In_dec (EqDec_dec eqd_lab) l (ext_action A2)).
    apply ext_action_corr in s; crush.
    apply IHx.

    econstructor.
    intros.
    unfold AssocR in H7.
    rewrite (distBind_cong_l _ _ _ H7).
    rewrite bindAssoc.
    apply distBind_cong_r; intros.
    rewrite bind_ret.
    rewrite H6.
    unfold distEquiv; crush.
    unfold AssocR.
    rewrite bind_ret.
    unfold distEquiv.
    intro.
    simpl.
    unfold distRet.
    unfold integ.
    rewrite sumList_cons.
    rewrite sumList_cons.
    unfold sumList; simpl.
    unfold comp_start.
    unfold start.
    unfold compPIOA.
    unfold comp_start.
    clear H6.
    clear H5.
    destruct P1.
    destruct P2.
    destruct P3.
    crush.

    
    intros.
    apply corr_act_list.
    auto.
    Qed.
    
  Lemma implassoc : refinement (compPIOA P1 (compPIOA P2 P3)) (compPIOA (compPIOA P1 P2) P3).
    eapply simSound.
    apply SimAssocR.
  Qed.

End RefineAssoc.

    
Section ImplPIOA.
  Context {Q1 Q2 : Set}.
  Context `{EqDec Q1}.
  Context `{EqDec Q2}.
  Context {I O H1 H2 : set L.Lab}.
  Context (P1 : @PIOA Q1 I O H1).
  Context (P2 : @PIOA Q2 I O H2).
  
  Definition impl := forall QE IE OE HE (E : @PIOA QE IE OE HE) {eqQe : EqDec QE}
      `{Compatible _ _ _ _ _ _ _ _ P1 E}
      `{Compatible _ _ _ _ _ _ _ _ P2 E},
                            
      refinement (compPIOA P1 E) (compPIOA P2 E).


End ImplPIOA.


Section CompImpl.
  Context {Q1 Q2 Q3 : Set}.
  Context `{EqDec Q1}.
  Context `{EqDec Q2}.
  Context `{EqDec Q3}.
  Context {I I3 O O3 Hid1 Hid2 Hid3 : set L.Lab}.
  Context (P1 : @PIOA Q1 I O Hid1).
  Context (P2 : @PIOA Q2 I O Hid2).
  Context (P3 : @PIOA Q3 I3 O3 Hid3).
  Context `{Compatible _ _ _ _ _ _ _ _ P1 P3}.
  Context `{Compatible _ _ _ _ _ _ _ _ P2 P3}.
  

  Lemma implcomp :
    impl P1 P2 -> impl (compPIOA P1 P3) (compPIOA P2 P3).
    admit.
  Admitted.
End CompImpl.
  

Section RefinePIOAEx.
  Context {Q1 Q2 Q3 : Set}.
  Context `{EqDec Q1}.
  Context `{EqDec Q2}.
  Context {eqQ3 : EqDec Q3}.
  Context {I1 I2 O1 O2 H1 H2 I3 O3 H3 : set L.Lab}.
  Context (P1 : @PIOA Q1 I1 O1 H1).
  Context (P2 : @PIOA Q2 I2 O2 H2).
  Context (P3 : @PIOA Q3 I3 O3 H3).
  
  Lemma refinement_refl : refinement P1 P1.
    unfold refinement.
    intros a; exists a.
    unfold distEquiv; crush.
  Qed.

  Lemma refinement_trans : refinement P1 P2 -> refinement P2 P3 -> refinement P1 P3.
    intros.
    unfold refinement in *.
    intros.
    destruct (H4 acts).
    destruct (H5 x).
    exists x0.
    rewrite H6.
    apply H7.
  Qed.

End RefinePIOAEx.

End PIOARel.
    
