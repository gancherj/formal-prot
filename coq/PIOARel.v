(* Change from Comp to finitely supported distribution, carried by a list of pairs *)

Add LoadPath "~/fcf/src".
Require Import FCF.FCF.
Require Import CpdtTactics.
Require Import List.
Require Import Coq.Lists.ListSet.
Require Import SetLems.
Require Import Dist.
Require Import PIOA.

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
        (comp_fmap (run P1 acts) (traceOf P1)) ~~ (comp_fmap (run P2 acts') (traceOf P2)).

End RefinePIOADef.

(* Without convex combination. *)
Section SimPIOA.
  Definition fragConsistent {Q : Set} `{EqDec Q} {I O H} (P : @PIOA Q I O H) (eps : Comp (@Frag Q)) (l : ActList P) := forall x, In x (getSupport eps) -> In x (getSupport (run P l)).
  
  Context {Q1 Q2 : Set}.
  Context `{EqDec Q1}.
  Context `{EqDec Q2}.
  Context {I1 I2 O1 O2 H1 H2 : set L.Lab}.
  Context (P1 : @PIOA Q1 I1 O1 H1).
  Context (P2 : @PIOA Q2 I2 O2 H2).
  Context (c : ActList P1 -> loc_lab P1 -> ActList P2).

  Print ActList.
  
  Fixpoint runC (acts : ActList P1) : ActList P2 :=
    match acts with
    | ActNil _ => ActNil P2
    | ActCons _ acts' a =>
      ActList_app P2 (runC acts') (c acts' a)
    end.

  Record SimR (R : Comp (@Frag Q1) -> Comp (@Frag Q2) -> Prop) :=
    {
      obs : (forall e1 e2, R e1 e2 -> comp_fmap e1 (traceOf P1) ~~ comp_fmap e2 (traceOf P2));
      startcond: (R (ret (FragStart (start P1))) (ret (FragStart (start  P2))));
      stepcond: 
    (forall e1 e2 gamma a, R e1 e2 -> fragConsistent P1 e1 gamma -> fragConsistent P2 e2 (runC gamma) -> R (appAction P1 a e1) (appList P2 e2 (c gamma a)))}.
      
      
  Lemma simInd : forall R (xs : ActList P1) a, SimR R ->
                                   R (run P1 xs) (run P2 (runC xs)) ->
                                   R (run P1 (xs ::> a)) (run P2 ((runC xs) +++ (c xs a))).
    intros.
    rewrite run_cons.
    rewrite run_app.
    apply (stepcond _ H3).
    auto.
    unfold fragConsistent; auto.
    unfold fragConsistent; auto.
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
  
  Definition AssocR (e1 : Comp (@Frag (Q1 * (Q2 * Q3)))) (e2 : Comp (@Frag ((Q1 * Q2) * Q3))) :=
    e1 ~~ (comp_fmap e2 (fun f => Frag_fmap f prodassoc)).

  Check loc_lab.

  Definition corr_act (l : loc_lab A1) : loc_lab A2.
  destruct l.
  econstructor.
  cut (set_eq (loc_action A1) (loc_action A2)).
  intros.
  unfold set_eq in H6.
  apply H6.
  apply s.

  unfold A1, A2, loc_action. 
  unfold comp_outs.
  unfold comp_hiddens.
  admit.

  (* routine set computation *)
  Admitted.

  Fixpoint corr_actlist (a : ActList A1) : ActList A2 :=
    match a with
      | ActNil _ => ActNil A2
      | ActCons _ f a => ActCons A2 (corr_actlist f) (corr_act a)
    end.

  Definition corr (xs : ActList (compPIOA P1 (compPIOA P2 P3))) (a : loc_lab (compPIOA P1 (compPIOA P2 P3))) := ActCons (compPIOA (compPIOA P1 P2) P3) (corr_actlist xs) (corr_act a).

  Check SimR.
  
  Definition SimAssocR: SimR A1 A2 corr AssocR.
    econstructor.
    intros.
    unfold AssocR in H6.
    rewrite (comp_fmap_cong _ _ _ H6).
    unfold comp_fmap.
    comp_inline leftc.
    comp_skip.
    induction x0.
    simpl.
    reflexivity.
    simpl.
    admit.

    unfold AssocR.
    simpl.
    unfold sumList.
    simpl.
    intros.
    destruct (EqDec_dec frag_eq (FragStart (start A2)) (FragStart (start A2))).    
    destruct (EqDec_dec frag_eq (FragStart (start A1)) x).    
    destruct (EqDec_dec frag_eq (FragStart (prodassoc (start A2))) x).
    rewrite <- ratAdd_0_l.
    rewrite ratMult_1_r.
    reflexivity.
    admit. (* this is a contradiction I cannot prove until I fix compPIOA *)
    destruct (EqDec_dec frag_eq (FragStart (prodassoc (start A2))) x).
    admit.
    rewrite <- ratAdd_0_l.
    rewrite ratMult_0_r.
    reflexivity.
    contradiction.

    intros.
    induction gamma.
    simpl.
    admit.
    (* Is this provable? *)
    admit.
Admitted.


  Lemma implassoc : refinement (compPIOA P1 (compPIOA P2 P3)) (compPIOA (compPIOA P1 P2) P3).
    eapply simSound.
    econstructor.
    instantiate (1 := AssocR).
    intros.
    unfold AssocR in H6.
    
    admit.
    Admitted.
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
    crush.
  Qed.

  Lemma refinement_trans : refinement P1 P2 -> refinement P2 P3 -> refinement P1 P3.
    intros.
    unfold refinement in *.
    intros.
    destruct (H4 acts).
    destruct (H5 x).
    exists x0.
    crush.
  Qed.

End RefinePIOAEx.

End PIOARel.
    
