
Add LoadPath "~/fcf/src".
Require Import FCF.FCF.
Require Import CpdtTactics.
Require Import List.
Require Import Coq.Lists.ListSet.
Require Import SetLems.
Require Import Dist.

  Module Type LAB.
    Parameter (Lab : Set).
    Parameter (Lab_eq : eq_dec Lab).
  End LAB.
                       
Module PIOADef (L : LAB).  
  Global Instance eqd_lab : EqDec (L.Lab).
  apply dec_EqDec; apply L.Lab_eq.
  Defined.
  
  
Record PIOA {Q : Set} {I O H : set L.Lab} :=
mkPIOA {
    start : Q;
    trans : Q -> L.Lab -> option (Dist Q);
    disjoint : set_disjoint L.Lab_eq I O /\ set_disjoint L.Lab_eq I H /\ set_disjoint L.Lab_eq O H;
    input_enabled : forall q l, set_In l I -> exists c, trans q l = Some c
    }.

Definition action {Q : Set} {I O H} (P : @PIOA Q I O H) :=
  set_union L.Lab_eq I (set_union L.Lab_eq O H).

Definition ext_action {Q : Set} {I O H} (P : @PIOA Q I O H)  :=
  set_union L.Lab_eq I O.

Definition loc_action {Q : Set} {I O H} (P : @PIOA Q I O H)  :=
  set_union L.Lab_eq O H.

Section SecPIOA.
  Context {Q : Set}.
  Context {I O H : set L.Lab}.
  Context (P : @PIOA Q I O H).
  Context `{EqDec Q}.


  Definition enabled (a : L.Lab) (q : Q) :=
    exists c, trans P q a = Some c.
    
    Inductive Frag :=
    | FragStart : Q -> Frag 
    | FragStep : L.Lab -> Q -> Frag  -> Frag .

  Global Instance frag_eq : EqDec Frag.
  apply dec_EqDec; unfold eq_dec; decide equality; apply EqDec_dec; auto; try apply eqd_lab.
  Defined.


    Definition lastState (f : Frag) :=
    match f with
    | FragStart  q => q
    | FragStep _ q _ => q
    end.

    Fixpoint firstState (f : Frag) :=
      match f with
      | FragStart  q => q
      | FragStep _ _ f' => firstState f'
      end.


    Fixpoint wf_Frag (f : Frag) : Prop :=
    match f with
    | FragStart  _ => True
    | FragStep  a q f' =>
      (wf_Frag f') /\
      (exists c, trans P (lastState f') a = Some c /\ In q (getSupport c)) 
    end.

    Definition loc_lab := {x : L.Lab | set_In x (loc_action P)}.

    Inductive ActList :=
    | ActNil : ActList
    | ActCons : ActList -> loc_lab -> ActList.


    Fixpoint ActList_app (l1 l2 : ActList) :=
      match l2 with
      | ActNil => l1
      | ActCons l2' a =>
        ActCons (ActList_app l1 l2') a
      end.

    Definition appAction (a : loc_lab) (c : Comp Frag) : Comp Frag :=
      f <-$ c;
      match (trans P (lastState f) (proj1_sig a)) with
        | Some mu =>
            q <-$ mu;
            ret (FragStep (proj1_sig a) q f)
        | Nothing => ret f
      end.

    
    Fixpoint appList (c : Comp Frag) (acts : ActList) :=
      match acts with
      | ActNil => c
      | ActCons l a => appAction a (appList c l)
        end.


    Definition run (acts : ActList) := appList (ret (FragStart (start P))) acts.

    Lemma run_cons : forall a acts, run (ActCons acts a) = appAction a (run acts).
    unfold run.
    simpl.
    auto.
    Qed.


    Lemma run_app : forall acts acts', run (ActList_app acts acts') = appList (run acts) acts'.
      induction acts'.
      simpl; auto.
      simpl.
      rewrite <- IHacts'.
      rewrite run_cons.
      auto.
    Qed.
    
    Fixpoint traceOf (f : Frag) :=
      match f with
      | FragStart q => nil
      | FragStep a q f' =>
        if (set_In_dec (EqDec_dec _) a (ext_action P)) then a :: (traceOf f') else traceOf f'
      end.

End SecPIOA.            

    Notation "x ::> y" := (ActCons _ x y) (at level 90).
    Notation "x +++ y" := (ActList_app _ x y) (at level 50).

Class Compatible {Q1 Q2 : Set} {I1 I2 O1 O2 H1 H2 : set L.Lab} (P1 : @PIOA Q1 I1 O1 H1) (P2 : @PIOA Q2 I2 O2 H2) :=
  {
    disjoint_outs : set_disjoint L.Lab_eq O1 O2;
    disjoint_hiddens_l : set_disjoint L.Lab_eq H1 (action P2);
    disjoint_hiddens_r : set_disjoint L.Lab_eq H2 (action P1)
  }.
      
Section CompPIOA.

  Context {Q1 Q2 : Set}.
  Context `{EqDec Q1}.
  Context `{EqDec Q2}.
  Context {I1 I2 O1 O2 H1 H2 : set L.Lab}.
  Context (P1 : @PIOA Q1 I1 O1 H1).
  Context (P2 : @PIOA Q2 I2 O2 H2).

  Context `{Compatible _ _ _ _ _ _ _ _ P1 P2}.

  Definition comp_start := (start P1, start P2).


  Definition comp_ins  :=
    set_diff L.Lab_eq (set_union L.Lab_eq I1 I2) (set_union L.Lab_eq O1 O2).

  Definition comp_outs  :=
    set_union L.Lab_eq O1 O2.

  Definition comp_hiddens  := 
    set_union L.Lab_eq H1 H2.

  Definition comp_trans (p : (Q1 * Q2)) (l : L.Lab) : option (Comp (Q1 * Q2)) :=
    match (trans P1 (fst p) l, trans P2 (snd p) l) with
    | (None, None) => None
    | (Some mu1, None) => Some (
      x <-$ mu1;
      ret (x, snd p))
    | (None, Some mu2) => Some (
        x <-$ mu2;
        ret (fst p, x))
    | (Some mu1, Some mu2) => Some (
        x <-$ mu1;
        y <-$ mu2;
        ret (x,y))
    end.

  Definition compPIOA : @PIOA (Q1 * Q2) comp_ins comp_outs comp_hiddens.
  econstructor.
  apply comp_start.
  split.
  unfold action in *.
  unfold comp_ins, comp_outs.
  apply diff_disjoint.
  split.
  unfold comp_ins, comp_outs, comp_hiddens.
  (* routine lemmas about sets *)
  admit.
  admit.
  admit.
  intros.
  unfold comp_ins in H3.
  instantiate (1 := comp_trans).
  unfold comp_trans.
  destruct (set_In_dec L.Lab_eq l I1).
  destruct (input_enabled P1 (fst q) l s) as [ia1 ia2].
  rewrite ia2.
  destruct (trans P2 (snd q) l).
  exists (x <-$ ia1; y <-$ d; ret (x,y)); crush.
  exists (x <-$ ia1; ret (x, snd q)); crush.

  destruct (trans P1 (fst q) l).
  destruct (trans P2 (snd q) l).
  exists (x <-$ d; y <-$ d0; ret (x,y)); crush.
  exists (x <-$ d; ret (x, snd q)); crush.

  destruct (set_In_dec L.Lab_eq l I2).
  destruct (input_enabled P2 (snd q) l s) as [H6 H7].
  rewrite H7.
  exists (x <-$ H6; ret (fst q, x)); crush.
  unfold comp_ins in H4.
  apply set_diff_elim1 in H4.
  apply set_union_elim in H4.
  destruct H4; crush.
  Admitted.
  
End CompPIOA.

End PIOADef.