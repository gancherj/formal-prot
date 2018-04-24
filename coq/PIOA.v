
Add LoadPath "~/fcf/src".
Add LoadPath "./Dist".
Require Import FCF.EqDec.
Require Import Dist.
Require Import CpdtTactics.
Require Import List.
Require Import Coq.Lists.ListSet.
Require Import SetLems.

  Module Type LAB.
    Parameter (Lab : Set).
    Parameter (Lab_eq : eq_dec Lab).
  End LAB.
                       
Module PIOADef (L : LAB).  

  Global Instance eqd_lab : EqDec (L.Lab).
  apply dec_EqDec; apply L.Lab_eq.
  Defined.
  
  
Record PIOA :=
mkPIOA {
    pQ : Set;
    pI : set L.Lab;
    pO : set L.Lab;
    pH : set L.Lab;
    start : pQ;
    trans : pQ -> L.Lab -> option (Dist pQ);
    }.

Class wfPIOA (P : PIOA) :=
  {
    disjoint : set_pairwise_disjoint L.Lab_eq ((pI P) :: (pO P) :: (pH P) :: nil);
    input_enabled : forall q l, set_In l (pI P) -> exists c, (trans P) q l = Some c;
    trans_wf : forall q l c, (trans P) q l = Some c ->
                             (set_In l (pI P) \/ set_In l (pO P) \/ set_In l (pH P))
  }.


Definition action (P : PIOA) :=
  set_union L.Lab_eq (pI P) (set_union L.Lab_eq (pO P) (pH P)).

Definition ext_action (P : PIOA) :=
  set_union L.Lab_eq (pI P) (pO P).

Definition loc_action (P : PIOA) :=
  set_union L.Lab_eq (pO P) (pH P).

Section SecPIOA.
  Context (P : PIOA).
  Context `{EqDec (pQ P)}.
    
    Inductive Frag :=
    | FragStart : pQ P -> Frag 
    | FragStep : L.Lab -> pQ P -> Frag  -> Frag .

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
      (exists c, trans P (lastState f') a = Some c /\ In q (distSupport c)) 
    end.

    Definition loc_lab := {x : L.Lab | set_In x (loc_action P)}.
    Definition act_lab := {x : L.Lab | set_In x (action P)}.

    
    (* NOTE: these correspond to the task schedules. Here I am allowing for input actions to also be included. (In the paper, only locally controlled actions are considered.) This I believe will allow for compositional reasoning. I think this is a safe generalization. *)
    Inductive ActList :=
    | ActNil : ActList
    | ActCons : ActList -> act_lab -> ActList.


    Fixpoint ActList_app (l1 l2 : ActList) :=
      match l2 with
      | ActNil => l1
      | ActCons l2' a =>
        ActCons (ActList_app l1 l2') a
      end.

    Definition appAction (a : act_lab) (c : Dist Frag) : Dist Frag := 
      f <- c;
      match (trans P (lastState f) (proj1_sig a)) with
        | Some mu =>
            q <- mu;
            ret (FragStep (proj1_sig a) q f)
        | Nothing => ret f
      end.

    
    Fixpoint appList (c : Dist Frag) (acts : ActList) :=
      match acts with
      | ActNil => c
      | ActCons l a => appAction a (appList c l)
        end.


    Definition run (acts : ActList) := appList (ret (FragStart (start P))) acts.

    Lemma run_cons : forall a acts, run (ActCons acts a) = appAction a (run acts).
      unfold run; simpl; auto.
      Qed.


    Lemma run_app : forall acts acts', run (ActList_app acts acts') = appList (run acts) acts'.
      induction acts'; [simpl; auto |
                        simpl; rewrite <- IHacts'; rewrite run_cons; auto].
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

Class Compatible (P1 P2 : PIOA) :=
  {
    disjoint_outs : set_disjoint L.Lab_eq (pO P1) (pO P2);
    disjoint_h_l : set_disjoint L.Lab_eq (pH P1) (action P2);
    disjoint_h_r : set_disjoint L.Lab_eq (pH P2) (action P1)
                                }.

                                        
    
      
Section CompPIOA.
  Context (P1 P2 : PIOA).
  Context `{Compatible P1 P2}.


  Definition comp_start := (start P1, start P2).

  Definition comp_ins  :=
    set_diff L.Lab_eq (set_union L.Lab_eq (pI P1) (pI P2)) (set_union L.Lab_eq (pO P1) (pO P2)).

  Definition comp_outs  :=
    set_union L.Lab_eq (pO P1) (pO P2).

  Definition comp_hiddens  := 
    set_union L.Lab_eq (pH P1) (pH P2).

  Definition comp_trans p l :=
    match (trans P1 (fst p) l, trans P2 (snd p) l) with
    | (None, None) => None
    | (Some mu1, None) => Some (
      x <- mu1;
      ret (x, snd p))
    | (None, Some mu2) => Some (
        x <- mu2;
        ret (fst p, x))
    | (Some mu1, Some mu2) => Some (
        x <- mu1; 
        y <- mu2; 
        ret (x,y))
    end.

  Definition compPIOA : PIOA :=
    mkPIOA ((pQ P1) * (pQ P2)) comp_ins comp_outs comp_hiddens comp_start comp_trans.

                                    
  Instance compWf : forall (w1 : wfPIOA P1) (w2 : wfPIOA P2), wfPIOA compPIOA.
  econstructor.
  simpl.
  unfold set_pairwise_disjoint.
  unfold allpairs.
  simpl.
  repeat split.
  unfold comp_ins, comp_outs.
  intro; intro.
  apply set_inter_elim in H0.
  rewrite set_diff_iff in H0; destruct H0.
  destruct H0.
  crush.

  unfold comp_ins, comp_hiddens.
  intro; intro.
  apply set_inter_elim in H0.
  rewrite set_diff_iff in H0; destruct H0.
  destruct H0.
  apply set_union_elim in H0.
  apply set_union_elim in H1.
  destruct H0; destruct H1.

  destruct w1 as [w _ _].
  unfold set_pairwise_disjoint in w.
  unfold allpairs in w; simpl in w.
  destruct w.
  destruct H3.
  apply (H5 x).
  apply set_inter_intro; crush.

  destruct H as [_ _ cH].
  apply (cH x).
  apply set_inter_intro. 
  crush.
  unfold action.
  apply set_union_intro; left; crush.

  destruct H as [_ cH _].
  apply (cH x).
  apply set_inter_intro. 
  crush.
  unfold action.
  apply set_union_intro; left; crush.

  destruct w2 as [w _ _].
  unfold set_pairwise_disjoint in w.
  unfold allpairs in w; simpl in w.
  destruct w.
  destruct H3.
  apply (H5 x).
  apply set_inter_intro; crush.

  unfold comp_outs, comp_hiddens.
  unfold set_disjoint; intro; intro.
  apply set_inter_elim in H0; destruct H0.

  apply set_union_elim in H0.
  apply set_union_elim in H1.
  destruct H0; destruct H1.

  destruct w1 as [w _ _].
  unfold set_pairwise_disjoint in w.
  unfold allpairs in w; simpl in w.
  destruct w.
  apply (H3 x).
  apply set_inter_intro; crush.
  
  destruct H as [_ _ cH].
  apply (cH x).
  apply set_inter_intro. 
  crush.
  unfold action.
  apply set_union_intro; right; apply set_union_intro; crush.

  destruct H as [_ cH _].
  apply (cH x).
  apply set_inter_intro. 
  crush.
  unfold action.
  apply set_union_intro; right; apply set_union_intro; crush.


  destruct w2 as [w _ _].
  unfold set_pairwise_disjoint in w.
  unfold allpairs in w; simpl in w.
  destruct w.
  apply (H3 x).
  apply set_inter_intro; crush.

  intros.
  simpl in H0.
  unfold comp_ins in H0.
  simpl.

  unfold comp_trans.
  destruct (set_In_dec L.Lab_eq l (pI P1)).
  simpl in q.
  destruct (input_enabled (fst q) l s) as [ia1 ia2].
  rewrite ia2.
  destruct (trans P2 (snd q) l).
  exists (x <- ia1; y <- d; ret (x,y)); crush.
  exists (x <- ia1; ret (x, snd q)); crush.

  destruct (trans P1 (fst q) l).
  destruct (trans P2 (snd q) l).
  exists (x <- d; y <- d0; ret (x,y)); crush.
  exists (x <- d; ret (x, snd q)); crush.

  destruct (set_In_dec L.Lab_eq l (pI P2)).
  destruct (input_enabled (snd q) l s) as [H6 H7].
  rewrite H7.
  exists (x <- H6; ret (fst q, x)); crush.
  apply set_diff_elim1 in H0.
  apply set_union_elim in H0.
  destruct H0; crush.

  intros.
  simpl.
  simpl in H0.
  unfold comp_trans in H0.
  remember (trans P1 (fst q) l).
  remember (trans P2 (snd q) l).
  symmetry in Heqo; symmetry in Heqo0.
  destruct o.
  destruct w1 as [w11 w12 w13].
  destruct (w13 _ _ _ Heqo).

  destruct o0.
  destruct w2 as [w21 w22 w23].
  destruct (w23 _ _ _ Heqo0).
  left; unfold comp_ins.
  rewrite set_diff_iff.
  split.
  apply set_union_intro; crush.
  intro.
  apply set_union_elim in H3; destruct H3.

  unfold set_pairwise_disjoint, allpairs in w11; simpl in w11.
  destruct w11.
  destruct H4.
  destruct H4.
  apply (H7 l).
  apply set_inter_intro; crush.

  unfold set_pairwise_disjoint, allpairs in w21; simpl in w21.
  destruct w21.
  destruct H4.
  destruct H4.
  apply (H7 l).
  apply set_inter_intro; crush.

  destruct H2.
  right; left; unfold comp_outs; apply set_union_intro; crush.
  right; right; unfold comp_outs; apply set_union_intro; crush.

  destruct (set_In_dec L.Lab_eq l (pO P2)).
  right; left; unfold comp_outs; apply set_union_intro; crush.
  left; unfold comp_ins.
  apply set_diff_iff; split.
  apply set_union_intro; crush.
  intro.
  apply set_union_elim in H2; destruct H2.

  unfold set_pairwise_disjoint, allpairs in w11; simpl in w11.
  destruct w11 as [[[_ w] _] _].
  apply (w l).
  apply set_inter_intro; crush.
  crush.

  destruct H1.
  right; left; unfold comp_outs; apply set_union_intro; crush.
  right; right; unfold comp_hiddens; apply set_union_intro; crush.

  destruct o0.
  destruct w2.
  destruct (trans_wf0 _ _ _ Heqo0).
  destruct (set_In_dec L.Lab_eq l (pO P1)).
  right; left; unfold comp_outs; apply set_union_intro; crush.
  left; unfold comp_ins; apply set_diff_iff; split.
  apply set_union_intro; crush.
  intro.
  apply set_union_elim in H2.
  destruct H2.
  crush.

  unfold set_pairwise_disjoint, allpairs in disjoint0; simpl in disjoint0.
  destruct disjoint0.
  destruct H3.
  destruct H3.
  apply (H6 l).
  apply set_inter_intro; crush.

  destruct H1.
  right; left; unfold comp_outs; apply set_union_intro; crush.
  right; right; unfold comp_outs; apply set_union_intro; crush.
  crush.
  Defined.
End CompPIOA.



Notation "x ||| y" := (compPIOA x y) (at level 51, right associativity).

End PIOADef.