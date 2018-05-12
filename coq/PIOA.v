
Add LoadPath "~/fcf/src".
Add LoadPath "./Dist".
Require Import FCF.EqDec.
Require Import Dist.
Require Import CpdtTactics.
Require Import List.
Require Import Bool.
Require Import SetLems.

Section PIOADef.
  Context {Lab : Set}.
  Context `{eqLab : EqDec Lab}.
  
Record PIOA :=
mkPIOA {
    pQ : Set;
    pI : Lab -> bool;
    pO : Lab -> bool;
    pH : Lab -> bool;
    start : pQ;
    trans : pQ -> Lab -> option (Dist pQ);
    }.

Definition disjoint (f g : Lab -> bool) := forall x,
    (f x = true -> g x = false) /\
    (g x = true -> f x = false).

Definition pairwise_disjoint (f g h : Lab -> bool) := forall x,
    (f x = true -> (g x = false /\ h x = false)) /\
    (g x = true -> (h x = false /\ g x = false)) /\
    (h x = true -> (f x = false /\ f x = false)). 



Class wfPIOA (P : PIOA) :=
  {
    disjoint_labs : pairwise_disjoint (pI P) (pO P) (pH P);
    input_enabled : forall q l, (pI P) l = true -> exists c, (trans P) q l = Some c;
    trans_wf : forall q l c, ((trans P) q l = Some c ->
                              (pI P l = true \/ pO P l = true \/ pH P l = true)) /\
                             ((pI P l = false /\ pO P l = false /\ pH P l = false) -> trans P q l = None)
  }.




Definition action (P : PIOA) (l : Lab) :=
  (pI P l || pO P l) || pH P l.
  
Definition ext_action (P : PIOA) l :=
  pI P l || pO P l.

Definition loc_action (P : PIOA) l :=
  pO P l || pH P l.

Section SecPIOA.
  Context (P : PIOA).
  Context `{EqDec (pQ P)}.
    
    Inductive Frag :=
    | FragStart : pQ P -> Frag 
    | FragStep : Lab -> pQ P -> Frag  -> Frag .

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

    Definition loc_lab := {x : Lab | (loc_action P) x = true}.
    Definition act_lab := {x : Lab | (action P) x = true}.

    (* In the paper they use loc_lab below where I use act_lab. is this an important difference? *)
    
    (* the label only gets added to the frag if the process accepts it. *)
    Definition appAction (a : act_lab) (c : Dist Frag) : Dist Frag := 
      f <- c;
      match (trans P (lastState f) (proj1_sig a)) with
        | Some mu =>
            q <- mu;
            ret (FragStep (proj1_sig a) q f)
        | Nothing => ret f
      end.

    
    (* Earlier actions are applied later *)
    Fixpoint appList (c : Dist Frag) (acts : list (act_lab)) :=
      match acts with
      | nil => c
      | l :: acts' =>
        appAction l (appList c acts')
                  end.


    Definition run (acts : list act_lab) : Dist Frag := appList (ret (FragStart (start P))) acts.

    Lemma run_cons : forall a acts, run (a :: acts) = appAction a (run acts).
      unfold run; simpl; auto.
      Qed.


    Lemma run_app : forall acts acts', run (acts ++ acts') = appList (run acts') acts.
      induction acts; simpl.
      auto.
      intro.
      rewrite run_cons.
      rewrite IHacts.
      auto.
    Qed.
    
    Fixpoint traceOf (f : Frag) :=
      match f with
      | FragStart q => nil
      | FragStep a q f' =>
        if ((ext_action P) a) then a :: (traceOf f') else traceOf f'
      end.

End SecPIOA.            


Class Compatible (P1 P2 : PIOA) :=
  {
    disjoint_outs : disjoint (pO P1) (pO P2);
    disjoint_ins : disjoint (pI P1) (pI P2);
    disjoint_h_l : disjoint (pH P1) (action P2);
    disjoint_h_r : disjoint (pH P2) (action P1)
  }.

Class Comparable (P1 P2 : PIOA) :=
  {
    equal_ins : forall l, pI P1 l = pI P2 l;
    equal_outs : forall l, pO P1 l = pO P2 l;
    disjoint_hiddens_l : disjoint (pH P1) (action P2);
    disjoint_hiddens_r : disjoint (pH P2) (action P1);
    }.

Lemma compatible_comparable : forall P1 P2 P3,
    Compatible P1 P3 ->
    Comparable P1 P2 ->
    Compatible P2 P3.

Admitted.
                                        
    
      
Section CompPIOA.
  Context (P1 P2 : PIOA).
  Context `{Compatible P1 P2}.


  Definition comp_start := (start P1, start P2).

  Definition comp_ins l :=
    (pI P1 l || pI P2 l) && (negb (pO P1 l || pO P2 l)).
    
  Definition comp_outs l :=
    (pO P1 l || pO P2 l) && (negb (pI P1 l || pI P2 l)).


  Definition comp_hiddens l := 
    pH P1 l || pH P2 l || (pI P1 l && pO P2 l) || (pO P1 l && pI P2 l).

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

  Hint Rewrite negb_false_iff.
  Hint Rewrite negb_true_iff.
  Hint Rewrite negb_orb.
  Hint Rewrite negb_andb.
  Hint Rewrite negb_involutive.
  Hint Rewrite orb_false_elim.
  Hint Rewrite andb_true_iff.
  Hint Rewrite andb_false_iff.
  Hint Rewrite orb_true_iff.
  Hint Rewrite orb_false_iff.

  Ltac exists_some := match goal with
                      | [ |- exists c, Some ?b = Some c] => exists ?b
                      | [ |- exists c, Some c = Some ?b] => exists ?b
                      end.

                                    
  Instance compWf : forall (w1 : wfPIOA P1) (w2 : wfPIOA P2), wfPIOA compPIOA.
  econstructor.
  simpl.
  unfold pairwise_disjoint.
  intro x.
  destruct H; unfold disjoint in *.
  destruct w1 as [w1 _ _]; unfold pairwise_disjoint in w1; pose proof (w1 x); clear w1.
  destruct w2 as [w2 _ _]; unfold pairwise_disjoint in w2; pose proof (w2 x); clear w2.
  unfold comp_ins, comp_outs, comp_hiddens.
  admit.
  
  intros.
  destruct w1 as [_ w1 _].
  destruct w2 as [_ w2 _].
  simpl in H0.
  unfold comp_ins in H0.
  unfold trans; simpl.
  unfold comp_trans.
  
  rewrite andb_true_iff in H0; destruct H0.
  remember (pI P1 l) as b1.
  remember (pI P2 l) as b2.
  destruct b1; destruct b2; symmetry in Heqb1; symmetry in Heqb2.

  destruct (w1 (fst q) _ Heqb1).
  destruct (w2 (snd q) _ Heqb2).
  rewrite H2; rewrite H3; simpl.
  exists (x1 <- x; y <- x0; ret (x1, y)); crush.

  destruct (w1 (fst q) _ Heqb1).
  rewrite H2.
  destruct (trans P2 (snd q) l).
  exists (x0 <- x; y <- d; ret (x0, y)); crush.
  exists (x0 <- x; ret (x0, snd q)); crush.

  destruct (w2 (snd q) _ Heqb2).
  rewrite H2.
  destruct (trans P1 (fst q) l).
  exists (x0 <- d; y <- x; ret (x0, y)); crush.
  exists (x0 <- x; ret (fst q, x0)); crush.
  simpl in H0.
  crush.


  intros.
  destruct w1 as [wf1 ia1 w1].
  destruct w2 as [wf2 ia2 w2].
  destruct H.
  split; intros.
  simpl in H0.
  unfold comp_trans in H0.

  remember (trans P1 (fst q) l); symmetry in Heqo.
  destruct o.
  apply w1 in Heqo.
  destruct Heqo.
  remember (pO P2 l) as b; destruct b.
  right; right; simpl.
  unfold comp_hiddens.
  cut (pI P1 l && pO P2 l = true).
  intro HH; rewrite HH; crush.
  crush.
  left; simpl; unfold comp_ins.
  rewrite H1. rewrite <- Heqb.
  simpl.
  cut (pO P1 l = false).
  intro HH; crush.
  destruct (wf1 l).
  crush.
  destruct H1.
  remember (pI P2 l) as b; destruct b.
  right; right; simpl; unfold comp_hiddens.
  cut (pO P1 l && pI P2 l = true); crush.
  right; left; simpl; unfold comp_outs.
  rewrite H1. rewrite <- Heqb.
  simpl.
  destruct (wf1 l).
  cut (pI P1 l = false); crush.
  right; right; simpl; unfold comp_hiddens; rewrite H1; crush.

  remember (trans P2 (snd q) l); symmetry in Heqo0.
  destruct o.
  apply w2 in Heqo0.
  destruct Heqo0.
  remember (pO P1 l) as b; destruct b.
  right; right; simpl.
  unfold comp_hiddens.
  cut (pO P1 l && pI P2 l = true); crush.
  left; simpl; unfold comp_ins.

  rewrite H1; rewrite <- Heqb.
  rewrite orb_true_r.
  simpl.
  destruct (wf2 l).
  cut (pO P2 l = false); crush.
  destruct H1.
  remember (pI P1 l) as b; destruct b.
  right; right; simpl; unfold comp_hiddens; simpl.
  cut (pI P1 l && pO P2 l = true); crush.
  right; left; simpl; unfold comp_outs.
  rewrite H1; rewrite <- Heqb.
  rewrite orb_true_r.
  simpl.
  destruct (wf2 l); crush.
  right; right; simpl; unfold comp_hiddens; crush.
  crush.
  simpl; unfold comp_trans.
  destruct H0.
  destruct H1.
  simpl in *.
  unfold comp_ins, comp_outs, comp_hiddens in *.
  cut (trans P1 (fst q) l = None /\ trans P2 (snd q) l = None).
  crush.
  split.

  apply w1.
  apply (x <- c; ret (fst x)).
  split.
  remember (pI P1 l) as b; destruct b; symmetry in Heqb.
  remember (pO P2 l) as b2; destruct b2; symmetry in Heqb2.
  simpl in *.
  crush.
  simpl in *.
  remember (pO P1 l) as b3; destruct b3; symmetry in Heqb3.

  destruct (wf1 l); crush.
  simpl in *.
  crush.
  crush.
  split.

  remember (pO P1 l) as b; destruct b; symmetry in Heqb.
  remember (pO P2 l) as b2; destruct b2; symmetry in Heqb2.
  crush.
  simpl in *.
  remember (pI P1 l) as b3; destruct b3; symmetry in Heqb3.
  destruct (wf1 l); crush.
  crush.
  crush.
  destruct (pH P1 l).
  simpl in H2.
  crush.
  crush.
  
  apply w2.
  apply (x <- c; ret (snd x)).
  split.
  remember (pI P2 l) as b; destruct b; symmetry in Heqb.
  remember (pO P1 l) as b2; destruct b2; symmetry in Heqb2.
  simpl in *.
  crush.
  simpl in *.
  remember (pO P2 l) as b3; destruct b3; symmetry in Heqb3.

  destruct (wf2 l); crush.
  simpl in *.
  crush.
  crush.
  split.

  remember (pO P2 l) as b; destruct b; symmetry in Heqb.
  remember (pO P1 l) as b2; destruct b2; symmetry in Heqb2.
  crush.
  simpl in *.
  remember (pI P2 l) as b3; destruct b3; symmetry in Heqb3.
  destruct (wf2 l); crush.
  crush.
  crush.
  destruct (pH P2 l).
  simpl in H2.
  crush.
  crush.
  Admitted.
  
  
End CompPIOA.




End PIOADef.

Notation "x |+| y" := (@compPIOA _ x y) (at level 51, right associativity).