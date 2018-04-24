
Add LoadPath "~/fcf/src".
Add LoadPath "./Dist".
Require Import CpdtTactics.
Require Import List.
Require Import FCF.Rat.
Require Import FCF.Fold.

Require Import Coq.Lists.ListSet.
Require Import SetLems.
Require Import PIOA.
Require Import PIOARel.
Require Import Dist.
Require Import DistRel.
Require Import Program.
Require Import FCF.EqDec.

Inductive LabI : Set :=
  | Recv : LabI
  | Send : bool -> LabI.
Module Labs : PIOA.LAB with Definition Lab := LabI.
  Definition Lab := LabI.
  Lemma Lab_eq : eq_dec Lab.
    unfold eq_dec.
    decide equality.
    apply EqDec_dec; crush. 
  Qed.
End Labs.
Print Labs.Lab.

Module P := PIOADef Labs.
Module R := PIOARel.PIOARel Labs.
Import R.
Import Labs.

Definition tst_trans (n : option bool) (l : Labs.Lab) :=
  match n, l with
  | None, Recv =>
    Some (x <- ((1/2, true) :: (1/2, false) :: nil); ret (Some x))
  | Some m, Recv => Some (ret (Some m))
  | Some m, Send m' =>
    if eqb m m' then Some (ret (Some m)) else None
  | None, Send _ => None
  end.
    
Definition tst :=
  P.mkPIOA (option bool) (Recv :: nil) (map Send (true :: false :: nil)) nil None tst_trans.

Definition tst2_trans (n : option bool) (l : Labs.Lab) :=
  match n, l with
  | None, Recv =>
    Some (x <- ((1/2, true) :: (1/2, false) :: nil); ret (Some x))
  | Some m, Recv => Some (ret (Some m))
  | Some m, Send m' =>
    if eqb m (negb m') then Some (ret (Some m)) else None
  | None, Send _ => None
  end.

Definition tst2 :=
  P.mkPIOA (option bool) (Recv :: nil) (map Send (true :: false :: nil)) nil None tst2_trans.

Check simpl_impl.
Lemma impltst : impl tst tst2.
  eapply simpl_impl.
  crush.
  crush.
  crush.

  instantiate (1 := fun s => match s with
                             | Some b => Some (negb b)
                             | None => None
                             end).
  crush.
  simpl.
  unfold option_lift; simpl.
  intros.
  induction l; induction s.
  simpl.
  right.
  exists (ret Some a).
  exists (ret Some (negb a)).
  crush.
  rewrite bind_ret.
  unfold distEquiv; crush.
  simpl.
  right.
  exists ((x <- [(1 / 2, true); (1 / 2, false)]; ret Some x)).
  exists ((x <- [(1 / 2, true); (1 / 2, false)]; ret Some x)).
  crush.
  rewrite bindAssoc.
  unfold distBind; simpl.
  unfold distJoin; simpl.
  unfold distEquiv; crush.
  unfold integ.
  repeat rewrite sumList_cons; simpl.
  unfold sumList; simpl.
  repeat rewrite ratMult_1_r.
  repeat rewrite <- ratAdd_0_r.
  rewrite ratAdd_comm.
  reflexivity.

  simpl.
  assert (eqb a b = eqb (negb a) (negb b)).
  remember (eqb (negb a) (negb b)) as h; destruct h.
  symmetry in Heqh; rewrite eqb_leibniz in Heqh.
  apply eqb_leibniz.
  induction a,b; crush.
  symmetry in Heqh; rewrite eqb_false_iff in Heqh.
  apply eqb_false_iff.
  induction a,b; crush.

  rewrite <- H.
  destruct (eqb a b).
  right; exists (ret Some a); exists (ret Some (negb a)).
  crush.
  rewrite bind_ret.
  unfold distEquiv; crush.
  left; crush.
  simpl.
  left; crush.
  Qed.
