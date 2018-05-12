
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

Inductive Lab : Set :=
  | Recv : Lab
  | Send : bool -> Lab.

Definition tst_trans (n : option bool) (l : Lab) :=
  match n, l with
  | None, Recv =>
    Some (x <- ((1/2, true) :: (1/2, false) :: nil); ret (Some x))
  | Some m, Recv => Some (ret (Some m))
  | Some m, Send m' =>
    if eqb m m' then Some (ret (Some m)) else None
  | None, Send _ => None
  end.

Check mkPIOA.
    
Definition tst :=
  @mkPIOA Lab (option bool) (fun l => match l with | Recv => true | _ => false end)
          (fun l => match l with | Send _ => true | _ => false end)
          (fun _ => false) None tst_trans.

Definition tst2_trans (n : option bool) (l : Lab) :=
  match n, l with
  | None, Recv =>
    Some (x <- ((1/2, true) :: (1/2, false) :: nil); ret (Some (negb x)))
  | Some m, Recv => Some (ret (Some m))
  | Some m, Send m' =>
    if eqb m m' then Some (ret (Some m)) else None
  | None, Send _ => None
  end.

Definition tst2 :=
  @mkPIOA Lab (option bool) (fun l => match l with | Recv => true | _ => false end)
          (fun l => match l with | Send _ => true | _ => false end)
          (fun _ => false) None tst2_trans.

Lemma impltst : implement tst tst2.
  eapply simpl_implement.
  crush.
  crush.
  crush.

  instantiate (1 := fun s => match s with
                             | Some b => Some b
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
  exists (ret Some a).
  crush.
  rewrite bind_ret.
  unfold distEquiv; crush.
  simpl.
  right.
  exists ((x <- [(1 / 2, true); (1 / 2, false)]; ret Some x)).
  exists ((x <- [(1 / 2, true); (1 / 2, false)]; ret Some (negb x))).
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
  destruct (eqb a b).
  right.
  exists (ret Some a), (ret Some a).
  crush.
  rewrite bind_ret.
  unfold distEquiv; crush.
  left; crush.
  simpl.
  left; crush.
Qed.
