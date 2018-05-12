
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

(* make Labels an open sum *)
Inductive Lab {L : Set} : Set :=
  | Recv :  Lab
  | Send :  bool -> Lab 
  | Other : L -> Lab .

Definition tst_trans {L : Set} (n : option bool) (l : @Lab L) :=
  match n, l with
  | None, Recv =>
    Some (x <- ((1/2, true) :: (1/2, false) :: nil); ret (Some x))
  | Some m, Recv => Some (ret (Some m))
  | Some m, Send m' =>
    if eqb m m' then Some (ret (Some m)) else None
  | None, Send _ => None
  | _, Other _ => None
  end.

    
Definition tst {L : Set} :=
  @mkPIOA (@Lab L) (option bool) (fun l => match l with | Recv => true | _ => false end)
          (fun l => match l with | Send _ => true | _ => false end)
          (fun _ => false) None tst_trans.

Definition tst2_trans {L : Set} (n : option bool) (l : @Lab L) :=
  match n, l with
  | None, Recv =>
    Some (x <- ((1/2, true) :: (1/2, false) :: nil); ret (Some (negb x)))
  | Some m, Recv => Some (ret (Some m))
  | Some m, Send m' =>
    if eqb m m' then Some (ret (Some m)) else None
  | None, Send _ => None
  | _, Other _ => None
  end.

Definition tst2 {L : Set} :=
  @mkPIOA (@Lab L) (option bool) (fun l => match l with | Recv => true | _ => false end)
          (fun l => match l with | Send _ => true | _ => false end)
          (fun _ => false) None tst2_trans.

Lemma impltst {L : Set} : implement (@tst L) (@tst2 L).

  eapply simpl_implement.

  (* Labels match up. *)
  crush.
  crush.
  crush.

  (* Start states match up. *)
  instantiate (1 := fun s => match s with
                             | Some b => Some b
                             | None => None
                             end).
  crush.


  (* Transition function lines up. *)
  simpl.
  unfold option_lift; simpl.
  intros.

  (* Case analysis on label and state *)
  induction l.

  (* Recv *)
  induction s.
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

  (* Send *)
  induction s.
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


  (* Other *)
  destruct s; simpl;
  left; crush.
  
Qed.
