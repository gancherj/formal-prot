

Require Import Arith.
Require Import Ascii.
Require Import String.
Require Import List.
Require Import Permutation.

Definition Id := string.
Definition eq_Id := string_dec.

Definition PID := nat.
Definition eq_PID := Nat.eq_dec.

Class RelMonad (m : Type -> Type) := {
  ret : forall {a}, a -> m a;
  bind : forall {a b}, m a -> (a -> m b) -> m b;
  (* Relational lifting operator. *)
  rel_lift : forall {a b} (R : a -> b -> Prop), m a -> m b -> Prop 
}.

Definition State s a := s -> (a * s)%type.
Definition stateRet (S A : Type) (a : A) := fun (s : S) => (a , s).

Definition stateBind (S A B : Type) (ma : State S A) (f : A -> State S B) : State S B := 
  fun s =>
    let p := ma s in
    let p' := f (fst p) (snd p) in
    p'.


Definition stateRelLift (S A B : Type) (R : A -> B -> Prop) (ma : S -> A * S) (mb : S -> B * S) :=
  forall s, R (fst (ma s)) (fst (mb s)) /\ snd (ma s) = snd (mb s).
Instance StateM : forall s, RelMonad (State s) := {ret := stateRet _; bind := stateBind _; rel_lift := stateRelLift _}.

Definition mcomp {m : Type -> Type} `{RelMonad m} {a b c} (f : a -> m b) (g : b -> m c) : a -> m c :=
  fun a => bind (f a) g.

Record Lang {m : Type -> Type} `{RelMonad m} :=  {
  Val : Type;
  Com : Type;
  denote : Com -> (Id -> Val) -> (PID -> Val) -> m ((Id -> Val) * (PID -> Val))%type
}.

Record System {m : Type -> Type} `{RelMonad m} {L : @Lang m _} {pids : list PID} :=  {
  parties : list (PID * (Com L));
  adv_id : PID;
  wf_parties : forall p1 p2, In p1 parties -> In p2 parties -> p1 <> p2 -> (fst p1) <> (fst p2)
               /\ Permutation pids (adv_id :: (map fst parties))
  }.
  

Section MPS.
  Context (m : Type -> Type) `{RelMonad m}.
  Hypothesis L : @Lang m _.
  Hypothesis pids : list PID.
  Hypothesis P : @System m _ L pids.

  Definition GSt := PID -> (Id -> (Val L)).
  Definition update_Gst (i : PID) (s : Id -> (Val L)) (gs : GSt) := fun j => if eq_PID j i then s else gs j.


(* GB i j = messages from i to j *)
  Definition GBuf := PID -> PID -> (Val L).
  (* messages to i *)
  Definition ins (i : PID) (g : GBuf) : PID -> (Val L) := fun j => g j i.
  (* messages from i *)
  Definition outs (i : PID) (g : GBuf) : PID -> (Val L) := fun j => g i j.

  Definition GTrans (gst : GSt) (buf : GBuf) (c : PID * (Com L)) : m (GSt * GBuf) := 
    let mp := (denote L) (snd c) (gst (fst c)) (ins (fst c) buf) in
    bind mp (fun p =>
    ret (update_Gst (fst c) (fst p) gst, fun i' j => if eq_PID i' (fst c) then (snd p) j else buf i' j)).

  Definition round_robin (g : GSt * GBuf) (cs : list (PID * (Com L))) : m (GSt * GBuf) :=
    fold_left (fun acc c => bind acc (fun p => GTrans (fst p) (snd p) c)) cs (ret g).
  

  Definition C_tr (g : GSt * GBuf) (c : (Com L)) : m (GSt * GBuf) := round_robin g ((adv_id P, c) :: (parties P)).
End MPS.

Section NI.
  Context (m : Type -> Type) `{RelMonad m}.
  Hypothesis L : @Lang m _.
  Hypothesis pids : list PID.
  Hypothesis S1 : @System _ _ L pids.
  Hypothesis S2 : @System _ _ L pids.

  Definition C_tr_1 := @C_tr _ _ L pids S1.
  Definition C_tr_2 := @C_tr _ _ L pids S2.

  Definition GlSt := ((GSt _ L) * (GBuf _ L))%type.   

  Definition adv_NI_prog (R : GlSt -> GlSt -> Prop) : GlSt -> GlSt -> Prop :=
  fun p1 p2 => R p1 p2 -> 
    forall com,
    let g1 := C_tr_1 p1 com in
    let g2 := C_tr_2 p2 com in
    (* TODO: Check that this is the correct relational lift. *)
    (rel_lift (fun g1 g2 => R g1 g2 /\ 
                            (forall s, (fst g1) (adv_id S1) s = (fst g2) (adv_id S2) s) /\
                            (forall j, (snd g1) j (adv_id S1) = (snd g2) j (adv_id S2))) g1 g2).

  Definition adv_st_rel (g1 : GlSt) (g2 : GlSt) : Prop :=
    (forall s, (fst g1) (adv_id S1) s = (fst g2) (adv_id S2) s) /\ (forall j, (snd g1) j (adv_id S1) = (snd g2) j (adv_id S2)).

  Definition adv_NI :=
  forall g1 g2, adv_st_rel g1 g2 -> (adv_NI_prog adv_st_rel) g1 g2.

End NI.

Check adv_NI.


