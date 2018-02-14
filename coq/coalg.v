
Require Import Arith.
Require Import Ascii.
Require Import String.
Require Import List.
Require Import Permutation.

Definition Id := string.
Definition eq_Id := string_dec.

Definition PID := nat.
Definition eq_PID := Nat.eq_dec.

Module Type LANG.
  Parameter Val : Type.
   Parameter Com : Type.
  (* For now, assume language is total, and not defined over any effects. *)
  (* denote c : st -> inbuf -> st * outbuf *)
  Parameter denote : Com -> (Id -> Val) -> (PID -> Val) -> (Id -> Val) * (PID -> Val).
End LANG.

Record Lang := mkLang {
  Val : Type;
  Com : Type;
  denote : Com -> (Id -> Val) -> (PID -> Val) -> (Id -> Val) * (PID -> Val)
}.



Record Party {L : Lang} {pids : list PID} := mkParty {
  parties : list (PID * (Com L));
  adv_id : PID;
  wf_parties : forall p1 p2, In p1 parties -> In p2 parties -> p1 <> p2 -> (fst p1) <> (fst p2)
               /\ Permutation pids (adv_id :: (map fst parties))
  }.
  

Section MPS.
  Hypothesis L : Lang.
  Hypothesis pids : list PID.
  Hypothesis P : @Party L pids.

  Definition GSt := PID -> (Id -> (Val L)).
  Definition update_Gst (i : PID) (s : Id -> (Val L)) (gs : GSt) := fun j => if eq_PID j i then s else gs j.


(* GB i j = messages from i to j *)
  Definition GBuf := PID -> PID -> (Val L).
  (* messages to i *)
  Definition ins (i : PID) (g : GBuf) : PID -> (Val L) := fun j => g j i.
  (* messages from i *)
  Definition outs (i : PID) (g : GBuf) : PID -> (Val L) := fun j => g i j.

  Definition GTrans (gst : GSt) (buf : GBuf) (c : PID * (Com L)) : GSt * GBuf := 
    let p := (denote L) (snd c) (gst (fst c)) (ins (fst c) buf) in
    (update_Gst (fst c) (fst p) gst, fun i' j => if eq_PID i' (fst c) then (snd p) j else buf i' j).

  Definition round_robin (g : GSt * GBuf) (cs : list (PID * (Com L))) : GSt * GBuf :=
    fold_left (fun acc c => GTrans (fst acc) (snd acc) c) cs g.
  

  Definition C_tr (g : GSt * GBuf) (c : (Com L)) : GSt * GBuf := round_robin g ((adv_id P, c) :: (parties P)).

  Definition adv_Bisim_prog (R : GSt * GBuf -> GSt * GBuf -> Prop) : GSt * GBuf -> GSt * GBuf -> Prop :=
  fun p1 p2 => R p1 p2 -> 
    forall com,
    let g1 := C_tr p1 com in
    let g2 := C_tr p2 com in
    R g1 g2 /\ (forall s, (fst g1) (adv_id P) s = (fst g2) (adv_id P) s) /\ (forall j, (snd g1) j (adv_id P) = (snd g2) j (adv_id P)).

  Definition adv_st_rel (g1 : GSt * GBuf) (g2 : GSt * GBuf) : Prop :=
    (forall s, (fst g1) (adv_id P) s = (fst g2) (adv_id P) s) /\ (forall j, (snd g1) j (adv_id P) = (snd g2) j (adv_id P)).

  Definition adv_Bisim :=
  forall g1 g2, adv_st_rel g1 g2 -> (adv_Bisim_prog adv_st_rel) g1 g2.

End MPS.



