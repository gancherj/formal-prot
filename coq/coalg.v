
Require Import Arith.
Require Import Ascii.
Require Import String.
Require Import List.

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

Module Type MPSParties (L : LANG).
  Parameter Parties : list (PID * L.Com).
  Parameter wf_Parties : forall p1 p2, In p1 Parties -> In p2 Parties -> p1 <> p2 -> (fst p1) <> (fst p2).
  Parameter Adv_Id : PID.
End MPSParties.

Module MPS (L : LANG) (P : MPSParties L).

  Definition GSt := PID -> (Id -> L.Val).
  Definition update_Gst (i : PID) (s : Id -> L.Val) (gs : GSt) := fun j => if eq_PID j i then s else gs j.


(* GB i j = messages from i to j *)
  Definition GBuf := PID -> PID -> L.Val.
  (* messages to i *)
  Definition ins (i : PID) (g : GBuf) : PID -> L.Val := fun j => g j i.
  (* messages from i *)
  Definition outs (i : PID) (g : GBuf) : PID -> L.Val := fun j => g i j.

  Definition GTrans (gst : GSt) (buf : GBuf) (c : PID * L.Com) : GSt * GBuf := 
    let p := L.denote (snd c) (gst (fst c)) (ins (fst c) buf) in
    (update_Gst (fst c) (fst p) gst, fun i' j => if eq_PID i' (fst c) then (snd p) j else buf i' j).

  Definition round_robin (g : GSt * GBuf) (cs : list (PID * L.Com)) : GSt * GBuf :=
    fold_left (fun acc c => GTrans (fst acc) (snd acc) c) cs g.

  Definition C_tr (g : GSt * GBuf) (c : L.Com) : GSt * GBuf := round_robin g ((P.Adv_Id, c) :: P.Parties).

  Definition adv_Bisim_prog (R : GSt * GBuf -> GSt * GBuf -> Prop) : GSt * GBuf -> GSt * GBuf -> Prop :=
  fun p1 p2 => R p1 p2 -> 
    forall com,
    let g1 := C_tr p1 com in
    let g2 := C_tr p2 com in
    R g1 g2 /\ (forall s, (fst g1) P.Adv_Id s = (fst g2) P.Adv_Id s) /\ (forall j, (snd g1) j P.Adv_Id = (snd g2) j P.Adv_Id).

  Definition adv_Bisim (R : GSt * GBuf -> GSt * GBuf -> Prop) :=
  forall p1 p2, R p1 p2 -> (adv_Bisim_prog R) p1 p2.

End MPS.


