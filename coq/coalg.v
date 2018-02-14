
Require Import Arith.
Require Import Ascii.
Require Import String.
Require Import List.

Definition Id := string.
Definition eq_Id := string_dec.

Module Type LANG.
  Parameter Val : Type.
  Definition St := Id -> Val.
  Parameter Com : Type.
  (* For now, assume language is total, and not defined over any effects. *)
  Parameter denote : Com -> St -> (Id -> Val) -> St * (Id -> Val).
End LANG.

Module Type MPS (L : LANG).
  Parameter Parties : list (string * L.Com).
  Parameter wf_Parties : forall p1 p2, In p1 Parties -> In p2 Parties -> p1 <> p2 -> (fst p1) <> (fst p2).
  Definition GSt := Id -> L.St.
  Definition update_Gst (i : Id) (s : L.St) (gs : GSt) := fun j => if eq_Id j i then s else gs j.

(* GB i j = messages from i to j *)
  Definition GBuf := Id -> Id -> L.Val.
  (* messages to i *)
  Definition ins (i : Id) (g : GBuf) : Id -> L.Val := fun j => g j i.
  (* messages from i *)
  Definition outs (i : Id) (g : GBuf) : Id -> L.Val := fun j => g i j.

  Definition GTrans (gst : GSt) (buf : GBuf) (c : string * L.Com) : GSt * GBuf := 
    let p := L.denote (snd c) (gst (fst c)) (ins (fst c) buf) in
    (update_Gst (fst c) (fst p) gst, fun i' j => if eq_Id i' (fst c) then (snd p) j else buf i' j).

  Definition round_robin (g : GSt * GBuf) (cs : list (string * L.Com)) : GSt * GBuf :=
    fold_left (fun acc c => GTrans (fst acc) (snd acc) c) cs g.

  Parameter adv_Id : Id.
  Definition C_tr (g : GSt * GBuf) (c : L.Com) : GSt * GBuf := round_robin g ((adv_Id, c) :: Parties).

  Definition adv_Bisim_prog (R : GSt * GBuf -> GSt * GBuf -> Prop) : GSt * GBuf -> GSt * GBuf -> Prop :=
  fun p1 p2 => R p1 p2 -> 
    forall com,
    let g1 := C_tr p1 com in
    let g2 := C_tr p2 com in
    R g1 g2 /\ (forall s, (fst g1) adv_Id s = (fst g2) adv_Id s) /\ (forall j, (snd g1) j adv_Id = (snd g2) j adv_Id).

  Definition adv_Bisim (R : GSt * GBuf -> GSt * GBuf -> Prop) :=
  forall p1 p2, R p1 p2 -> (adv_Bisim_prog R) p1 p2.

End MPS.


