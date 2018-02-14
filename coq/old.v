Require List.
Module L := List.

Set Implicit Arguments.

Section GenComonad.

Class Monad {M : Type -> Type} := {
  ret : forall {a}, a -> M a;
  bind : forall {a b}, M a -> (a -> M b) -> M b
}.

(* Config would be a tuple of variables local to each process, along with buffers between each process. I.e., a global state.*)
Variable Config : Type.

(* Com would be a (perhaps security-typed) language with send and receive actions, which alter the buffers in the configuration. *)
(* We may use information flow techniques to soundly model cryptographic primitives. *)
Variable Com : Type.
Variable n : nat.

(* The parties in the protocol. *)
Variable Ps : list Com.

(* Requiring that input commands are well-typed restricts what the adversary may do. (i.e., cannot decrypt a ciphertext it doesn't (statically) have a public key for). *)
Variable well_typed_com : Com -> Prop.

(* The language semantics can be parameterized over a monad. *)
Variable m : Type -> Type.
Variable M_m : @Monad m.
Variable denote : Com -> (Config -> m Config).

(* Observation function for Config. This denotes, for example, the output bit sent by the adversary. *)
Variable Obs : Type.
Variable obs : Config -> Obs.

Definition mcomp {a} {b} {c} (f : a -> m b)  (g : b -> m c) : a -> m c :=
  fun x => bind (f x) g.

Definition round_robin : Config -> m Config :=
  L.fold_left (fun acc com => mcomp acc (denote com)) Ps ret.

Definition C_tr_ (com : Com) : Config -> m (Config * Obs) :=
  mcomp (mcomp (denote com) round_robin) (fun c => ret (c, obs c)).

Definition C_tr : Config -> (Com -> m (Config * Obs)) := fun C com => C_tr_ com C.

(* Lifting of the functor m \circ (_ * Obs). For example, if m is identity monad and R is (fun _ _ => True), m_obs_lift R will relate s and t if they have identical observations.*)
Variable m_obs_lift : forall {a b}, (a -> b -> Prop) -> (m (a * Obs) -> m (b * Obs) -> Prop).

(* R is a bisimulation if whenever sRt, then for every well-typed com, (C_tr s com) (Rel (m \circ (_ * Obs)) (R)) (C_tr t com). *)
Definition Bisim (R : Config -> Config -> Prop) : Prop := forall s t,  R s t -> (forall com, well_typed_com com -> (m_obs_lift R) (C_tr s com) (C_tr t com)).

Check Bisim.

End GenComonad.
  
  


