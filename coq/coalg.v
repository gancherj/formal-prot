Require List.
Module L := List.

Set Implicit Arguments.

Section GenComonad.

Class Monad {M : Type -> Type} := {
  ret : forall {a}, a -> M a;
  bind : forall {a b}, M a -> (a -> M b) -> M b
}.

Variable Config : Type.
Variable Com : Type.
Variable n : nat.
Variable Ps : list Com.
Variable well_typed_com : Com -> Prop.
Variable m : Type -> Type.
Variable M_m : @Monad m.
Variable denote : Com -> (Config -> m Config).

Definition mcomp {a} {b} {c} (f : a -> m b)  (g : b -> m c) : a -> m c :=
  fun x => bind (f x) g.

Check L.fold_left.

Definition round_robin : Config -> m Config :=
  L.fold_left (fun acc com => mcomp acc (denote com)) Ps ret.

Definition C_tr_ (com : Com) : Config -> m Config :=
  mcomp (denote com) round_robin.

Definition C_tr : Config -> (Com -> m Config) := fun C com => C_tr_ com C.

Variable m_lift : forall {a b}, (a -> b -> Prop) -> (m a -> m b -> Prop).

CoInductive Bisim (R : Config -> Config -> Prop) :=
  | B : forall s t, R s t -> (forall com, well_typed_com com -> (m_lift R) (C_tr s com) (C_tr t com)) -> Bisim R.

End GenComonad.
  
  


