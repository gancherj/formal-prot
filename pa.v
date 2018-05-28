
Add LoadPath "~/fcf/src".
Require Import Dist.
Require Import FcfLems.
Require Import FCF.Rat.
Require Import FCF.Fold.
Require Import List.
Require Import CpdtTactics.

Inductive ActType := HiddenAct | InAct | OutAct.

Record PA {Q Act : Set} :=
  {
    start : Q;
    trans : Q -> Act -> option (Dist Q);
    actType : Act -> option ActType;
    }.
                                     
Definition Exec {Q act : Set} (P : @PA Q act) := list (Q * act).

Definition appAction {Q act : Set} (P : @PA Q act) (a : act) (d : Dist (Exec P)) : Dist (Exec P) :=
  alpha <- d;
  match alpha with
  | nil =>
    match (trans P (start P) a) with
    | Some eta => x <- eta; ret ((x,a) :: nil)
    | None => ret nil
    end
  | (s,a') :: exec =>
    match (trans P s a) with
    | Some eta => x <- eta; ret (x,a) :: (s,a') :: exec
    | None => ret (s,a') :: exec
    end
  end.

Definition appActionsFrom {Q act : Set} (P : @PA Q act) (acts : list act) (from : Dist (Exec P)) :=
  fold_left (fun acc a => appAction P a acc) (rev acts) from.

Definition appActions {Q act : Set} (P : @PA Q act) (acts : list act) :=
  appActionsFrom P acts (ret nil).


Lemma appActions_cons {Q act : Set} (P : @PA Q act) (xs : list act) (x : act) : forall d,
  appActionsFrom P (x :: xs) d = appAction P x (appActionsFrom P xs d).
  unfold appActionsFrom.
  simpl.
  intros.
  rewrite fold_left_app.
  simpl.
  auto.
Qed.


Lemma appActions_app {Q act : Set} (P : @PA Q act) (a1 a2 : list act) : forall d,
  appActionsFrom P (a1 ++ a2) d = appActionsFrom P a1 (appActionsFrom P a2 d).
induction a1; intros.
simpl.
auto.
simpl.
rewrite appActions_cons.
rewrite appActions_cons.
rewrite IHa1.
auto.
Qed.


Definition traceOf {Q act : Set} (P : @PA Q act) (alpha : list act) :=
  filter (fun a =>
            match (actType P a) with
            | Some InAct | Some OutAct => true
            | _ => false
                     end
                     ) alpha.

Definition traceOfDist {Q act : Set} {P : @PA Q act} (d : Dist (Exec P)) : Dist (list act):=
  alpha <- d;
  ret (traceOf P (map snd alpha)).


Definition Comparable {Q Q' act : Set} (P1 : @PA Q act) (P2 : @PA Q' act) :=
  (forall a, actType P1 a = Some HiddenAct -> actType P2 a = None) /\
  (forall a, actType P2 a = Some HiddenAct -> actType P1 a = None).


Definition PARefine {Q Q' act : Set} (P1 : @PA Q act) (P2 : @PA Q' act) (traceMetric : Dist (list act) -> Dist (list act) -> Prop) :=
  Comparable P1 P2 /\
  (forall acts, exists acts',
        traceMetric 
        (traceOfDist (appActions P1 acts)) (traceOfDist (appActions P2 acts'))).
        
  
Definition PASim {Q Q' act : Set} (P : @PA Q act) (P' : @PA Q' act) (R : Dist (Exec P) -> Dist (Exec P') -> Prop) (traceMetric : Dist (list act) -> Dist (list act) -> Prop) :=
  (forall d1 d2, R d1 d2 -> traceMetric (traceOfDist d1) (traceOfDist d2)) /\
  (R (ret nil) (ret nil)) /\
  (forall d1 d2, R d1 d2 ->
                 forall a, exists acts,
                     (traceOf P (a :: nil) = traceOf P' acts) /\
                     R (appAction P a d1) (appActionsFrom P' acts d2)).

Lemma simSound {Q Q' act : Set} (P : @PA Q act) (P' : @PA Q' act) R M :
  Comparable P P' ->
  PASim P P' R M -> PARefine P P' M.
  intros.
  constructor.
  auto.
  cut (forall acts, exists acts',
            (M
            (traceOfDist (appActions P acts)) (traceOfDist (appActions P' acts'))) /\
            (R (appActions P acts) (appActions P' acts'))).
  intros.
  destruct (H1 acts); crush.
  exists x.
  destruct H0.
  apply H0.
  crush.
  
  intros.
  induction acts.
  exists nil.
  unfold traceOfDist.
  unfold appActions.
  unfold appActionsFrom.
  simpl.
  destruct H0.
  split.
  apply H0.
  crush.
  crush.
  
  crush.
  destruct H0.
  destruct H1.
  destruct (H4 (appActions P acts) (appActions P' x) H3 a).
  destruct H5.
  exists (x0 ++ x).
  unfold appActions.
  split.
  apply H0.
  unfold appActions in H6.
  rewrite <- appActions_app in H6.
  rewrite appActions_cons.
  crush.
  rewrite appActions_cons.
  unfold appActions in H6.
  rewrite appActions_app.
  crush.
Qed.
  
 