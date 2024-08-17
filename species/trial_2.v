(* Any *)
(* Require Import UniMath.Foundations.All. *)
Require Import Setoid.
Notation "'∫' x : A , B" := (sigT (fun x : A => B))
  (at level 200, x ident, A at level 200, right associativity).

Axiom IsSmooth : Type -> Type.
Definition Smooth : Type := ∫ x : Type, IsSmooth x.
Definition man (man : Smooth) : Type.
  induction man; assumption.
Defined.
Coercion man : Smooth >-> Sortclass.
Definition smoothness (man : Smooth) : IsSmooth man.
  induction man; assumption.
Defined.

Axiom NoMan : Smooth.
Axiom Point : Smooth.
Definition Nonzero : Smooth -> Type :=
  fun x => (x = NoMan) -> False.
Definition Someone : Type := ∫ man : Smooth, Nonzero man.

Axiom Plus : Smooth -> Smooth -> Smooth. 
Axiom Times : Smooth -> Smooth -> Smooth.
Axiom Divide : Smooth -> Smooth -> Smooth.
Definition Sn (n : nat) : Smooth.
  induction n.
  (* n = 0 *)
  - exact NoMan.
  - exact (Plus IHn Point).  
Defined.
Coercion Sn : nat >-> Smooth.

Notation "x + y" := (Plus x y).

(* To shorten notation and avoid overlap, "Zed" implies "Zero" *)
Axiom ZedPlusX : forall X     : Smooth, NoMan + X   = X.
Axiom XPlusZed : forall X     : Smooth, X + NoMan   = X.
Axiom PlusAssL : forall X Y Z : Smooth, X + (Y + Z) = (X + Y) + Z.
Axiom PlusAssR : forall X Y Z : Smooth, (X + Y) + Z = X + (Y + Z).
Axiom PlusComm : forall X Y   : Smooth, (X + Y)       = (Y + X).

Definition commuteplus {X Y : Smooth} : man (X + Y) -> man (Y + X).
  intro.
  rewrite (PlusComm Y X).
  assumption.
Defined.

Definition Relabelings (X : Smooth) := ∫ 𝔲 : Smooth, X = 𝔲. 
Definition thelabeledobject {X : Smooth} (relabeling : Relabelings X) : Smooth.
  induction relabeling. exact x.
Defined.
Coercion thelabeledobject : Relabelings >-> Smooth.
Definition thelabelproof {X : Smooth} (relabeling : Relabelings X) : X = relabeling.
  inversion relabeling.
  unfold thelabeledobject.
  simpl.
  unfold sigT_rect.
  induction relabeling.
  assumption.
Defined.
Notation "## H" := (thelabeledobject H) (at level 300).

Axiom Relabel  : forall X : Smooth, Relabelings X.
Definition relabel : Smooth -> Smooth.
  intros X.
  pose proof (Relabel X).
  induction X0 as [X__ _].
  exact X__.
Defined.
Notation "# X" := (relabel X) (at level 300).

Lemma labelsdontmatterL : forall X, X = relabel X.
  intros.
  unfold "#", sigT_rect; simpl.
  induction (Relabel X). assumption. 
Defined.
Lemma labelsdontmatterR : forall X, relabel X = X.
  symmetry; apply labelsdontmatterL.
Defined.

Compute (Relabel (5 + 6 + 4)).

Definition RelabelXL {X Y : Smooth} : man ((Relabel X) + Y) -> man (X + Y).
  intro theoutcome.
  unfold "##", sigT_rect in theoutcome.
  induction (Relabel X).
  rewrite <- p in theoutcome.
  exact theoutcome.
Defined.
Definition RelabelXR {X Y: Smooth} : man (Y + (Relabel X)) -> man (Y + X).
  intro theoutcome.
  rewrite (PlusComm Y (## Relabel X)) in theoutcome.
  apply commuteplus.
  exact (RelabelXL theoutcome).
Defined.

Example relabeling_XY {X Y: Smooth} : man ((Relabel X) + (Relabel Y)) -> man (X + Y).
  intro.
  apply RelabelXR.
  apply RelabelXL.
  assumption.
Defined.

