Require Import UniMath.Foundations.All.

(* There are more than one way to define a universe *)
(* A universe is a family of types. *)
Definition tarski_universe : UU :=
  ∑ X : UU, X → UU.
Definition tarski_universe_over (X : UU) := (X → UU).
(* This version is often what one has in mind, but the former is useful! *) 
Definition Tarski_universe : UU :=
  ∑ X : hSet, X → UU.

(* A universe isa property of types *) 
Definition property_universe : UU := UU → hProp.
(* A universe isa decidable property of types *) 
Definition decidable_universe : UU := UU → bool.
(* A universe is a mapping from types to pointed types *)
(* The "point" indicates that the type is not in the universe *)
(* For instance, UU → Nat is like a "multiset" of types*)
(* Geometrically, the nonzero elements of the classifying type classifies incidences *)
Definition classifying_universe : UU :=
  ∑ X : UU, ∑ zero : X, UU → X.
Definition pointed : UU := ∑ X : UU, X.
Notation "UU*" := pointed.
Definition pointed_to_UU : UU* → UU := pr1.
Coercion pointed_to_UU : pointed >-> UU.
Definition base (X : pointed) : X := pr2 X.
Coercion base : pointed >-> pointed_to_UU.

(* This redefinition is fun, don't you agree? *)
Definition basepoint ( X : UU* ) : X := X.

Definition classifying_universe_over (X : UU*) := UU → X.

Definition unital_classifying_universe : UU :=
  ∑ 𝔘 : classifying_universe ,
      ∏ x : (pr1 𝔘), x = x.

Definition hypertarski : UU := UU → UU.

Definition UU_with_basepoint : UU*.
  exists UU. exact ∅.
Defined.
Notation "UU∅" := UU_with_basepoint.

(* The main definition *)
Inductive Universe : UU :=
| tarski     (X : UU) : tarski_universe_over X → Universe
| propertied (X : UU*) : classifying_universe_over X → Universe.
Axiom wedge : tarski UU = propertied UU∅.
(* The idea isthat Universe isthe wedge sum of the two notions of universe *)

Definition Universe_decomposition : Universe → tarski_universe ⨿ classifying_universe.
  intro.
  induction X.
  left; exists X; exact t.
  right; exists X. exists X. exact c.
Defined.

Definition Universal := UU → UU.
(* \mbfU *)
Section Points.
Context (𝐔 : Universal).
(* tarski points *)
Definition tpoints : UU :=
  ∑ x : UU, ishinh (∑ y : UU, 𝐔 y = x).
(* incident points *)
Definition ipoints : UU :=
  ∑ x : UU, ishinh ( 𝐔 x ).

Definition dualize : Universal → Universal.
  intros.
  exact (λ x, ∑ y : UU, X y = x).
Defined.
End Points.
Notation "◒" := dualize (at level 300). 

Section incidence.
Context (𝐔 : Universal).
Definition ipoint : ipoints 𝐔 → UU.
  exact pr1.
Defined.
Definition imultiplicity : ipoints 𝐔 → UU.
  intro.
  exact (𝐔 (pr1 X)).
Defined.

Definition tpoint : tpoints 𝐔 → UU.
  exact pr1.
Defined.
Definition tmultiplicity : tpoints 𝐔 → UU.
  unfold tpoints.
  intro. induction X as [X _].
  exact (∑ y : UU, 𝐔 y = X).
Defined.

Definition iincidence : ipoints 𝐔 → UU.
  intro.
  exact (ipoint X × imultiplicity X).
Defined.
Definition tincidence : tpoints 𝐔 → UU.
  intro.
  exact (tpoint X × tmultiplicity X).
Defined.

End incidence.

Section incidences.
  Context (𝐔 : Universal).
Definition iincidences := total2 (iincidence 𝐔).
Definition tincidences := total2 (tincidence 𝐔).
End incidences.

Theorem iintot_incidences {x : Universal} : tincidences x = iincidences (◒ x).
  unfold tincidences, iincidences, dualize. unfold iincidence, tincidence.
  unfold tpoints, tpoint, tmultiplicity, ipoints, ipoint, imultiplicity.
  apply idpath.
Defined.

Theorem iintot_points {x : Universal} : tpoints x = ipoints (◒ x).
  unfold tpoints, ipoints, dualize. apply idpath.
Defined.
Theorem iintot_point {x : Universal} : tpoint x = ipoint (◒ x).
  apply idpath.
Defined.
Theorem iintot_incidence {x : Universal} : tincidence x = iincidence (◒ x).
  apply idpath.
Defined.

Definition incidences0 := iincidences.
Definition incidences1 := tincidences.
Fixpoint incidences (n : nat) : Universal → UU.
  induction n.
  - exact iincidences.
  - exact (incidences n ∘ ◒). 
Defined.

Theorem incidence_levels_flatten : ∏ n : nat, ∏ UtoU : Universal,
       ∑ flattened : Universal, incidences 0 flattened = incidences n UtoU .
  intros.
  induction n.
  exists UtoU. apply idpath.
  induction IHn as[lastcase equals].
  simpl.
  exists (◒ lastcase).
  unfold dualize.
  simpl .
  unfold 
  
  induction n.
  - simpl. 
    unfold ipoints, ipoint.
    unfold imultiplicity.
    Theorem incidence_levels_inclusive_strong : ∏ n : nat,
          ∏ UtoU : Universal, 
  
Definition make_ipoints {X : UU} (y : 𝐔 X) : ipoints 𝐔.
  unfold ipoints.
  exists X. intro. intro. apply X0.
  exact y.
Defined.

Definition make_tpoints (Y : UU) : tpoints 𝐔.
  refine (𝐔 Y,, _).
  unfold ishinh.
  simpl.
  unfold ishinh_UU.
  intros.
  apply X.
  exists Y.
  apply idpath.
Defined.

Definition make_iincidence {X : UU} (x : X) (y : 𝐔 X) : iincidence (make_ipoints y).
  split. exact x.
  unfold imultiplicity, make_ipoints.
  exact y.
Defined.
Definition make_tincidence {X : UU} (x : X) (y : 𝐔 X) : tincidence (make_tpoints X).
  split. exact y.
  exists X.
  apply idpath.
Defined.
  
                             



