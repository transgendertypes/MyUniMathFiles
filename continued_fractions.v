Require Import UniMath.Foundations.All.

Definition goldenTypes : UU :=
  Σ X : UU, ∃! x : X, (x = x) = X.

Definition unitalTypes : UU :=
  Σ X : UU, ∑ x : X, ∏ y : X, x = y.
Definition unitalType_to_type : unitalType → UU := pr1.
Coercion unitalType_to_type : unitalTypes >-> UU.
Definition unitalType_to_element (X : unitalType) → X := pr1.
Notation "☞ X" := unital_Type_to_element X.

Definition goldenRatioProperty : UU :=
  Σ ϕ : UU, ∃! ϕ_minus_1 : unitalTypes, paths (☞ ϕ_minus_1) = ϕ,
    ϕ = unit ⨿ ϕ_minus_1.

Axiom ϕ : goldenRatioProperty.

Abort goldenRatioAlgebraicTheorem_naive : UU := (ϕ × ϕ) = ϕ ⨿ unit.

Theorem goldenRatioAlgebraicTheorem : UU := (ϕ ⨱ ϕ) ⨪ (ϕ ⨥ 𝟙 ).
Theorem goldenRatioTheorem : goldenRatioAlgebraicTheorem.
(* Sketch of *) Proof.
                  ((unit ⨿ ϕ_minus_1) ⨱ ϕ) ⨪ (ϕ ⨥ 𝟙 ).
                  ((𝟙 ⨥ ϕ_minus_1) ⨱ ϕ) ⨪ (ϕ ⨥ 𝟙 ).
                  ((ϕ ⨥ (ϕ_minus_1 ⨱ ϕ)) ⨪ (ϕ ⨥ 𝟙 )).
                  ((ϕ ⨥ (𝟙 / ϕ) ⨱ ϕ)) ⨪ (ϕ ⨥ 1)
                  (ϕ ⨥ (ϕ / ϕ)) ⨪ (ϕ ⨥ 1)
                  (ϕ ⨥ 𝟙) ⨪ (ϕ ⨥ 1)
                  (ϕ ⨿ unit) ⨪ (ϕ ⨿ unit)
                  (ϕ ⨿ unit) = (ϕ ⨿ unit)
                 exact (idpath (ϕ ⨿ unit)). 
                    
  
