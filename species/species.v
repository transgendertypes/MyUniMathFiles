(* Experimental work on combinatorial species *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Export UniMath.Foundations.NaturalNumbers.

Definition isFunctorial (fu : nat -> UU) : UU :=
  ∏ n n' : nat, (stn n → stn n') -> fu n -> fu n'.

Definition nspecies : UU := ∑ fu : nat -> UU, isFunctorial fu.
Definition nspecies_function : nspecies → (nat -> UU) := pr1.
Coercion nspecies_function : nspecies >-> Funclass.
Definition nspecies_lift {fu : nspecies} {n n' : nat} : 
  (stn n → stn n') -> fu n -> fu n' := pr2 fu n n'.


Definition triv {n} : stn 0 -> stn n.
  intro.
  induction X.
  apply (negnatlthn0) in pr2.
  contradiction.
Defined.

Definition constant {fu : nspecies} {n : nat} : fu 0 → fu n.  
  exact (nspecies_lift triv).
Defined.

Definition raise_stn_function {n n' : nat} (δ : nat)
(fu : stn n -> stn n')   : (stn (n + δ) ->  stn (n' + δ)). 
  admit.
Admitted.
Definition derivative (n : nat) (fu : nspecies) : nspecies.
  exists (λ x, fu (x + n)).
  unfold isFunctorial.
  intros x y.
  intro map.
  exact (nspecies_lift (raise_stn_function n map)).
Defined.

Definition ExponentialProposition : UU :=
    ∑ exp : nspecies, derivative 1 exp = exp.

Definition trivialexponential : ExponentialProposition.
  unfold ExponentialProposition.
  refine (((λ n, ∅),, _),, _).
  Unshelve. Focus 2.
  unfold isFunctorial.
  intros.
  exact X0.
  apply idpath.
Defined.

Definition standardexponential : ExponentialProposition.
  unfold ExponentialProposition.
  refine (((λ n, unit),, _),, _).
  Unshelve. Focus 2.
  unfold isFunctorial.
  intros.
  exact X0.
  apply idpath.
Defined.

Example thetrivialwitnessat5 : ((pr1 standardexponential) 5).
apply constant.
simpl. exact tt.
Defined.


(* This is quite wrong... *)

