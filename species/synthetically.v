Require Import UniMath.Foundations.All.

Axiom Derivative :
  ∏ X : UU,
  ∑ d : UU → UU,
      (* Linearity *)
      (∏ x y : UU, (d x) ⨿ (d y) = d (x ⨿ y)) 
      ×  (∏ x y : UU, x × (d y) -> d (x × y)) 
      (* Losing's allowed *)                              
      ×  (∏ x : UU, ∅ -> d x)
      (* Winning's allowed *)
      ×  (unit -> d X) 
      (* Liebniz rule applies *)
      × (∏ x y : UU, ((x × (d y)) ⨿ ((d x) × y)) -> d (x × y))
      (* Introduction rule *)
      × ∏ Y : UU, X -> (d Y -> Y).

Notation D_ X := (Derivative X) .
Definition d_ (X : UU) := pr1 (D_ X).
Definition derive (X : UU) : ∏ Y : UU, X -> (d_ X Y -> Y).
  exact (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (D_ X))))))).
Defined. 
Definition derive_using {X Y : UU} (x : X) : (d_ X Y) -> Y.
  exact ((derive X Y) x).
Defined.

Definition win_game (X : UU) : (unit -> (d_ X X)).
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (D_ X)))))).
Defined.
(* A roundabout proof of something familiar *)
Definition win_with {X : UU} (x : X) : (unit -> (X)).
  intro t.
  apply (derive_using x).
  apply (win_game X).
  exact t.
Defined.

Lemma x_to_dx {X : UU} (x : X) : (d_ X) X.
  apply (win_game X).
  exact tt.
Defined.

Definition lose {X Y : UU} : (∅ -> (d_ X) Y). 
  exact fromempty.
Defined.

Definition losing_strategy {X : UU} (x : X) : X.
  apply (derive_using x).
  apply lose.
  Abort.

(*********************************************Calc Rules *************)

(* Liebniz *)
Definition liebniz {X : UU} : ∏ x y : UU, ((x × (d_ X y)) ⨿ ((d_ X x) × y)) -> d_ X (x × y).
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (D_ X))))))).
Defined.

Definition sumrule {X : UU} : ∏ x y : UU, d_ X x ⨿ d_ X y = d_ X (x ⨿ y).
  exact (pr1 (pr2 (D_ X))).
Defined.
Definition scalarrule {X : UU} : ∏ x y : UU, x × d_ X y -> d_ X (x × y).
  exact (pr1 (pr2 (pr2 (D_ X)))).
Defined.

Example scalarexample {X Y : UU} (x : X) (y : Y) : X × Y.
  apply (derive_using y).
  apply (scalarrule).
  split.
- assumption.
- apply (win_game Y).
  exact tt.
Defined.

Example sumexample {X Y : UU} (x : X) (y : Y) : X ⨿ Y.
apply (derive_using x).
rewrite <- sumrule.
left. apply (win_game X).
exact tt.
Defined.

Example sameexample_differentstrategy {X Y : UU} (x : X) (y : Y) : X ⨿ Y.
apply (derive_using x).
rewrite <- sumrule.
right.
apply lose.
Abort.

Example liebniz_example {X Y : UU} (x : X) (y : Y) : X × Y.
apply (derive_using x).
apply liebniz.
right.
split.
apply (win_game X); exact tt.
exact y.
Defined.
(* You have to imagine the linear types here, I don't yet know how in coq*)
Example better_liebniz_example {X Y : UU} (x0 x1 : X) : X × X.
apply (derive_using x0).
apply liebniz.
apply (derive_using x1).
rewrite <- sumrule.
left.
apply liebniz.
right.
split; apply (win_game X); exact tt.
Defined.

Definition win {X : UU} : d_ X X.
  apply (win_game X); exact tt.
Defined.

Axiom exponentials : ∑ exp : UU → UU,
      ∏ X : UU, (d_ X (exp X) = exp X)
                  × ∏ Y : UU, ((exp X -> d_ X Y) -> d_ (exp X) Y).
Definition exp : UU → UU := pr1 exponentials.
Definition exprules (X : UU) 
  := (pr2 exponentials) X.
Definition exprule1 {X : UU} : d_ X (exp X) = exp X
  := (pr1 (exprules X)).
Definition exprule2 {X Y : UU}
  := (pr2 (exprules X)) Y.

Compute exp unit.

(* again, imagine that my exp is an affine resource *) 
(* or linear in which case I cannot finish this proof*) 
Example exponentials_example {X : UU} : exp X -> X.
intro etox.
apply (derive_using etox).
apply exprule2.
intro.
apply win.
Defined.

Example exponentials_example2 {X : UU} : X -> exp X.
intro x.
apply (derive_using x).
rewrite exprule1.
apply (derive_using x).
rewrite exprule1.
apply (derive_using x).
apply (derive_using x).
rewrite exprule1.
rewrite exprule1.
(* you get the picture *)
Abort.

(* This axiom is optional but it makes the geometry better *) 
Axiom introduce_exponential: ∏ X : UU, X -> exp X.
Definition expintro {X : UU} (x : X) : exp X.
  apply introduce_exponential.
  exact x.
Defined.


Axiom exponentialminusone : ∑ expminusone : UU → UU,
    ∏ X : UU, (d_ X (expminusone X) = (expminusone X) ⨿ unit) × (∏ Y : UU, (exp X -> d_ X Y) -> d_ (expminusone X) Y).
Definition expminusone : UU → UU := pr1 exponentialminusone.
Definition expminusonerules (X : UU) 
  := (pr2 exponentialminusone) X.
Definition expminusonerule1 {X : UU} 
  := (pr1 (expminusonerules X)).
Definition expminusonerule2 {X : UU}
  := (pr2 (expminusonerules X)).

Example minusone_example1 {X : UU} : X -> expminusone X.
  intro x.
  apply (derive_using x).
  rewrite expminusonerule1.
  left.
  apply (derive_using x).
  rewrite expminusonerule1.
  left.
  apply (derive_using x).
  rewrite expminusonerule1.
  left.
  apply (derive_using x).

  rewrite expminusonerule1.
  right.
  exact tt.
  (* you get the picture; with the additional axiom we have way more proofs.*)
Defined.




Example minusone_example2 {X : UU} : expminusone X -> (X ⨿ unit).
intro.
apply (derive_using X0).
clear X0.
apply (expminusonerule2).
intro.
rewrite <- sumrule.
left. apply win.
Defined.


(* 

Axiom DerivativeDual :
  ∏ X : UU,
  ∑ d : UU → UU,
      (* Linearity *)
      (∏ x y : UU, (d x) ⨿ (d y) = d (x ⨿ y)) 
      ×  (∏ x y : UU, x × (d y) <- d (x × y)) 
      (* Losing's allowed *)                              
      ×  (∏ x : UU, ∅ <- d x)
      (* Winning's allowed *)
      ×  (unit <- d X) 
      (* Liebniz rule applies *)
      × (∏ x y : UU, ((x × (d y)) ⨿ ((d x) × y)) <- d (x × y))
      (* Introduction rule *)
      × ∏ Y : UU, X <- (d Y -> Y).
Notation D' := DerivativeDual.
Definition d' (X : UU) : UU -> UU := pr1 (DerivativeDual X).

Definition liebniz' {X : UU} : ∏ x y : UU, ((x × (d' X y)) ⨿ ((d' X x) × y)) <- d' X (x × y).
  exact (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (D' X))))))).
Defined.

Definition sumrule' {X : UU} : ∏ x y : UU, d' X x ⨿ d' X y = d' X (x ⨿ y).
  exact (pr1 (pr2 (D' X))).
Defined.
Definition scalarrule' {X : UU} : ∏ x y : UU, x × d' X y <- d' X (x × y).
  exact (pr1 (pr2 (pr2 (D' X)))).
Defined.

Axiom Obtain: ∏ X Y : UU, (Y -> d_ X Y) -> (Y -> (X × d' X Y)).  

Definition obtain {Y : UU} (X : UU) : (Y -> d_ X Y) -> (Y -> (X × (d' X Y))).
  apply Obtain.
Defined.

Example obtain_XY {X Y : UU} : X × Y -> X.
intro XY.
apply (obtain X) in XY.
induction XY as [part rest].
exact part.
intro resource.
apply liebniz.
right.
split.
apply win.
exact (pr2 resource).
Defined.

Example obtain_Lplus {X Y : UU} : X⨿Y -> X.
intro XY.
apply (obtain X) in XY.
induction XY as [part rest].
exact part.
intro resource.
rewrite <- sumrule.
left. apply win.
Defined.

Example obtain_Rplus {X Y : UU} : Y⨿X -> X.
intro XY.
apply (obtain X) in XY.
induction XY as [part rest].
exact part.
intro resource.
rewrite <- sumrule.
right. apply win.
Defined.

Example leftside : unit ⨿ unit. left. exact tt. Defined.
Compute (obtain_Lplus leftside).
Compute (obtain_Rplus leftside).
  


 *) 

Example XY {X Y : UU} : X -> Y -> X × Y.
  intros x y.
  apply (derive_using x).
  apply liebniz.
  apply (derive_using y).
  rewrite <- sumrule.
  right.
  apply liebniz.
  left.
  split.
  - apply win.
  - apply win.
Defined.
Notation "∂" := derive_using.
(* Using tactics we can simulate linear resource usage *)
Ltac δ x  := apply (∂ x); clear x; try apply liebniz; try rewrite <- sumrule; try apply win.
Ltac simplify := repeat try apply liebniz; try rewrite <- sumrule; try apply win.
Ltac splitify := repeat try (simplify; split; simplify; split; simplify).
Ltac LEFT x  := apply (∂ x); clear x; repeat try simplify; repeat (left; try simplify). 
Ltac SPLIT x  := apply (∂ x); clear x; repeat try (apply liebniz; try rewrite <- sumrule; try split; try apply win).
Ltac win := apply win.
Ltac checkmate x := apply (win_with x); apply tt.
Example XPlusY {X Y : UU} : X -> X ⨿ Y.
intro x.
(* wins automatically *)
(* LEFT x. *)
δ x.
left.
simplify.
Defined.
Example Xwin {X : UU} : X -> X.
intro x.
checkmate x.
Defined.

Example XTimesY {X Y : UU} : X -> Y -> X × Y.
intros x y. SPLIT y.
left.
split.
checkmate x.
win.
Defined.

Example XCubed {X : UU} : X -> X -> X -> X × X × X.
intros x1 x2 x3.
δ x1.
right.
split; try win.
δ x2.
left. split; try win.
δ x3.
Defined.

Example x_fourth_plus_one {X : UU} : X -> X -> X -> X -> ((X × X × X × X) ⨿ unit).
intros x0 x1 x2 x3.
δ x0. 
left. simplify.
left. split.
- δ x1.
- clear x1. simplify.
  left. split.
  + δ x2.
  + clear x2.
    simplify. left. split.
    ++ δ x3.
    ++ clear x3.
       win.
Defined.

Example x_fourth_plus_one_trivial {X : UU} : unit -> ((X × X × X × X) ⨿ unit).
intro tt.
δ tt.
right. win.
Defined.

(******* Trees and things ********)

Definition BinaryTypeConstructor : UU :=
  ∑ 𝔣 : UU → UU, ∏ 𝔵 : UU, (𝔣 𝔵) × (𝔣 𝔵) -> d_ 𝔵 (𝔣 𝔵). 
Definition 𝔣 : BinaryTypeConstructor -> (UU -> UU) := pr1.
Coercion 𝔣 : BinaryTypeConstructor >-> Funclass.

Axiom Tree : ∑ ϕ : BinaryTypeConstructor,
      (ϕ ∅) ×
(∏ X Y : UU, (X -> Y) -> (ϕ X -> ϕ Y)).
Definition tree := pr1 Tree.
Notation ϕ := tree.
Definition treerule1 {x : UU} := pr2 (pr1 Tree) x.
Definition treerule2 := pr1 (pr2 Tree).
Definition treerule3 {x y : UU} (f : x -> y) := pr2 (pr2 Tree) x y f.
Definition trivialize_tree (X : UU)  := (treerule3 (fromempty :∅ -> X)).
Example tree_example {X : UU} : X -> X -> ϕ X.
intros x0 x1.
  δ x0.
  apply treerule1.
  split.
- apply (trivialize_tree X).
  exact treerule2.
- δ x1.
  apply treerule1.
  split;
    apply (trivialize_tree X);
    exact treerule2.
Defined.

Example obtain_from_exp {x : UU} : exp x -> x ⨿ unit.
- intro exx. δ exx.
  left. apply exprule2.
  intro. win.
Defined.
Check exprule2.
Axiom obtainaxiom_unsure : ∏ f : UU -> UU, ∏ X Y : UU, ((d_ X (f X) -> d_ X Y) -> d_ (f X) Y).
Example obtain_from_tree {x : UU} : ϕ x -> x ⨿ unit.
intro tree.
δ tree.
rewrite sumrule.
apply obtainaxiom_unsure.
intro.
simplify.
left. win.
Defined.

Example plusone : UU → UU := λ X, X ⨿ unit.
Example xplusone {X : UU} : X ⨿ unit -> X ⨿ unit.
intro xplusone.
δ xplusone.
left.
apply obtainaxiom_unsure.
intro.
Abort. (* nothing is contradicted, but not useful here *)

Example onetimesx{X : UU} : unit × X -> X.
intro xone.
δ xone.
apply obtainaxiom_unsure.
intro.
win.
Defined.

Definition square : UU → UU := λ x, x × x.

Axiom winpath : ∏ X : UU, d_ X X = unit. 
Axiom xtimesunit : ∏ X : UU,  X × unit = X. 
Axiom unittimesx : ∏ X : UU,  unit × X = X. 
Definition cleanup (X : UU) : X × unit = X := xtimesunit X.
Definition cocleanup (X : UU) : unit × X = X := unittimesx X.
Ltac unitize X := rewrite (winpath X).
Ltac cleanup X := try rewrite (cleanup X); try rewrite (cocleanup X).

Example squareofx {X : UU} : X -> X -> square X.
intros x0 x1.
δ x0.
δ x1.
rewrite sumrule.
unitize X.
pose proof (cleanup X).
simplify.
left.
apply liebniz.
right.
split. win. apply tt.
Defined.

Example squared_test {X : UU} : X × X -> X × X.
intro square.
apply (∂ square).
win.
Defined.

Example squared_test2 {X : UU} : X × X -> X × X.
intro square.
apply (∂ square).
apply obtainaxiom_unsure.
intro.
exact X0.
Defined.











  



                                                        
