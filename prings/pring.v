Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Section chu_universes.
  (* Chu structures over UU *)
  Definition chu (X Y : UU) : UU := X → Y → UU.
  Definition incidence (X Y : UU) : UU := X → Y → hProp.
  Definition chu_to_incidence {X Y}
    (chu : chu X Y) : incidence X Y
    := λ x, ishinh ∘ chu x.
  Definition incidence_to_chu {X Y}
    (incidence : incidence X Y) : chu X Y
    := incidence.
  Coercion incidence_to_chu : incidence >-> chu.
  Coercion chu_to_incidence : chu >-> incidence.
End chu_universes.
          
Section predicates.
  (* Predicative Monoids *)
  Definition chu_property := λ X, X → UU.
  Definition property := λ X, X → hProp.
  Definition chu_property_to_property {x} : chu_property x → property x.
    intro chu. exact (ishinh ∘ chu).
  Defined.
  Definition property_to_chu_property {x} : property x → chu_property x.
    intro chu. exact chu.
  Defined.
  Coercion chu_property_to_property : chu_property >-> property.

    Definition punion {X} : chu_property X → chu_property X → chu_property X . 
      intros.
      exact (λ x, X0 x × X1 x).
    Defined.
      
  Definition predicate := total2 chu_property.
  Definition predicate_to_property (X : predicate)
    : (pr1 X) → UU
    := pr2 X.
  Coercion predicate_to_property : predicate >-> Funclass.
  Definition predicate_to_type : predicate → UU := pr1.
  Coercion predicate_to_type : predicate >-> UU.

  Definition 𝔘 : predicate → UU :=
    λ X, ∑ x : X, X x. 
  
  Definition property_to_predicate {X}
    : (X → hProp) → predicate.
  Proof.
    intro pred. exists X. exact pred.
  Defined.

  Context (𝔐 : predicate).
  Context (plus : 𝔐 → 𝔐 → 𝔐).

  Definition 𝔘_to_predicate (_ : 𝔘 𝔐) : predicate := 𝔐.
  Coercion 𝔘_to_predicate : 𝔘 >-> predicate.
  Definition 𝔘_to_element (uu : 𝔘 𝔐) : 𝔐 := pr1 uu.
  Coercion 𝔘_to_element : 𝔘 >-> predicate_to_type.

  Definition ispmagma : UU :=
    ∏ x y : 𝔐, 𝔐 x → 𝔐 y → 𝔐 (plus x y).
  Definition ispmagma' : UU :=
    ∏ x y : 𝔘 𝔐, 𝔐 (plus x y).  
  Lemma ispmagma_alternate :
    ispmagma → 
    ispmagma'.  
  Proof.
    unfold ispmagma'.
    intros.
    pose proof (X x y).
    induction x, y.
    exact (X0 pr2 pr3).
  Defined.
  Lemma ispmagma_alternate' :
    ispmagma <- 
    ispmagma'.  
    unfold ispmagma. intros.
    remember (x,, X0) as ux.
    remember (y,, X1) as uy.
    pose proof (X ux uy).
    rewrite Hequy in X2.
    rewrite Hequx in X2.
    exact X2.
  Defined.

  Definition ispmagma_eq_ispmagma' : Equivalence ispmagma ispmagma'. 
    exists ispmagma_alternate. exists ispmagma_alternate'.
    unfold ispmagma_alternate, ispmagma_alternate'.
    unfold ispmagma, ispmagma'. unfold 𝔘. simpl.
    unfold 𝔘_to_predicate.
    unfold 𝔘_to_element.
    unfold predicate_to_property.
    unfold predicate_to_type.
    simpl.
    exists (λ _, idpath _).
    exists (λ _, idpath _).
    intro. apply idpath.
  Defined.

  Definition paths_ispmagma : ispmagma = ispmagma'. 
    apply univalence. apply Equivalence_to_weq.
    apply ispmagma_eq_ispmagma'.
  Defined.
  End predicates.

  Notation "x ∪ y" := (punion x y).

  Definition pmagma : UU := ∑ pre : predicate, ∑ op, ispmagma pre op.
  Definition pmagma_to_predicate : pmagma → predicate := pr1.
  Coercion pmagma_to_predicate : pmagma >-> predicate.
  Definition op (𝔓 : pmagma) : 𝔓 → 𝔓 → 𝔓 := pr12 𝔓.

  Section properties_of_pmagmas. 
  Context (𝔓 : pmagma). Context (plus := op 𝔓).

  Definition punital : UU.
    exact (∑ zero : 𝔓, ∏ x : 𝔓,
                plus x zero = x
          ×     plus zero x = x).
  Defined.

  Definition pcommutes : UU :=
    ∏ x y : 𝔓, plus x y = plus y x.

  Definition passociates : UU :=
    ∏ x y z : 𝔓, plus x (plus y z) = plus (plus x y) z.

  Definition pcancels : UU :=
    ∏ x y z : 𝔓, (plus x y = plus x z) → ( y = z ).

  Definition pdivisible : UU :=
    ∏ x y : 𝔓, ∃! z z' : 𝔓,
          plus x  z = y
        × plus z' x = y. 
  End properties_of_pmagmas. 

  Section magma_hierarchy.
    Definition punitalmagma :=
      total2 punital.
    Definition punitalmagma_to_magma : punitalmagma → pmagma := pr1.
    Coercion punitalmagma_to_magma : punitalmagma >-> pmagma.

    Definition idelem {𝔪 : punitalmagma} : 𝔪.
    Proof.
      induction 𝔪, pr2.
      assumption.
    Defined.
    Notation 𝔢 := idelem.
    
    Definition pquasigroup :=
      total2 pdivisible.
    Definition pquasigroup_to_magma : pquasigroup → pmagma := pr1.
    Coercion pquasigroup_to_magma : pquasigroup >-> pmagma.
    Definition psemigroup :=
      total2 passociates.
    Definition psemigroup_to_magma : psemigroup → pmagma := pr1.
    Coercion psemigroup_to_magma : psemigroup >-> pmagma.

    Definition ploop := total2
      (pdivisible ∪ punital).
    Definition ploop_to_punitalmagma : ploop → punitalmagma.
      intro.
      induction X, pr2.
      exists pr1; assumption.
    Defined.
    Coercion ploop_to_punitalmagma : ploop >-> punitalmagma.

    Definition passociative_quasigroup := total2
      (pdivisible ∪ passociates).
    Definition passociative_quasigroup_to_psemigroup
      : passociative_quasigroup → psemigroup.
      intro.
      induction X, pr2.
      exists pr1; assumption.
    Defined.
    Coercion passociative_quasigroup_to_psemigroup
      : passociative_quasigroup >-> psemigroup.

    Definition pmonoid := total2
      (punital ∪ passociates).
    Definition pmonoid_to_unital_magma : pmonoid → punitalmagma.
      intro.
      induction X, pr2.
      exists pr1; assumption.
    Defined.
    Coercion pmonoid_to_unital_magma : pmonoid >-> punitalmagma.

    Definition pgroup := total2
      (punital ∪ passociates ∪ pdivisible).
    Definition pgroup_to_pmonoid : pgroup → pmonoid.
      intro.
      induction X, pr2.
      exists pr1; assumption.
    Defined.
    Coercion pgroup_to_pmonoid : pgroup >-> pmonoid.

    Notation 𝔤 := pgroup.
    Notation 𝔪 := pmonoid.

    Definition pinvertible (X : punitalmagma) : UU :=
      ∏ x : X, ∑ x' : X,
            (op X) x x' = 𝔢
          × (op X) x' x  = 𝔢.

    Theorem invertible_monoids_are_groups {X : 𝔪} :
      pinvertible X → pdivisible X.
    Proof.
      unfold pinvertible, pdivisible.
      unfold 𝔪 in X.
      intro.
      intros.
      pose proof X0 x.
      pose proof X0 y.
      unfold iscontr.
      assert (∑ z z' : (pr1 X), op (pr1 X) x z = y × op (pr1 X) z' x = y).
      exists (op (pr1 X) (pr1 X1) y).
      exists (op (pr1 X) y (pr1 X1)).
      split.
      induction X1, X2.
      simpl.
      induction X.
      simpl. simpl in pr2, pr3.
      induction pr2, pr3.
      induction pr5.
      rewrite pr8.
      rewrite pr2.
      induction pr5.
      unfold 𝔢.
      simpl.
      induction (pr9 y).
      assumption.
      induction X.
      induction pr2.
      simpl.
      rewrite <- (pr2 y _).
      induction X1.
      induction pr4.
      rewrite <- pr5.
      simpl.
      simpl in pr5.
      rewrite pr5.
      apply pr0.
      exists X3. intro.
      admit. (* could probably prove this but... *)
    Admitted.
   

Section prings.
  (* Predicative Rings *)
End prings.