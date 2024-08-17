Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Section Families.
  Definition Family : UU := ∑ X : UU, X → UU.
  Definition Base (𝐗 : Family) : UU := pr1 𝐗.
  Definition Familymap {𝐗 : Family} : Base 𝐗 → UU := pr2 𝐗.
  Coercion Familymap : Family >-> Funclass.
  Definition Incidences (𝐗 : Family) : UU := ∑ x : Base 𝐗,𝐗 x. 
  Coercion Incidences : Family >-> UU.
  Notation "⟟ X" := (Incidences X) (at level 100).
  Definition Fiber {𝐗 : Family} (x : Base 𝐗) : UU := 𝐗 x.
  Coercion Fiber : Base >-> UU.
  Notation "⨏" := (Fiber) (at level 300).
  Definition PositiveFSection (𝐗 : Family) : UU := ∏ x : Base 𝐗, x. 
  Definition FSection (𝐗 : Family) : UU := ∏ x : Base 𝐗, x ⨿ (x → ∅). 
  Definition FIsTrivial (𝐗 : Family) : UU := ∏ x y : Base 𝐗, Fiber x = Fiber y.
End Families.

Section TruthValues.
  Definition Roots (𝐗 : Family) : UU := ∑ x : Base 𝐗, x → ∅.
  Notation 𝐙 := Roots.
  Definition ClassifyingSpace : UU := ∑ 𝐋 : Family, 𝐙 𝐋. 
  Definition ClassifyingSpace_to_Family : ClassifyingSpace → Family := pr1.
  Coercion ClassifyingSpace_to_Family : ClassifyingSpace >-> Family.
  Definition FFalse {𝐋 : ClassifyingSpace} : Base 𝐋 := pr1 (pr2 𝐋).
  (* \msanszero *)
  Notation "𝟢" := FFalse.
  Definition PointedFamily : UU := ∑ 𝐗 : Family, ∑ x : Base 𝐗, x. 
  Example OnlyZero : ClassifyingSpace.
  exists (unit,, λ _, ∅). exists tt.
  apply fromempty.
  Defined.

  Example OnlyUnit : PointedFamily.
  exists (unit,, λ _, unit). exists tt.
  exact tt.
  Defined.

  Example UUFam : Family := UU,, idfun UU.
  (* The "identity" family UU → UU *)
  Example UUF : ClassifyingSpace.
    exists UUFam. exact (∅,, fromempty).
  Defined.
  Notation 𝐔𝐔 := UUF.
  Example PathsFam : Family := UU,, λ x, x=x.
  Example PPF : PointedFamily.
  exists PathsFam. exact (∅,, idpath ∅).
  Defined.
  Notation 𝛖 := PPF.
  Example HPropFam : Family := hProp,, pr1.
  Example HPropF : ClassifyingSpace := HPropFam,, (hfalse,, idfun ∅).
  Notation ℙ := HPropF.
End TruthValues.

Section Predicates.
  Definition BaseOperator (𝐅 : Family) := Base 𝐅 → Base 𝐅 → Base 𝐅.
  (*
   The points of the base space are like elements of a set .  The fiber at such
a point intros  the type of proofs (might be empty!) that the element intros  in the "set ".
 From a proof that x and y are in the family (their fibers are inhabited)
       one may obtain a proof that their image under some base operation is  inhabited,then that is the definition of closure.
    Prototypically, the base space intros  UU or UU × UU or some expression like that.
   *) 
  Definition isclosedoperator {𝐅 : Family} (BOp : BaseOperator 𝐅) : UU :=
    ∏ x y : Base 𝐅, x → y → BOp x y.
  Definition operatorhasleftunit  {𝐅 : Family} (BOp : BaseOperator 𝐅) : UU :=
    ∑ x : Base 𝐅, ∏ y : Base 𝐅, BOp x y = y.
  Definition operatorhasrightunit  {𝐅 : Family} (BOp : BaseOperator 𝐅) : UU :=
    ∑ x : Base 𝐅, ∏ y : Base 𝐅, BOp y x = y.
  Definition operatorhasunit  {𝐅 : Family} (BOp : BaseOperator 𝐅) : UU :=
    ∑ x : Base 𝐅, ∏ y : Base 𝐅, (BOp x y = y) × (BOp y x = y).

  Definition Fmonoid : UU :=
    ∑ 𝐅: Family, ∑ BOp : BaseOperator 𝐅, isclosedoperator BOp × operatorhasunit BOp.
  Definition Fmonoid_to_family : Fmonoid → Family := pr1.
  Coercion Fmonoid_to_family : Fmonoid >-> Family.
  Definition Fmonoid_to_operator {𝐌 : Fmonoid} : BaseOperator 𝐌 := pr1 (pr2 𝐌).
  Coercion Fmonoid_to_operator : Fmonoid >-> BaseOperator.
  Notation "x + y" := (Fmonoid_to_operator x y).
  
Notation "x * y" := (Fmonoid_to_operator x y).
  Definition Fmonoid_to_closedness (𝐌 : Fmonoid) : isclosedoperator 𝐌 := pr1 (pr2 (pr2 𝐌)).
  Coercion Fmonoid_to_closedness : Fmonoid >-> isclosedoperator.
  Definition Fmonoid_to_hasunit (𝐌 : Fmonoid) : operatorhasunit 𝐌 := pr2 (pr2 (pr2 𝐌)).
  Coercion Fmonoid_to_hasunit : Fmonoid >-> operatorhasunit.
  (* These coercions mean we can just apply a monoid to prove basic things *) 
  Definition Fmonoid_unit {𝐌 : Fmonoid} : Base 𝐌.
    induction 𝐌.
    repeat induction pr2.
    induction pr3.
    assumption.
  Defined.
  Notation F0 := Fmonoid_unit.
  Notation F1 := Fmonoid_unit.

  Definition Fmonoid_isgroup  (𝐌 : Fmonoid) : UU :=
    ∏ x : Base 𝐌, ∑ y : Base 𝐌, (x + y = F0) × (y + x = F0).

  Definition Fgroup : UU :=
    ∑ 𝐆 : Fmonoid, Fmonoid_isgroup 𝐆.
  Definition Fgroup_to_Fmonoid : Fgroup → Fmonoid := pr1.
  Coercion Fgroup_to_Fmonoid : Fgroup >-> Fmonoid.

  Example Propositions_Under_Conjugation : Fmonoid.
  exists HPropF. exists (λ x y, hconj x y).
  split.
  - unfold isclosedoperator. intros . split; assumption.
  - unfold operatorhasunit. exists htrue. intros . unfold hconj. simpl. unfold make_hProp, isapropdirprod, isapropunit. split. induction y. simpl. unfold isofhleveldirprod.
    pose proof weqtodirprodwithunit pr1.
    apply univalence in X.
    pose proof weqdirprodcomm pr1 unit.
    apply univalence in X0.
    refine (total2_paths_f _ _).
    simpl.
    Focus 2.
    induction y.
    simpl.
    refine (total2_paths_f _ _).
    simpl.
    Unshelve.
    Focus 2.
    simpl.
    rewrite <- X0.
    symmetry; assumption.
    simpl.
    Focus 2.
    simpl.
    pose proof weqtodirprodwithunit pr1.
    symmetry; apply univalence; assumption.
    simpl.
    pose proof (isapropisaprop pr1) (transportf isaprop
    match
      pr11 (univalenceAxiom pr1 (pr1 × unit) (weqtodirprodwithunit pr1)) in (_ = u)
      return (u = pr1)
    with
    | idpath _ => idpath pr1
    end (isofhleveldirprod 1 pr1 unit pr2 iscontrpathsinunit)).
    unfold isaprop in X.
    unfold isofhlevel in X.
    pose proof X pr2.
    induction X0.
    assumption.
    simpl.
    pose proof (isapropisaprop pr1) pr2 (transportf isaprop
    (internal_paths_rew UU (pr1 × unit) (λ u : UU, u = pr1)
       match X in (_ = u) return (u = pr1) with
       | idpath _ => idpath pr1
       end (unit × pr1) X0)
    (isofhleveltotal2 1 (λ _ : unit, pr1) iscontrpathsinunit (λ _ : unit, pr2))).
    induction X1.
    symmetry.
    assumption.
    Defined.

  Lemma copy {X : UU} : X → X × X. split; assumption. Defined.
  Example Types_Under_Coproduct : Fmonoid.
  exists UUF. exists (λ x y, x ⨿ y).
  split.
  - left; assumption.
  - exists ∅. 
    intro.
    pose proof (weqcoprodcomm y ∅).
    apply univalence in X.
    rewrite X.
    clear X.
    apply copy.
    apply univalence. apply Equivalence_to_weq.
    refine (_,, _,, _,, _).
    Unshelve. Focus 3.
    intro. right; assumption.
    Focus 2. intro. induction X; try contradiction; try assumption.
    simpl.
    Unshelve. 
    Focus 2. apply idpath.
    simpl.
    refine (_,, _).
    intros. induction x; try contradiction.
    simpl.
    + 
      unfold Base, UUF in y.
      simpl in y. simpl.
      unfold empty_rect, coprod_rect.
      unfold maponpaths.
      unfold paths_rect.
      simpl.
      Unshelve. Focus 2.
      intro x. induction x; try contradiction.
      simpl. apply idpath.
      simpl. apply idpath.
  Defined.


  Example Types_Under_Product : Fmonoid.
  exists UUF. exists (λ x y, x × y).
  split.
  - split; assumption.
  - exists unit. simpl. intro y.
    pose proof (weqdirprodcomm unit y).
    apply univalence in X.
    rewrite X. apply copy.
    apply univalence.
    exists pr1.
    unfold isweq.
    intro. unfold iscontr, hfiber.
    refine (_,, _).
    Unshelve.
    2: {
      exists (y0,, tt). apply idpath.
      }
      intros .
    refine (total2_paths_f _ _).
    unfold transportf.
    simpl.
    Unshelve. 2: {
              
              

              simpl.
              induction t.
              simpl.
              induction pr1.
              simpl in pr2.
              rewrite pr2. induction pr0.
              apply idpath.
            }
            simpl.
    unfold constr1, internal_paths_rew_r .
    unfold unit_rect, paths_rect.
    simpl.
    induction t.
    simpl.
    induction pr1.
    simpl in pr2.
    rewrite pr2.
    induction pr0.
    simpl.
    apply idpath.
  Defined.


