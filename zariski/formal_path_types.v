Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Section AlgebraicDefinitions.
  Definition Family : UU :=
    ∑ X : UU, X -> UU.
  Definition familyset : Family -> UU := pr1.
  Coercion familyset : Family >-> UU.

  Definition familyfunction (fam : Family) : fam -> UU := pr2 fam.
  Coercion familyfunction : Family >-> Funclass.

  Definition simpleSumClosure :Family -> UU :=
    λ fam, ∏ X Y : fam,  ∑ Z : fam, fam Z = fam X ⨿ fam Y.
  Definition simpleSumCommutative : Family -> UU :=
    λ fam, ∏ X Y : fam, fam X ⨿ fam Y = fam Y ⨿ fam X.
  Lemma allFamiliesAreSimpleSumCommutative :
    ∏ fam : Family, simpleSumCommutative fam.
    intros.
    unfold simpleSumCommutative.
    intros.
    apply univalence.
    exact (weqcoprodcomm (fam X) (fam Y)).
  Defined.
  
  Definition simpleProductClosure :Family -> UU :=
    λ fam, ∏ X Y : fam,  ∑ Z : fam, fam Z = fam X × fam Y.
  Definition simpleProductCommutative : Family -> UU :=
    λ fam, ∏ X Y : fam, fam X × fam Y = fam Y × fam X.

  Lemma allFamiliesAreSimpleProductCommutative :
    ∏ fam : Family, simpleSumCommutative fam.
    intros.
    unfold simpleSumCommutative.
    intros.
    apply univalence.
    exact (weqcoprodcomm (fam X) (fam Y)).
  Defined.

  Definition familyDoesContain (X : UU) : Family -> UU :=
    λ fam, ∑ x : fam, fam x = X.

  Definition familyPrimeCondition : Family -> UU :=
    λ fam, ∏ x : fam, ∏ X : UU,
          ∑ y : fam, fam y = fam x × X. 

  Definition familyIsPrime : Family -> UU :=
    λ fam,
      familyPrimeCondition fam
        × simpleSumClosure fam.

  Example unitFamily : Family:=
    UU,, idfun UU.
  Example zeroFamily : Family:=
    unit,, λ _, ∅.
  Example Stn : Family :=
    nat,, stn.
  Example Stn_extended : Family.
  exists (nat ⨿ unit).
  intros.
  induction X.
  exact (stn a).
  exact nat.
  Defined.

  Definition Subfamily : UU :=
    ∑ FF : Family,
    ∑ subtype : FF -> UU,
        ∏ ff : FF, subtype ff -> FF ff.

  Definition ExtensionFamily : Subfamily -> Family := pr1.
  Definition Subfamily_function (sub : Subfamily) : ExtensionFamily sub -> UU.
    unfold ExtensionFamily.
    induction sub as[entire [function rest]].
    exact function.
  Defined.
  Definition Subfamily_family (sub : Subfamily)
    : Family.
    exists (ExtensionFamily sub).
    exact (Subfamily_function sub).
  Defined.
  Coercion Subfamily_family : Subfamily >-> Family. 
  (* This induces sortclass and funclass coercions *)

  Example zeroFamily_in_UnitFamily : Subfamily.
  exists unitFamily.
  exists (λ x, x).
  exact (λ _, λ X, X).
  Defined.

  Definition Subfamilies (FF : Family) : UU :=
    ∑ subtype : FF -> UU,
        ∏ ff : FF, subtype ff -> FF ff.
  Definition Subfamilies_to_subfamily {X : Family} :
    Subfamilies X -> Subfamily.
    intros.
    exists X.
    exact X0.
  Defined.
  Coercion Subfamilies_to_subfamily : Subfamilies >-> Subfamily.
  Definition Subfamily_to_subfamilies (sub : Subfamily) : Subfamilies (pr1 sub).
    exact (pr2 sub).
  Defined.
  Coercion Subfamily_to_subfamilies : Subfamily >-> Subfamilies.


  Definition SubfamiliesTrans {U : Family}
    (U0: Subfamilies U) (U1 : Subfamilies U0) :
    Subfamilies U.
    unfold Subfamilies.
    induction U1 as[U1family pathU1].
    induction U0 as[U0family pathU0].
    induction U as[Ufamily pathU].
    simpl in Ufamily, U0family, U1family.
    simpl in pathU1, pathU0, pathU.
    simpl.
    exists U1family.
    intros.
    apply pathU0.
    apply pathU1.
    assumption.
  Defined.

  Notation "X ⫃ Y" := (SubfamiliesTrans Y X) (at level 400).
  Definition UnitSubfamily (Z : Family) : Subfamilies Z.
    exists Z.
    intro z.
    apply idfun.
  Defined.
  Notation "⨃ Z" := (UnitSubfamily Z) (at level 400).

  Definition SubfamilyUnion {Z : Family} {Y : Subfamilies Z} :
       ∏ X X0 : Subfamilies Y, Subfamilies Y.
    intros X X0.
    unfold "⫃".
    simpl.
    unfold Subfamilies in X,X0.
    induction X as[f0 rest0].
    induction X0 as[f1 rest1].
    unfold Subfamilies.
    exists (λ x, f0 x ⨿ f1 x).
    intros.
    induction X.
    - apply rest0; assumption.
    - apply rest1; assumption.
  Defined.
  Notation "X ⊍ Y" := (SubfamilyUnion X Y) (at level 400). 

  Definition SubfamilyIntersection {Z : Family} {Y : Subfamilies Z} :
       ∏ X X0 : Subfamilies Y, Subfamilies Y.
    intros X X0.
    unfold Subfamilies.
    exists (λ x, X x ⨿ X0 x).
    intros.
    induction X1.
    - apply X; assumption.
    - apply X0; assumption.
  Defined.

  Notation "X ⩀ Y" := (SubfamilyIntersection X Y) (at level 400). 

  Check SubfamilyUnion.
  Definition isassoc_on_subfamilies {𝔘 : Family}
    (op : Subfamilies 𝔘 -> Subfamilies 𝔘 -> Subfamilies 𝔘) : UU :=
    ∏ 𝔘a 𝔘b 𝔘c: Subfamilies 𝔘, op (op 𝔘a 𝔘b) 𝔘c ≃ op 𝔘a (op 𝔘b 𝔘c).
  Definition iscomm_on_subfamilies {𝔘 : Family}
    (op : Subfamilies 𝔘 -> Subfamilies 𝔘 -> Subfamilies 𝔘) : UU :=
    ∏ 𝔘a 𝔘b: Subfamilies 𝔘, op 𝔘a 𝔘b ≃ op 𝔘b 𝔘a.
  Definition isabsorb_on_subfamilies {𝔘 : Family}
    (op1 : Subfamilies 𝔘 -> Subfamilies 𝔘 -> Subfamilies 𝔘) 
    (op2 : Subfamilies 𝔘 -> Subfamilies 𝔘 -> Subfamilies 𝔘) :=
    ∏ 𝔘a 𝔘b: Subfamilies 𝔘, op1 𝔘a (op2 𝔘a 𝔘b) ≃ 𝔘a.
  Lemma isassoc_SubfamilyUnion {𝔘 : Family} (𝔦: Subfamilies 𝔘)
    : isassoc_on_subfamilies (@SubfamilyUnion 𝔘 𝔦). 
    unfold isassoc_on_subfamilies.
    intros.
    apply idweq.
  Defined.
  Lemma isassoc_SubfamilyIntersection {𝔘 : Family} {𝔦: Subfamilies 𝔘} : isassoc_on_subfamilies (@SubfamilyIntersection 𝔘 𝔦).
    unfold isassoc_on_subfamilies.
    intros.
    apply idweq.
  Defined.
  Lemma iscomm_SubfamilyUnion {𝔘 : Family} {𝔦: Subfamilies 𝔘} : iscomm_on_subfamilies (@SubfamilyUnion 𝔘 𝔦).
    unfold iscomm_on_subfamilies.
    intros.
    apply idweq.
  Defined.

  Lemma iscomm_SubfamilyIntersection {𝔘 : Family} {𝔦: Subfamilies 𝔘} : iscomm_on_subfamilies (@SubfamilyIntersection 𝔘 𝔦).
    unfold iscomm_on_subfamilies.
    intros.
    apply idweq.
  Defined.

  Lemma isabsorb_Subfamily_minmax {Z Y} : isabsorb_on_subfamilies (@SubfamilyUnion Z Y) (@SubfamilyIntersection Z Y). 
    unfold isabsorb_on_subfamilies.
    intros.
    apply idweq.
  Defined.
  Lemma isabsorb_Subfamily_maxmin {Z Y} : isabsorb_on_subfamilies (@SubfamilyUnion Z Y) (@SubfamilyIntersection Z Y).
    unfold isabsorb_on_subfamilies.
    intros.
    apply idweq.
  Defined.
  
  Definition islattice_on_subfamilies {𝔘}
    (min max : Subfamilies 𝔘 -> Subfamilies 𝔘 -> Subfamilies 𝔘)
    : UU :=
  ((isassoc_on_subfamilies min) × (iscomm_on_subfamilies min))
    × ((isassoc_on_subfamilies max) × (iscomm_on_subfamilies max))
    × (isabsorb_on_subfamilies min max)
    × (isabsorb_on_subfamilies max min).

  Theorem subfamily_union_intersection_form_lattice {𝔘 𝔘0}
    : islattice_on_subfamilies (@SubfamilyUnion 𝔘 𝔘0) (@SubfamilyIntersection 𝔘 𝔘0).
    unfold islattice_on_subfamilies.
    split; repeat try split.
    - apply isassoc_SubfamilyUnion.
    - apply iscomm_SubfamilyUnion.
    - apply isassoc_SubfamilyIntersection.
    - apply iscomm_SubfamilyIntersection.
    - apply isabsorb_Subfamily_maxmin.
    - apply isabsorb_Subfamily_minmax.
  Defined.

  Definition members (fam: Family) : UU :=
    ∑ x : UU, ∑ x' : fam, x = fam x'.
  Definition type_of_member {fam : Family} : members fam -> UU :=
    pr1.
  Coercion type_of_member : members >-> UU.

  Section Cancellation.
    Definition ismultCancellative {U0 : Family} (X : members U0) : UU :=
      ∏ Y Y0 : members U0, 
                   (X × Y ≃ X × Y0) -> (Y ≃ Y0).
    Definition isaddCancellative {U0 : Family} (X : members U0) : UU :=
      ∏ Y Y0 : members U0, (X ⨿ Y ≃ X ⨿ Y0) -> (Y ≃ Y0).

    Definition make_unitFamily : UU -> unitFamily.
      apply idfun.
    Defined.
    Coercion make_unitFamily : UU >-> familyset.

    Definition themember {U0 : Family} (x : U0) : members U0.
      induction U0 as [scaffold arch].
      exists (arch x).
      exists x.
      apply idpath.
    Defined.

    Notation "$ x" := (themember x) (at level 50).

    Example nat_UU : unitFamily := ℕ.

    Lemma natnotcancellative_lemma000 : (ℕ ⨿ unit -> ℕ ⨿ ∅).
      intro.
      left.
      induction X.
      exact (S a).
      exact 0.
    Defined.
    Lemma natnotcancellative_lemma001 : (ℕ ⨿ unit <- ℕ ⨿ ∅).
      intro.
      induction X.
      induction a.
      right; exact tt.
      left; exact a.
      inversion b.
    Defined.
    Lemma natnotcancellative_sublemma000
      : ∏ y : ℕ ⨿ ∅,
          natnotcancellative_lemma000 (natnotcancellative_lemma001 y) = y.
      intro; induction y.
      - induction a; apply idpath.
      - inversion b.
    Defined.
    Lemma natnotcancellative_sublemma001
      : ∏ y : ℕ ⨿ unit,
          natnotcancellative_lemma001 (natnotcancellative_lemma000 y) = y.
      intro; induction y.
      - induction a; apply idpath.
      - induction b; apply idpath.
    Defined.
    Lemma natnotcancellative_lemma002 : (ℕ ⨿ unit ≃ ℕ ⨿ ∅).
      apply Equivalence_to_weq.
      exists natnotcancellative_lemma000.
      exists natnotcancellative_lemma001.
      unfold isEquivalence.
      exists natnotcancellative_sublemma000.
      exists natnotcancellative_sublemma001.
      intro.
      induction x.
      - induction a; apply idpath.
      - induction b; apply idpath.
    Defined.

    Lemma natfunnotmultcancellative_lemma000 {X : UU} : (ℕ -> X) -> (ℕ -> X) × X.
      intro ff; split.
      - exact (λ x, ff (S x)).
      - exact (ff 0).
    Defined.

    Definition infSum (X : UU) : UU := ℕ -> X.
    Notation "X ∞" := (infSum X) (at level 400). 

    Lemma natfunnotmultcancellative_lemma001 {X : UU} : (X ∞) <- (X ∞) × X.
      intro ff; induction ff as[ff ff0].
      intro n; induction n.
      - exact ff0.
      - exact (ff n).
    Defined.
    
    Lemma natfunnotmultcancellative_sublemma000 {X : UU}
      : ∏ y : (X ∞) × X,
          natfunnotmultcancellative_lemma000 (natfunnotmultcancellative_lemma001 y) = y.
      intro. apply idpath.
    Defined.

    Lemma natfunnotmultcancellative_sublemma001 {X : UU}
      : ∏ y : (X ∞),
          natfunnotmultcancellative_lemma001 (natfunnotmultcancellative_lemma000 y) = y.
      intro.
      apply funextfun.
      intro.
      induction x; apply idpath.
    Defined.
    Lemma natfunnotmultcancellative_extralemma {X : UU}
      : ∏ y : (X ∞), (∑ x : (X ∞) × X, natfunnotmultcancellative_lemma001 x = y).
      intro.
      exists (natfunnotmultcancellative_lemma000 y).
      apply funextfun.
      unfold homot.
      intro.
      induction x; apply idpath.
    Defined.

    Lemma natfunnotmultcancellative_lemma002 {X :UU} : (X ∞) × X ≃ (X ∞).
      exists natfunnotmultcancellative_lemma001.
      unfold isweq.
      intro.
      exists (natfunnotmultcancellative_extralemma _).
      intro.
      induction t.
      refine (total2_paths_f _ _).
      unfold transportf, constr1.
      Unshelve. Focus 2.
      - induction pr1.
        refine (total2_paths_f _ _).
        Unshelve. Focus 2.
        + apply funextfun.
          intro.
          rewrite <- pr2.
          apply idpath.
        + simpl.
          rewrite <- pr2.
          simpl.
          unfold transportf, funextfun.
          unfold funextfunImplication.
          unfold funextsec.
          unfold funextsecImplication.
          unfold make_weq.
          unfold invmap, constr1.
          unfold toforallpaths.
          unfold hfiberpr1.
          unfold paths_rect.
          simpl.
          unfold weqccontrhfiber.
          unfold iscontrpr1.
          simpl.
          unfold Preamble.pr1.
          unfold maponpaths.
          unfold paths_rect.


      
      exists natfunnotmultcancellative_lemma000.
      unfold isEquivalence.
      exists natfunnotmultcancellative_sublemma001.
      exists natfunnotmultcancellative_sublemma000.
      intro.
      induction x.
      simpl.
      unfold natfunnotmultcancellative_sublemma000.
      unfold natfunnotmultcancellative_sublemma001.
      unfold natfunnotmultcancellative_lemma000.
      unfold natfunnotmultcancellative_lemma001.
      simpl.
      unfold nat_rect.
      - induction a; apply idpath.
      - induction b; apply idpath.
    Defined.

    Example natfuntype_not_add_cancellative {X : UU}
      : (isaddCancellative ($ (X ∞))) -> ∅.
    unfold isaddCancellative.
    intro Y.
    pose proof (Y ($ X) ($ ∅)).
    assert ($ (X ∞) ⨿ ($ X) ≃ $ (X ∞)).
    - simpl.
      
    Example nattype_not_add_cancellative
      : (isaddCancellative ($ ℕ)) -> ∅.
    unfold isaddCancellative.
    intro.
    pose proof (X ($ unit) ($ ∅)).
    simpl in X0.
    pose proof (X0 natnotcancellative_lemma002). 
    apply X1. exact tt.
    Defined.  

    Example nattype_not_mult_cancellative
      : (ismultCancellative ($ ℕ)) -> ∅.
    unfold ismultCancellative.
    intro.
    pose proof (X ($ unit) ($ ∅)).
    simpl in X0.
    pose proof (X0 natnotcancellative_lemma002). 
    apply X1. exact tt.
    Defined.  

    Example infinite_sum_not_add_cancellative
    
  End Cancellation.
            

Section FormalPathTypes.
End FormalPathTypes.
