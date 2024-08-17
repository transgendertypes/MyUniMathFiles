(* There is a write up which goes along with this file.  The contents
are similar to the file "types over rings" and there is much overlap.
The notation is intended to allow more polymorphism than typedoverrings.v
and to better match the write-up (forthcoming) about bricolages, schemes
of types, etc. *)

Section PreBricolage.
  Require Import UniMath.Foundations.Preamble.

  (* Type this using \lfbowtie in agda input mode *)
  Notation "⧑ x" := (pr1 x) (at level 400).
  (* Type this using \rfbowtie in agda input mode *)
  Notation "⧒ x" := (pr2 x) (at level 400).
  (* Type this using \bowtie in agda input mode *)
  Notation "⋈ x" := (pr2 x,, pr1 x) (at level 400).

  Require Import UniMath.Foundations.PartA.
  (* incidence *)
  (* Type this using \mitI in agda input mode *)
  Definition 𝐼 (x y : UU) := ((x × y) -> UU). 
  Definition Style := 𝐼 UU UU.
  Definition Style_function : Style -> (UU -> UU -> UU).
    intro. exact (curry X).
  Defined.
  Coercion Style_function : Style >-> Funclass.
  
  Definition PathStyle : Style.
    exact (λ x, (⧑ x) = (⧒ x)).
  Defined.

  Require Import UniMath.Foundations.All.
  Definition pathtype := image (PathStyle).
  Definition make_pathtype (x y : UU) : pathtype.
    exists (x = y).
    unfold ishinh, hfiber, ishinh_UU.
    simpl.
    intros.
    apply X.
    exists (x,,y).
    apply idpath.
  Defined.
  (* Type this using \minus in agda input mode *)
  Notation "x − y" := (make_pathtype x y) (at level 400).
  Check (unit − unit).

  Definition topathtype (x : UU) : pathtype :=
    make_pathtype x ∅.
  Coercion topathtype : UU >-> pathtype.
  Definition astype_ofpaths (x : pathtype) : UU :=
    (⧑ x).
  Coercion astype_ofpaths : pathtype >-> UU.
  (* note that these coercions are "adjoint" (at least in some loose sense)
     but not inverses *)
  Notation "♓" := topathtype.

  (* zero is  ∅ = ∅ *)
  Definition zero : pathtype := ∅.
  Example zeropath : zero := idpath ∅.
  (* uncomment these instructions and step through if this seems impossible *)
  (* all the apparent strangeness is  just notation / coercion *)

  (* unfold zero.
  unfold "♓".
  unfold "−".
  simpl.
  exact (idpath ∅).
  Defined.
   *)



  (* one is  unit = ∅ *)
  Definition one : pathtype := unit.
  Example onepath_will_abort : one.
  unfold one, "♓", "−". simpl.
  (* of course this is  impossible. *)
  Abort.

  (* the definition is kind of interesting.  The negation of auto pathtype is
     just its involution.  Since any path type is  equal its involution
     up to univalence, neg x = x up to a path, yet neg (neg x) is reflexively equal x *) 
  (* We're going to define a "bricolage" in order to make sense of the described "ring "*)
  Definition neg : pathtype -> pathtype.
    unfold pathtype, image, ishinh, hfiber, ishinh_UU.
    simpl.
    intro.
    induction X.
    exists pr1.
    intros.
    apply pr2.
    intros.
    apply X.
    induction X0 as [xy path].
    exists (⋈ xy).
    rewrite <- path.
    unfold PathStyle.
    induction xy.
    simpl.
    apply univalence.
    exact (weqpathsinv0 _ _).
  Defined.

  Definition pathtype_presum : UU -> UU -> pathtype :=
    λ x y, ♓ (x ⨿ y).
  Notation "x +++ y" := (pathtype_presum x y) (at level 300).

  Definition isweakly_zero (x : pathtype) : UU := zero -> x.
  Notation "x ⩵ 0" := (isweakly_zero x) (at level 300).
  Definition isweakly_nonzero (x : pathtype) : UU := x -> one.
  Notation "x !⩵ 0" := (isweakly_nonzero x) (at level 300).

  Axiom zero_equals_unit : iscontr (zero : UU).
  Definition zero_assumed_equal_unit : (zero : UU) = unit.
    apply univalence.
    exists (λ _, tt).
    unfold isweq, iscontr, hfiber.
    intros.
    induction y.
    exists (idpath ∅,, idpath tt).
    intro.
    induction t.
    simpl.
    refine (total2_paths_f _ _).
    unfold transportf.
    simpl.
    unfold constr1, paths_rect, maponpaths.
    simpl.
    Unshelve. Focus 2.
    simpl.
    induction (zero_equals_unit).
    rewrite (pr3 pr1).
    rewrite (pr3 (idpath ∅)).
    exact (idpath pr0).
    simpl.
    unfold internal_paths_rew_r, paths_rect.
    simpl.
    apply (isasetunit tt tt).
  Defined.

  Theorem negative_types_theorem : ∏ x : UU, ((x − x) ⩵ 0).
    unfold isweakly_zero, "−".
    intros; simpl.
    exact (idpath x).
  Defined.

  Theorem zero_types_theorem : ∏ x : UU, ((x − one) ⩵ 0) -> (x ⩵ 0).
    unfold isweakly_zero, "−", "♓".
    simpl.
    simpl; intros.
    rewrite (X X0).
    symmetry.
    apply univalence.
    exists (fromempty).
    unfold isweq, fromempty.
    intro.
    pose proof tt.
    rewrite y in X1.
    contradiction.
  Defined.


  (* this is kind of nice, but can't we do better? *)
  Section Tension.
  Definition tension := UU × UU .
  Definition make_tension (x y : UU) : tension :=
    x,, y.

  Notation "x - y" := (make_tension x y).
  
  (* \tau in agda input mode *)
  Definition τ : tension -> UU.
    intro X; induction X.
    exact (pr1 = pr2).
  Defined.
  Coercion τ : tension >-> UU.
  (* \taurus in agda input mode *)
  Definition type_to_tension : UU -> tension :=
    λ x, x,, ∅.
  Coercion type_to_tension : UU >-> tension.
  Notation "♉" := type_to_tension.

  Definition tension_equals : tension -> tension -> tension.
    intros.
    exact (X - X0).
  Defined.
  Notation "X ≖ Y" := (tension_equals X Y) (at level 400).

  Definition tension_sum : binop tension.
    unfold binop; intros x y; induction x as [x x']; induction y as [y y'].
    exact (x ⨿ y,, x' ⨿ y').
  Defined.

  (* input using \pluseqq but please read as a "summation of path types" *)
  Notation "p1 ⩲ p2" := (tension_sum p1 p2) (at level 50).
  Theorem tension_sum_is_weak_product (p1 p2 : tension) :
    p1 × p2 -> (p1 ⩲ p2).
    unfold τ, "⩲".
    simpl. intro. induction X as [ pp1 pp2 ].
    rewrite pp1. rewrite pp2.
    apply idpath.
  Defined.

  Definition tension_product : binop tension.
    unfold binop; intros x y; induction x as [x x']; induction y as [y y'].
    (* (x - x')(y - y') = xy + x'y' - x'y - xy' *)
    exact (((x × y) ⨿ (x' × y')) - ((x' × y) ⨿ (x × y'))).
  Defined.
  Notation "x ⨱ y" := (tension_product x y) (at level 250).

  Lemma subtraction_product_theorem : ∏ x y : UU,
        ((x - x) ⨱ y).
    intros.
    apply idpath.
  Defined.

  Theorem tension_product_is_weak_coproduct (p1 p2 : tension) :
    p1 ⨿ p2 -> (p1 ⨱ p2).
    intros. induction X as [ pp1 | pp2 ].
   (* unfold "⨱", "-", τ.*)
    induction p1 as [x x'].
    (* unfold τ in pp1. *)
    rewrite pp1.
    apply idpath.
    unfold "⨱", "-", τ.
    induction p2 as [y y'].
    unfold τ in pp2.
    rewrite  pp2.
    apply univalence.
    apply weqcoprodcomm.
  Defined.

  Require Import UniMath.Combinatorics.StandardFiniteSets.
  Coercion stn : nat >-> Sortclass.
  Example affine1 : UU := 1 -> tension.
  Example affine (n: nat) : UU := n -> tension. 
  Definition affine1_to_tension : affine1 -> tension := λ x, x firstelement.
  Coercion affine1_to_tension : affine1 >-> tension.
  Definition affine1_to_type (af : affine1) : UU.
    exact (af firstelement). 
  Defined.
  Coercion affine1_to_type : affine1 >-> UU.
  Definition affine_axis {n: nat} (n' : n)
                               : affine n -> tension
    := λ x, x n'.

  (* Notice that these three examples are entirely different types *)
  Example linear_variety_one_variable_tension (α β : tension) :=
    ∑ x : tension, ((α ⨱ x) − β).
  Example linear_variety_one_variable_UU (α β : tension) :=
    ∑ x : UU, ((α × x) − β).
  Example linear_variety_one_variable_tension_axis (α β : tension) :=
    ∑ x : UU, ((α ⨱ x) − β).
  Example stn_0_2 : 2.
  exists 0.
  unfold natlth.
  unfold natgth.
  simpl.
  apply idpath.
  Defined.

  Definition e0 {n} : S n.
    exists 0.
    unfold natlth, natgth; simpl.
    apply idpath.
  Defined.
  Definition e1 {n} : S (S n).
    exists 1.
  unfold natlth, natgth; simpl.
  apply idpath.
  Defined.
  Definition e2 {n} : S (S (S n)).
    exists 2.
  unfold natlth, natgth; simpl.
  apply idpath.
  Defined.
  Definition e3 {n} : S (S (S (S n))).
    exists 3.
  unfold natlth, natgth; simpl.
  apply idpath.
  Defined.

  (*  α x = β y *)
  Example ratio_two_tensions (α β : tension) :=
    ∑ x : affine 2, ((α ⨱ (x e0)) − (β ⨱ (x e1))).
  Example ratio_two_types (α β : UU) :=
    ∑ x y : UU , ((α × x) − (β × y)).

  Example x_twice_y := ratio_two_types 1 2.
  Example bool_twice_unit : x_twice_y.
  exists bool. exists unit.
  assert (bool = 2).
  - symmetry.
    apply univalence.
    exact weqstn2tobool.
  - rewrite X.
    assert (unit = 1).
    + symmetry. apply univalence.
      exact weqstn1tounit.
    + rewrite X0.
      apply univalence.
      apply weqdirprodcomm.
  Defined.
  Lemma unit_equals_1: unit = 1.
    symmetry.
    apply univalence.
    exact weqstn1tounit.
  Defined.
  Lemma one_times_x_equals_x (x : UU) : (1 × x) = x.
    rewrite <- unit_equals_1.
    apply univalence.
    exists pr2.
    unfold isweq, iscontr, hfiber.
    intros.
    exists ((tt,,y),, (idpath y)).
    intros.
    induction t.
    induction pr1.
    induction pr1.
    simpl in pr2.
    rewrite pr2.
    apply idpath.
  Defined.
    
  Example nat_twice_nat : x_twice_y.
  exists nat.
  exists nat.
  apply univalence.
  simpl.
  rewrite one_times_x_equals_x.
  (* exists (λ n, natdivrem n 2). *)
  (* skipping the proof, since this is just an illustrative example *)
  Admitted.

  Section SubUniverse.
    (* For  us, a universe isa "subuniverse" of UU,
     and we are interested in proof-relevant notions
     of sub-universe, so that it is not necessarily a mere proposition
     whether such and such auto type belongs to a universe.*)
    Definition Universe := UU -> UU.
    Definition isCoprodUniverse (uu : Universe) : UU :=
      ∏ x y : UU, uu x -> uu y -> uu (x ⨿ y).
    Definition isDirprodUniverse (uu : Universe) : UU :=
      ∏ x y : UU, uu x -> uu y -> uu (x × y).
    Definition isProdIdealUniverse (uu : Universe)
      : UU := ∏ x y : UU, uu x -> y -> uu (x × y).
    Definition ishPropertiedUniverse (uu : Universe) : UU :=
      ∏ x: UU, uu x -> uu (x -> hProp).
    Definition isLevelPropertiedUniverse (uu : Universe) (n : nat) : UU :=
      ∏ x: UU, uu x -> uu (x -> HLevel n).
    Definition hasIncidencehStructures (uu : Universe) : UU :=
      ∏ x y : UU, uu x -> uu y -> uu (x -> y -> hProp).
    Definition hasIncidenceStructures (uu : Universe) : UU :=
      ∏ x y : UU, uu x -> uu y -> uu (x -> y -> UU).
    Definition isFunctionUniverse (uu : Universe) : UU :=
      ∏ x y : UU, uu x -> uu y -> uu (x -> y).
    Definition isPathtypeUniverse0 (uu : Universe) : UU :=
      ∏ x y : UU, uu x -> uu y -> uu (x = y).
    Definition isPathtypeUniverse1 (uu : Universe) : UU :=
      ∏ x : UU, uu x -> ∏ xx xx' : x, uu (xx = xx').
    Definition isSigmaUniverse (uu : Universe) : UU :=
      ∏ x : UU, uu x -> 
                  ∏ ff : x -> UU,
            (∏ xx : x, uu (ff xx)) -> uu (∑ xx : x, ff xx).
    Definition isPiUniverse (uu : Universe) : UU :=
      ∏ x : UU, uu x -> 
                  ∏ ff : x -> UU,
            (∏ xx : x, uu (ff xx)) -> uu (∏ xx : x, ff xx).

    (* See also SpecUU below *)
    Definition isPrimeUniverse (uu : Universe) : UU :=
      ∏ x y : UU, uu (x × y) -> (uu x) ⨿ (uu y).

    Definition isNotNotPrimeUniverse (uu : Universe) : UU :=
      ∏ x y : UU, uu (x × y) -> (((uu x) ⨿ (uu y)) -> ∅) -> ∅.

    Definition hasUniverse_empty (uu : Universe) : UU :=
      uu empty.
    Definition hasUniverse_unit (uu : Universe) : UU :=
      uu unit.
    Require Import UniMath.SyntheticHomotopyTheory.Circle.
    Definition hasUniverse_circle (uu : Universe) : UU :=
      uu (pr1 circle).
    Definition hasUniverse_naturalnumbers (uu : Universe)
      : UU :=
      uu nat. 

    Definition IdealUniverse : UU :=
      ∑ uu : Universe,
      isCoprodUniverse uu
    × isProdIdealUniverse uu.

    Definition ProperIdealUniverse : UU :=
      ∑ uu : Universe,
      isCoprodUniverse uu
    × isProdIdealUniverse uu
    × ∑ X : UU, uu X -> ∅.

    (* bear with me, it will get more formal *)
    Definition SpecUU : UU :=
      ∑ uu : Universe,
          isCoprodUniverse uu
        × isProdIdealUniverse uu
        × isPrimeUniverse uu

        × ∑ X : UU, uu X -> ∅.
    Definition NotNotSpecUU : UU :=
      ∑ uu : Universe,
          isCoprodUniverse uu
        × isProdIdealUniverse uu
        × isNotNotPrimeUniverse uu
        × ∑ X : UU, uu X -> ∅.

    Example zeroIdeal : SpecUU.
      exists (λ x, x -> ∅).
      split; try split.
    - unfold isCoprodUniverse.
      intros x y x0 y0.
      intro cop.
      induction cop.
      exact (x0 a).
      exact (y0 b).
    - unfold isProdIdealUniverse.
      intros.
      apply X.
      exact (pr1 X1).
    - split.
      + unfold isPrimeUniverse.
        intros.
        Abort.
    (* this version of de morgan's law is unprovable. *)
    Example zeroIdeal : NotNotSpecUU.
      exists (λ x, x -> ∅).
      split; try split.
    - unfold isCoprodUniverse.
      intros x y x0 y0.
      intro cop.
      induction cop.
      exact (x0 a).
      exact (y0 b).
    - unfold isProdIdealUniverse.
      intros.
      apply X.
      exact (pr1 X1).
    - split.
      + unfold isNotNotPrimeUniverse.
        intros.
        apply X0.
        left.
        intro.
        apply X0.
        right.
        intro.
        apply X.
        split; assumption.
      + exists unit.
        intros.
        apply X; exact tt.
    Defined.

    Example hSetideal : SpecUU.
    exists (λ x, isaset x).
    split; try split.
    - unfold isCoprodUniverse.
      intros x y x0 y0.
      exact (isasetcoprod x y x0 y0).
    - unfold isProdIdealUniverse.
      intros x y x0.
    Abort. (* this is  clearly false *)

    (* The idea is  that the product of any x y of HLevel n is of
     hlevel n.  It follows that the hlevels are multiplicatively closed
     subuniverses.  What ought to follow is some version of the statement
     that "the subuniverse of types *not* of some hlevel is a "prime ideal"
     There are more prime ideals; for example, the collection of types which
     are *not* a set of cardinality less than some infinite cardinal λ is a "prime ideal" since the
      product of any such sets is such a set of cardinality greater than or equal to λ
      or is not a set .
      Though enumerating these ideals is elementary for sets, the case of
      groupoids is already interesting.  Essentially, we have a Zariski topology
which degenerates to the order topology on the infinite cardinals (viewed as a privileged copy of the ordinal numbers) but which partially orders the groupoids (in the sense that any topology gives way to a partial order).  The homotopy levels give another copy of the ordinal numbers as a very coarse topology "over" the entire zariski structure.  
     *) 
    (* The prime ideal of inhabited types *)
    Example nonemptyIdeal : SpecUU.
    exists (λ x, x).
    split; try split.
    - unfold isCoprodUniverse.
      intros x y xx yy.
      left; exact xx.
    - unfold isProdIdealUniverse.
      intros x y xx yy.
      exact (xx,, yy).
    - split.
      + unfold isPrimeUniverse.
        intros x y xy.
        left. exact (pr1 xy).
      + exists ∅.
        exact fromempty.
    Defined.

    (* the "not not prime" ideal of types which are not hProps *)
    Example hPropideal : NotNotSpecUU.
    exists (λ x, ∑ xx xx' : x, xx = xx' -> ∅).
    split; try split.
    - unfold isCoprodUniverse.
      intros x y x0 y0.
      induction x0 as [xx [xx' restx]].
      induction y0 as [yy [yy' resty]].
      exists (inl xx).
      exists (inl xx').
      intro X.
      pose proof (ii1_injectivity (Q:=y) xx xx' X).
      exact (restx X0).
    - unfold isProdIdealUniverse.
      intros x y X yy.
      induction X as[xx [xx' restx]].
      exists (xx,,yy). exists (xx',,yy).
      intros.
      apply base_paths in X.
      simpl in X.
      exact (restx X).
    - split.
      + unfold isNotNotPrimeUniverse.
        intros x y [xy [xy' rest]].
        induction xy as [xx yy].
        induction xy' as [xx' yy'].
        intros.
        apply X.
        left.
        exists (xx). exists (xx').
        intro xpath.
        apply X.
        right.
        exists (yy). exists (yy').
        intro ypath.
        apply rest.
        rewrite xpath. rewrite ypath.
        apply idpath.
      + exists unit.
        intros.
        induction X.
        induction pr2.
        induction pr1,pr0.
        apply pr2, idpath.
    Defined.

    Definition weaken_SpecUU : SpecUU -> NotNotSpecUU.
      intros.
      induction X.
      exists pr1.
      induction pr2.
      induction pr2.
      induction pr3.
      split; try split; try assumption.
      split; try assumption.
      unfold isNotNotPrimeUniverse.
      intros.
      unfold isPrimeUniverse in pr3.
      pose proof (pr3 x y).
      pose proof (X1 X).
      exact (X0 X2).
    Defined.
    Coercion weaken_SpecUU : SpecUU >-> NotNotSpecUU.

    Example nonunital_ideal : NotNotSpecUU.
    exists (λ x, (iscontr x) -> ∅).
    split; try split.
    - unfold isCoprodUniverse, iscontr.
      intros x y x0 y0 xy.
      induction xy as [cntr proof].
      induction cntr.
      + apply x0.
        exists a.
        intro witness.
        pose proof (proof (inl witness)).
        exact (ii1_injectivity (Q:=y) witness a X).
      + apply y0.
        exists b.
        intro witness.
        pose proof (proof (inr witness)).
        exact (ii2_injectivity (P:=x) witness b X).
    - unfold isProdIdealUniverse.
      intros.
    Abort. (* This condition fails because x may be taken empty *) 
    (* So, HLevel 0 is not a zariski open set. *)

    Require Import UniMath.Combinatorics.FiniteSets.
    Lemma isfinite_coprod_inverseproblem { X Y }
      : isfinite (X ⨿ Y) -> isfinite X.
      unfold isfinite, ishinh, ishinh_UU, make_hProp.
      simpl.
      intros.
      pose proof X0 P.
      clear X0.
      apply X2.
      intro.
      apply X1.
      clear X1. clear X2. clear P.
      rename X0 into premise.
      unfold finstruct in premise.
      induction premise as[n struct].
      unfold nelstruct in struct.
      unfold finstruct.
    Abort. 
    Example transfinite_ideal : NotNotSpecUU.
    exists (λ x, isfinite x -> ∅).
    split; try split.
    - unfold isCoprodUniverse, isfinite, finstruct, nelstruct.
      intros x y xinf yinf xyfinite.
      Abort.
  
  
      
    

    


    Example finiteSetsIdeal : SpecUU :=
      
         
    
    
    End SubUniverse.
  
  Section PreBricolageOnAMonoid.
    Require Import UniMath.Algebra.Monoids.
    Section ScaffoldMonoid.
      Context (_monoid : monoid).
      Notation "♂" := _monoid.
      Context (_arch : ♂ -> UU).
      Notation "♀" := _arch.

      Definition StagedMonoid : UU :=
        ∑ (α : monoid), α -> UU.
      Definition make_StagedMonoid : StagedMonoid
        := ♂,, ♀. 

      (* Type this using \stigma in agda input mode *)
      Context (ϛ : StagedMonoid).

      Definition scaffold : monoid
        := (⧑ ϛ).
      Definition arch : scaffold -> UU
        := (⧒ ϛ).
      End ScaffoldMonoid.

      (* Type this using \scorpio in agda input mode *)
      Notation "♏" := scaffold.
      (* Type this using \aries in agda input mode *)
      Notation "♈" := arch.

      Coercion scaffold : StagedMonoid >-> monoid.
      Coercion arch : StagedMonoid >-> Funclass.

      Section StyledMonoid.
        Example coproduct : Style := λ x y, (x ⨿ y).
        Example product : Style := λ x y, (x × y).
        Example equals : Style := λ x y, (x = y).

        Context (star : Style).
      (* Type this using \star in agda input mode *)
        Notation "⋆" := star.
        
        Definition StyledMonoid : UU :=
          StagedMonoid × Style.
        Definition StyledMonoid_to_StagedMonoid : StyledMonoid -> StagedMonoid.
          intro. exact (⧑ X).
        Defined.
        Definition StyledMonoid_to_Style : StyledMonoid -> Style.
          intro. exact (⧒ X).
        Defined.
        Coercion StyledMonoid_to_Style : StyledMonoid >-> Style.
        Coercion StyledMonoid_to_StagedMonoid : StyledMonoid >-> StagedMonoid.



    
  
