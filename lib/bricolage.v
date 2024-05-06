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



    
  
