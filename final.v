Require Import Coq.Init.Prelude.
Require Import UniMath.Foundations.All.

Require Import UniMath.MoreFoundations.Bool.
Require Import UniMath.MoreFoundations.Subtypes.
Require Import UniMath.MoreFoundations.Equivalences.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.NullHomotopies.
Require Import UniMath.MoreFoundations.Interval.
Require Import UniMath.Combinatorics.FiniteSequences.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Algebra.GroupAction.

Require Import UniMath.SyntheticHomotopyTheory.All.

Section Core.
  (* Prototypically, the classifier is hProp *) 
  Context (Classifier : UU).

  (* Prototypically, Points Lines are standard finite sets *) 
  Context (Points Lines : UU).

  (* Prototypically, Zero = hfalse *)
  Context (Zero : Classifier).

  Definition lieson (incidence : Classifier) : UU
    := incidence != Zero. 

  (* Prototypically, a lineover a set of points is a subset*) 
  Definition lineover : UU :=
    Points -> Classifier.

  (* We want our lines be pointed, because it makes things more interesting *)
  Definition linesover : UU :=
    ∑ line: lineover,
    ∑ point: Points, lieson (line point).
End Core.

Type linesover.
Type lineover.

Section IncidenceStructures.
  Context ( Classifier: UU ).
  Context ( Zero : Classifier ).
  Context ( Points Lines : UU ).
  Type linesover.
  Type lineover.

  Definition IncidenceStructureover : UU :=
    lineover Classifier (linesover Classifier Points Zero).


End IncidenceStructures.

Type IncidenceStructureover.
Section IncidenceType.
  (* We often want to treat incidence structures as a type.  Here's how. *)
  Context {Classifier Points : UU}.
  Context {Zero : Classifier}.
  Definition pointsof (_: IncidenceStructureover Classifier Zero Points) : UU := Points.

  Definition linesof
    : IncidenceStructureover Classifier Zero Points -> UU.
    unfold IncidenceStructureover.
    unfold lineover.
    intros.
    exact (∑ line: linesover Classifier Points Zero,
              lieson Classifier Zero(X line)).
  Defined.

  Coercion linesof : IncidenceStructureover >-> UU.

  Definition pointson {structure : IncidenceStructureover Classifier Zero Points}
    : linesof structure -> UU.
    unfold linesof.
    intro.
    induction X.
    unfold linesover in pr1.
    induction pr1 as [line [sample incidence]].
    exact (∑ pp : Points, lieson Classifier Zero
                            (line pp)).
  Defined.

  Coercion pointson : linesof >-> UU.

  Definition pencil {structure : IncidenceStructureover Classifier Zero Points} {line: linesof structure}
    : pointson line ->  linesover Classifier (linesof structure) Zero.  
    unfold linesover.
    intro point.
    unfold lineover.
    unfold IncidenceStructureover in structure.
    unfold lineover in structure.
    unfold linesover in structure.
    exists (λ X, ((pr11 X) (pr1 point))).
    exists line.
    unfold lieson.
    exact (pr2 point). 
  Defined.

  (*  From an incidence internal to an incidence structure,
      one can construct a pencil of lines.

      Taking the perspective that "points are types, lines are elements"
      the pencil is a structure which represents one of the types,
      up to its elements. *) 
  Definition pencil_substructure {structure : IncidenceStructureover Classifier Zero Points} {line: linesof structure}
    : pointson line ->  IncidenceStructureover Classifier Zero Points.  
    unfold IncidenceStructureover.
    unfold linesover.
    intro point.
    intro.
    exact ((pr1 X) (pr1 point)).
  Defined.

      

End IncidenceType.

Section StandardIncidenceStructure.

  Definition StandardIncidenceStructureover (Points: UU) : UU :=
    IncidenceStructureover hProp hfalse Points.

  Definition IOverNat (n : nat) : UU :=
    StandardIncidenceStructureover (stn n).

  Definition OneOnOne : IOverNat 1.
    intro
.
    induction X as [line [point incidence]].
    exact (line point).
  Defined.

  (* One line through two points *)
  Definition TwoOnOne : IOverNat 2.
    intro; induction X as [line [point incidence]].
    exact ( ishinh ( ∏ pp, lieson hProp hfalse (line pp) ) ).
  Defined.

  (* One line through N Points *)

  Definition nOnOne (n : nat) : IOverNat n.
    intro; induction X as [line [point incidence]].
    exact ( ishinh (∏ pp, lieson hProp hfalse (line pp))).
  Defined.

  Coercion stn : nat >-> Sortclass.

  Definition line_thru_all_three
    : linesover hProp (⟦ 3 ⟧)%stn hfalse.
    unfold linesover.
    exists (λ _, htrue).
    exists firstelement.
    intro.
    inversion X.
    exact tt.
  Defined.
  
  Definition one_line_lieson_all_three_points :
    linesof (nOnOne 3).
    unfold nOnOne.
    unfold linesover.
    unfold lineover.
    unfold lieson.
    simpl.
    unfold neg.
    exists (line_thru_all_three).
    intro.
    inversion X.
    unfold ishinh_UU.
    intro.
    intro.
    assert ((⟦ 3 ⟧)%stn → htrue = hfalse → ∅).
    + intro.
      intro.
      inversion X2; exact tt.
  + exact (X0 X1).
Defined.

  Definition a_point_on_the_line_thru_all_three :
    one_line_lieson_all_three_points.
    exists firstelement.
    intro.
    unfold one_line_lieson_all_three_points in X.
    unfold line_thru_all_three in X.
    inversion X; exact tt.
  Defined.

  Definition OneToOneIncidence
    (Classifier : UU)
    (Zero : Classifier)
    (Classify : UU -> Classifier)
    (Points : UU)
    :
    IncidenceStructureover Classifier Zero Points.
    intro; induction X as [line [point incidence]].
    exact (Classify 
               (∏ pp,
                 lieson Classifier Zero (line pp)
                 -> pp = point ) ).
  Defined.

  (* Truncation as classification of incidence *)
  Definition OneToOneIncidence_hProp
    (Points : UU) :
    IncidenceStructureover hProp hfalse Points
   := OneToOneIncidence hProp hfalse ishinh Points.

Section Polytopes.
  Context (Classifier : UU).
  Context (Zero : Classifier).
  Context (Classify : UU -> Classifier).

  Context (Points : UU).

  Notation IncidenceStructureover :=
    (IncidenceStructureover Classifier Zero).

  Context (Structure : IncidenceStructureover Points).
  
  Definition Incidence2StructureOver : UU.
    exact (IncidenceStructureover (linesof Structure)).
  Defined.
  
  Definition Incidence3StructureOver (two_structure: Incidence2StructureOver) : UU.
    exact (IncidenceStructureover (linesof two_structure)).
  Defined.

  Definition IncidenceStructure : UU :=
    ∑ PP : UU, IncidenceStructureover PP.

  (* We can view the "type" of incidence 2-structures
     as an incidence structure over incidence structures *)
  Definition Incidence2_s : IncidenceStructureover IncidenceStructure.
    unfold IncidenceStructureover.
    unfold lineover,linesover.
    intro.
    induction X as [line [point incidence]].
    exact (Classify (
               ∑ PP : UU,
                 ∑ structure : IncidenceStructureover PP,
                   (linesof structure = Points)
               )).
  Defined.
  
  Definition Incidence2 : IncidenceStructure.
    exists IncidenceStructure.
    exact Incidence2_s.
  Defined.

  Definition Incidence3_s : IncidenceStructureover IncidenceStructure.
    unfold IncidenceStructureover.
    unfold lineover,linesover.
    intro.
    induction X as [line [point incidence]].
    exact (Classify (
                 ∑ classifying_line : Incidence2_s,
                 ∑ incidence_structure : classifying_line,
                   
                   (linesof (pr21 incidence_structure)) = Points)
               ).
  Defined.

  Definition Incidence3 : IncidenceStructure.
    exists IncidenceStructure.
    exact Incidence3_s.
  Defined.

  Definition Incidence_n (n : nat) : IncidenceStructureover IncidenceStructure.
    induction n.
    + unfold IncidenceStructureover.
      unfold lineover.
      intro.
      exact (Classify htrue).
    + unfold IncidenceStructureover.
         unfold lineover; intros.
         exact (Classify (
                 ∑ classifying_line : IHn,
                 ∑ incidence_structure : classifying_line, 
                   weq (linesof (pr21 incidence_structure)) Points)
               ).
  Defined.

  Context (hitting_aint_missing : (Classify unit) != Zero).
  Context (hitting_never_missing: ∏ ts:UU,
            (ts != empty) -> (Classify ts) != Zero).
    
  Definition poly_to_struc {n : nat} : Incidence_n n -> IncidenceStructure.
    unfold Incidence_n. induction n.
    - simpl.
      intro.
      exact (pr121 X).
    - simpl.
      intro.
      apply IHn.
      simpl.
      induction n.
      + remember (pr121 X).
        induction i.
        remember (linesof pr2).
        inversion X.
        split.
        unfold linesover.
        ++ unfold lineover.
           unfold linesover in pr0.
           induction pr0.
           exists pr0.
           exact pr4.
        ++ exact (hitting_aint_missing).
      + split.
        ++ induction X.
           exact pr1.
        ++ 
           apply hitting_never_missing.
           intro.
           induction X0.
           assert ((fix F (n0 : ℕ) :
                           IncidenceStructureover IncidenceStructure :=
                         match n0 with
                         | 0 =>
                             λ _ : linesover Classifier IncidenceStructure
                                     Zero, Classify unit
                         | S n1 =>
                             λ _ : linesover Classifier IncidenceStructure
                                     Zero,
                             Classify
                               (∑ (classifying_line : F n1)
                                (incidence_structure : classifying_line),
                                weq (pr21 incidence_structure) Points)
                         end) n).
  Defined.
  
  Definition facets {n : nat} : Incidence_n n -> UU.
    simpl.
    - simpl.
      intro.
      exact (linesof (pr1 X)).

End Polytopes.
Section Polytope_examples.
    Context (Points: UU).
    Notation Incidence_n := (Incidence_n hProp hfalse ishinh Points).

    Definition forgetFacets {n: nat} : Incidence_n (S n) -> Incidence_n n.
    intro polyhedron.
    induction n.
    simpl in polyhedron.
    unfold Incidence2_s in polyhedron.
    induction polyhedron.
    simpl.
    split. exact pr1.
    unfold lieson.
    intro.
    inversion X.
    unfold ishinh_UU.
    intros.
    exact (X0 tt).
    - unfold Incidence_n. simpl.
      split.
      exact (pr1 polyhedron).
      induction polyhedron.
      unfold Incidence_n in pr2. simpl in pr2.
      pose proof (IHn pr1).
      
      exact (pr2).
      unfold lieson.
      unfold Incidence_n in polyhedron.
      simpl in polyhedron.
      induction polyhedron.
      unfold lieson in pr2.
      induction pr2.
      exists .
      
      unfold ishinh_UU.
      intros.
      apply X0.
      induction X.
      simpl in H0,H1.
      unfold ishinh_UU in H0.
      pose proof (IHn pr1).
      exists X.
      simpl in pr2.
      exact pr2.

    
  Definition PowerFaces : Incidence2StructureOver.
    unfold Incidence2StructureOver.
    unfold IncidenceStructureover.
    unfold lineover.
    intro.
    exact (Classify htrue).
  Defined.

  (* The main definition, really *)
  Definition iPolytope (n : nat) (Pts: UU) : UU.
    induction n.
    - exact Pts.
    - induction n.
      + exact incidenceStructureOver Pts.
      + exact (∑ structure: IHn,
                ∑ structure2: IncidenceStructureover structure,
                 IncidenceStructureover (linesof (pr2 structure))). 
  Defined.

  Definition polytope_to_istructure {n:nat}
    : iPolytope (S n) Points -> ∑ PP, IncidenceStructureover PP.
    intro.
    induction n.
    - exists Points.
      exact (pr2 X).
    - exists (iPolytope (S n) Points).
      exact (pr21 X).
  Defined.

  Definition poly_to_istructure {n} (poly: iPolytope (S n) Points):= pr2 (polytope_to_istructure poly).

  Definition lower {n} (poly: iPolytope (S n) Points)
    := pr1 (polytope_to_istructure poly).

  Coercion poly_to_istructure : iPolytope >-> IncidenceStructureover.

  Notation lineover := (lineover Classifier).
  Notation lieson := (lieson Classifier Zero).



  Definition iLower {n:nat}
    (higher: iPolytope (S n) Points)
    (face : higher)
    : iPolytope n Points.
  Proof.
    induction n.
    - unfold iPolytope; simpl.
      exact (idpath Points).
    - 
      induction n;
      induction face;
      induction pr1 as [line [point incidence]];
      exact point.
  Defined.

  Definition infinityPolytope: UU :=
    ∑ fn : (∏ n: nat, iPolytope n Points),
        ∏ n : nat, ∑ face : fn (S n),

          iLower (fn (S n)) face = fn n. 
  
End Polytopes.

Section PolytopeExamples.
  Context (Points Classifier : UU).
  Context (Zero : Classifier).
  Context (Classify : UU -> Classifier).

  Notation infinityPolytope := (infinityPolytope Classifier Zero).
  Notation iPolytope := (iPolytope Classifier Zero).
  Notation IncidenceStructureover := (IncidenceStructureover Classifier Zero).

  (* an empty incidence structure over n points has no lines at all. *)
  Definition empty_iStructure (PP: UU) : IncidenceStructureover PP.
    intro; exact Zero.
  Defined.

  (* a power iStructure has every possible line *)
  Definition power_iStructure (PP: UU) : IncidenceStructureover PP.
    intro; exact (Classify htrue).
  Defined.
  
  Definition empty_preinfinityPolytope
               : ∏ n : nat, iPolytope n Points.
    intro;induction n.
    - exact (idpath Points).
    - induction n.
      + exists IHn.
        exact (empty_iStructure Points).
      + assert (∑ _ : iPolytope (S n) Points = iPolytope (S n) Points,
                   IncidenceStructureover (iPolytope (S n) Points)).
        ++ exists (idpath _). 
        exact (empty_iStructure (linesof(empty_iStructure (iPolytope Points (S n))))).
  Defined.

        
 Compute empty_preinfinityPolytope 20.
 (* Compute empty_preinfinityPolytope witness (5 * 5 * 5 * 5).  *) 
    
 (* A true infinity polytope needs the special condition *) 
  Definition empty_infinityPolytope : infinityPolytope Points.
    unfold infinityPolytope.
    exists empty_preinfinityPolytope.
    intros.
    unfold iLower.
    simpl.
    unfold empty_iStructure.
    unfold nat_rect.
    induction n.
    - unfold linesover.
      Abort.
     
  Definition power_preinfinityPolytope :
    ∏ n : nat, iPolytope Points n.
    intro.
    induction n.
    - exact (idpath Points).
    - induction n.
      + exact (power_iStructure Points).
      + induction n.
        -- unfold iPolytope.
           simpl.
           exists IHn.
        pose proof ((power_iStructure (linesof IHn))).
        exists (power_iStructure (linesof IHn)).

