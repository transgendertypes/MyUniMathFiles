Require Import Coq.Init.Prelude.
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Bool.
Require Import UniMath.MoreFoundations.NegativePropositions.
Require Import UniMath.Combinatorics.FiniteSequences.
Require Import UniMath.Combinatorics.FiniteSets.

(*Definition UU := Type.*)

Definition hetero (Points:UU) (Lines:UU): UU := Points -> Lines -> hProp.

Definition polarize {Points: UU} {Lines: UU} (relation: hetero Points Lines): hetero Lines Points.
  unfold hetero.
  intros line point.
  exact (relation point line).
Defined.

Notation "x 'on y" := (hetero x y) (at level 300). 
Notation "x 'over y" := (polarize (hetero x y)) (at level 300). 

Definition hetero_times (Points:UU) (Lines:UU) : UU := Points × Lines -> hProp.

Theorem hetero_uncurry {Points} {Lines}: hetero Points Lines -> hetero_times Points Lines.
Proof.
  intros Relation.
  unfold hetero_times.
  intros.
  induction X as [point line].
  exact (Relation point line).
Defined.

Theorem hetero_curry {Points} {Lines} : hetero_times Points Lines -> hetero Points Lines.
  intros.
  exact (
      fun x => fun y => X (x,,y)).
Defined.

Theorem het_curry {Points Lines}:
      weq
        (hetero Points Lines)
        (hetero_times Points Lines).
  intros.
  exists hetero_uncurry.
  apply (isweq_iso hetero_uncurry hetero_curry); reflexivity.
Defined.

Definition incidences_of_hetero {Points} {Lines} (het : hetero Points Lines)
  : UU
  := ∑ point : Points,
     ∑ line: Lines, 
        het point line.

Definition propertyOfHetero (Points: UU) (Lines: UU) : UU
  := ∏ _ :  hetero Points Lines, hProp.

Definition hetero_with (Points Lines:UU) (property: propertyOfHetero Points Lines) : UU := ∑ incidence : hetero Points Lines, property incidence. 

Definition ispfinite_hetero {Points Lines: UU} : propertyOfHetero Points Lines.
  unfold propertyOfHetero.
  intros.
  exact ( isfinite Points ).
Defined.

Definition islfinite_hetero {Points Lines: UU} : propertyOfHetero Points Lines.
  unfold propertyOfHetero.
  intros.
  exact ( isfinite Lines ).
Defined.

Definition hetprop_and {Points Lines}
  (condition1 : propertyOfHetero Points Lines)
  (condition2 : propertyOfHetero Points Lines)
  : propertyOfHetero Points Lines
  := λ relation , hconj
           (condition1 relation)
           (condition2 relation)
           .
  
Definition isfinite_hetero {Points Lines: UU} : propertyOfHetero Points Lines :=
  hetprop_and
     ispfinite_hetero
     islfinite_hetero.

Definition finite_hetero_relation (Points Lines : UU) : UU
  := hetero_with Points Lines isfinite_hetero.            

Definition pfiniterelation (Points Lines: UU) : UU
  := hetero_with Points Lines ispfinite_hetero.

Definition lfiniterelation (Points Lines: UU) : UU
  := hetero_with Points Lines islfinite_hetero.
             
Theorem finite_points_polar_to_finite_lines {Points Lines} :
  ∏ rel_with_finite_points : pfiniterelation Points Lines,
        islfinite_hetero (polarize (pr1 rel_with_finite_points)). 
Proof.
  intros.
  induction rel_with_finite_points.
  exact pr2.
Defined.

Theorem finite_lines_polar_to_finite_points {Points Lines} :
  ∏ rel_with_finite_lines : lfiniterelation Points Lines,
        ispfinite_hetero (polarize (pr1 rel_with_finite_lines)). 
   intros.
   induction rel_with_finite_lines.
   exact pr2.
Defined.
          
Theorem finite_relations_polar_to_finite_relations {Points Lines} :
  ∏ finite_relation : finite_hetero_relation Points Lines,
      isfinite_hetero (polarize (pr1 finite_relation)).
  intros.
  induction finite_relation.
  induction  pr2.
  split. exact pr2. exact pr0.
Defined.

Definition polarCondition {Points} {Lines} (condition : propertyOfHetero Points Lines) : propertyOfHetero Lines Points := condition ∘ polarize.

Lemma finite_polarity_lemma {Points Lines : UU} : polarCondition (ispfinite_hetero : propertyOfHetero Points Lines) =  islfinite_hetero.
  reflexivity.
Defined.

Definition setPolymorphicCondition: UU :=
  ∏ Points Lines : hSet,
      propertyOfHetero Points Lines.

Definition polarConditions (condition: setPolymorphicCondition): setPolymorphicCondition.
  unfold setPolymorphicCondition in condition.
  unfold setPolymorphicCondition.
  intros .
  exact (polarCondition (condition Lines Points)).
Defined.

Definition isfinite_over: setPolymorphicCondition.
  unfold setPolymorphicCondition.
  intros.
  exact isfinite_hetero.
Defined.

Definition isselfdual_over  (condition : setPolymorphicCondition)
  := ∏ Points Lines : hSet,
      ∏ relation : (Points 'on Lines),
        condition Points Lines relation -> condition Lines Points (polarize relation).

Theorem finite_selfdual_over_sets : isselfdual_over isfinite_over.
  unfold isselfdual_over.
  intros.
  induction X as [pfin lfin].
  split.
  exact lfin.
  exact pfin.
Defined.

Definition hetero_with_selfdual_condition
  (Points Lines: hSet) 
   :=   ∑ condition : setPolymorphicCondition,
   ∑ incidence : hetero Points Lines,
        condition Points Lines incidence × isselfdual_over condition. 

Notation "x ⟛ y" := (hetero_with_selfdual_condition x y)
(at level 300).

Definition make_hetero_with_selfdual_condition
  (Points Lines : hSet)
  (condition : setPolymorphicCondition)
  (isdual_condition : isselfdual_over condition)
  (incidence: hetero Points Lines)
  (condition_met : condition Points Lines incidence)
  : hetero_with_selfdual_condition Points Lines.
  unfold hetero_with_selfdual_condition.
  exists condition.
  exists incidence.
  split.
  exact condition_met.
  exact isdual_condition.
Defined.

Definition polarize_with_condition {Points Lines Condition} : hetero_with Points Lines Condition -> hetero_with Lines Points (polarCondition Condition).
  intro points_on_lines.
  induction points_on_lines as [structure condition].
  exists (polarize structure).
  exact condition.
Defined.


Definition polarize_with_selfdual_condition {Points Lines} :
  (Points ⟛ Lines) -> (Lines ⟛ Points). 
  intro points_on_lines.
  induction points_on_lines as [condition rest].
  induction rest as[incidence rest].
  induction rest as[condition_met duality_met].
  exists condition.
  exists (polarize incidence).
  unfold isselfdual_over in duality_met.
  split.
  exact (duality_met Points Lines incidence condition_met).
  exact duality_met.
Defined.

Notation "♻" := polarize_with_selfdual_condition.

Definition selfdual_relation_with (condition : setPolymorphicCondition) : UU
  := ∑ Points Lines : hSet,
      ∑ relation : (Points 'on Lines),
        condition Points Lines relation -> condition Lines Points (polarize relation).

Lemma lemma_001 {Points Lines} : ∏ structure : (Points ⟛ Lines), selfdual_relation_with (pr1 structure).
  intro.
  exists Points. exists Lines.
  unfold hetero_with_selfdual_condition in structure.
  induction structure as [condition relation].
  induction relation as [incidence rest].
  exists incidence.
  simpl.
  induction rest as [condition_met duality].
  intro.
  unfold isselfdual_over in duality.
  exact (duality Points Lines incidence X).
Defined.

Definition points_on {Points Lines: hSet} (relation: (Points 'on Lines)) (line : Lines) : hsubtype Points.
  Proof.
  unfold hsubtype.
  exact (fun point => relation point line).
Defined.

Lemma isaset_points_on {Points Lines: hSet}
  (relation: hetero Points Lines)
  (line : Lines) : isaset (points_on relation line).
Proof.
  intros.
  unfold points_on.
  apply isaset_total2.
  - exact (setproperty Points).
  - intro point.
    unfold hetero in relation.
    exact (isasetaprop (propproperty (relation point line ))).
Defined.

Definition pointset (Points Lines: hSet) (relation: hetero Points Lines) (line : Lines) : hSet.

  exact (make_hSet (points_on relation line) (isaset_points_on relation line)).
Defined.
 
Definition lines_unique : setPolymorphicCondition.
  unfold setPolymorphicCondition.
  intros.
  unfold propertyOfHetero.
  unfold hetero.
  intro.
  exact ( ishinh (
             ∏ l1 l2 : Lines, (pointset Points Lines X l1) = (pointset Points Lines X l2) -> l1 = l2
        )).
Defined.

Definition setPolymorphicCondition_and (lhs rhs: setPolymorphicCondition)
  : setPolymorphicCondition.
  unfold setPolymorphicCondition.
  intros.
  unfold setPolymorphicCondition in lhs,rhs.
  assert (propertyOfHetero Points Lines) as left_rel.
  - exact (rhs Points Lines).
    - assert (propertyOfHetero Points Lines) as right_rel.
    + exact (lhs Points Lines).
    + exact (hetprop_and left_rel right_rel).
Defined.

Definition points_unique : setPolymorphicCondition := polarConditions lines_unique.

Definition points_and_lines_unique : setPolymorphicCondition
  := setPolymorphicCondition_and points_unique lines_unique.
Definition lines_and_points_unique := points_and_lines_unique.

Definition all_lines_inhabited : setPolymorphicCondition.
  unfold setPolymorphicCondition.
  intros.
  unfold propertyOfHetero.
  intro incidence.
  exact (ishinh
           (∏ line: Lines,
               ∑ point: Points,
                 incidence point line)).
Defined.

Definition all_points_inhabited : setPolymorphicCondition :=
    polarConditions all_lines_inhabited.
                 
Definition isincidence : setPolymorphicCondition :=
  setPolymorphicCondition_and all_lines_inhabited lines_unique.

Definition isfinite_incidence : setPolymorphicCondition :=
  setPolymorphicCondition_and isincidence isfinite_over.


Definition IncidenceStructure (Points Lines : hSet) : UU. :=
  ∑ incidence : (Points 'on Lines), isfinite_incidence Points Lines incidence.

Definition StandardIncidenceStructure (n1 n2 : nat) : UU :=
  IncidenceStructure (stnset n1) (stnset n2).

Definition always {Points Lines: hSet} : hetero Points Lines.
  unfold hetero.
  intros;
  exact (htrue).
Defined.

Definition never {Points Lines: hSet} : hetero Points Lines.
  unfold hetero.
  intros;
  exact (hfalse).
Defined.


(*  ∏ l1 l2 : (⟦ 1 ⟧)%stn,
  make_hSet (points_on (λ _ _ : (⟦ 1 ⟧)%stn, htrue) l1)
    (isaset_points_on (λ _ _ : (⟦ 1 ⟧)%stn, htrue) l1) =
  make_hSet (points_on (λ _ _ : (⟦ 1 ⟧)%stn, htrue) l2)
    (isaset_points_on (λ _ _ : (⟦ 1 ⟧)%stn, htrue) l2)
  → l1 = l2
*)

Definition Zero := stnset 0.
Definition One := stnset 1.

Lemma lines_unique_on_1 {always} :
  lines_unique One One always.
  unfold lines_unique.
  unfold ishinh.
  simpl.
  unfold ishinh_UU.
  intro.
  intros; apply X.
  intros.
  exact (isconnectedstn1 l1 l2).
Defined.

Lemma all_lines_inhabited_hit :  
  all_lines_inhabited (stnset 1) (stnset 1) always.
  unfold all_lines_inhabited.
  unfold ishinh.
  simpl.
  unfold ishinh_UU.
  intro.
  intro.
  apply X.
  intro.
  exists line.
  exact tt.
Defined.
  
Definition hit : StandardIncidenceStructure 1 1.
  unfold StandardIncidenceStructure.
  unfold IncidenceStructure.
  exists always.
  unfold isfinite_incidence.
  split.
  - split; exact (isfinitestn 1).
  - split.
    + exact lines_unique_on_1.
    + exact all_lines_inhabited_hit.
Defined.
      
Definition miss : StandardIncidenceStructure 1 0.
  unfold StandardIncidenceStructure.
  unfold IncidenceStructure.
  exists never.
  - split.
    + split; exact (isfinitestn _).
    + split.
      -- unfold lines_unique.
         simpl.
         unfold ishinh_UU.
         intro.
         intro.
         apply X.
         unfold pointset.
         intros.
         apply fromempty.
         exact ((pr1 weqstn0toempty) l1).
      -- unfold all_lines_inhabited.
         simpl. unfold ishinh_UU.
         intros.
         apply X.
         intro.
         apply fromempty.
         exact ((pr1 weqstn0toempty) line).
Defined.

Definition coprod_hetero { P1 L1 P2 L2 }
  (lhs : hetero P1 L1)
  (rhs : hetero P2 L2)
  : hetero (coprod P1 P2) (coprod L1 L2).
  unfold hetero.
  intros point line.
  induction point.
  induction line.
  exact (lhs a a0).
  exact hfalse.
  induction line.
  exact hfalse.
  exact (rhs b b0).
Defined.

Definition coproduct_stnset {P1 P2 L1 L2}
  (lhs: hetero (stnset P1) (stnset L1))
  (rhs: hetero (stnset P2) (stnset L2))
  : (stnset (P1 + P2) → stnset (L1 + L2) → hProp).
  intros point line.
  apply weqfromcoprodofstn_invmap in point,line.
  exact ((coprod_hetero lhs rhs) point line).
Defined.

Definition lines_unique_coprod {P1 L1 P2 L2 : hSet}
  {lhs : hetero P1 L1}
  {rhs : hetero P2 L2}
  (lines_unique_lhs : lines_unique P1 L1 lhs)
  (lines_unique_rhs : lines_unique P2 L2 rhs)
: lines_unique (setcoprod P1 P2) (setcoprod L1 L2) (coprod_hetero lhs rhs).
  unfold lines_unique.
  simpl. unfold ishinh_UU. intros. apply X.
  intros.


Definition coprod_stfinc {P1 L1 P2 L2}
  (lhs : StandardIncidenceStructure P1 L1)
  (rhs : StandardIncidenceStructure P2 L2)
  : StandardIncidenceStructure (P1 + P2) (L1 + L2).
  induction lhs.
  induction rhs.
  exists (coproduct_stnset pr1 pr0).
  split.
  - split; exact (isfinitestn _).
  - split.
    + unfold lines_unique.
      

                                                         
Definition triangle : StandardIncidenceStructure 3 3.
  unfold StandardIncidenceStructure.
  unfold IncidenceStructure.
  exists (λ n1 n2, negProp_to_hProp (
                           stnneq n1 n2)).
  split.
  - split; exact (isfinitestn 3).
  - unfold isincidence.
    split.
    + unfold lines_unique.
      
      
      
      
    
       
              
