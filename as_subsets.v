(* Since 
every line is presumed to be unique, we can
think of an incidence structure as an indexed subset
of pointwise properties *)


Require Import Coq.Init.Prelude.
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Bool.
Require Import UniMath.MoreFoundations.Subtypes.
Require Import UniMath.MoreFoundations.Equivalences.
Require Import UniMath.Combinatorics.FiniteSequences.
Require Import UniMath.Combinatorics.FiniteSets.

Definition PreIncidence (Points Lines : hSet) : UU :=
  incl Lines (subtype_set Points).
Definition linesover := subtype_set.

Definition noProperties_fn : hPropset -> hProp.
  intros.
  exact hfalse.
Defined.

Definition allProperties_fn : hPropset -> hProp.
  intros.
  exact htrue.
Defined.

Definition justTrueProperty_fn : hPropset -> hProp.
  intros.
  exact X.
Defined.

Definition justFalseProperty_fn (p1 : hPropset) : hProp :=
  hneg (hProptoType p1).

Definition noProperties : subtype_set hPropset.
  exact noProperties_fn.
Defined.

Definition allProperties : linesover hPropset.
  exact allProperties_fn.
Defined.

Definition justTrueProperty : linesover hPropset.
  exact justTrueProperty_fn.
Defined.

Definition justFalseProperty : linesover hPropset.
  exact justFalseProperty_fn.
Defined.

Definition pointson := linesover.

(* this definition is generalized by the next *)  
Definition hPropIncidence {Points Lines: UU}
  : UU :=
  ∑ lines  : hsubtype (linesover Points),
  ∑ points : hsubtype (pointson  Lines),
        ∑ decode_line : weq lines Lines,
        ∑ decode_point : weq points Points, 
          ∏ pp : points,
          ∏ ll : lines,
                (pr1 pp) (decode_line ll)
              = (pr1 ll) (decode_point pp).
 
Definition hlevelIncidence
  (Logos: UU)
  (truth_value : Logos -> UU)
  {n: nat}
  (ishlvel : isofhlevel n Logos)
  : UU -> UU -> UU :=
  λ Points Lines, 
  ∑ lines  : (Points -> Logos) -> Logos,
  ∑ points : (Lines -> Logos)  -> Logos,
            ∑ encode_line : weq Lines
                (∑ line: Points -> Logos,
                  truth_value (lines line)),
              ∑ encode_point : weq Points
                (∑ point: Lines -> Logos,
                 truth_value (points point)),
          ∏ pp : Points,
          ∏ ll : Lines,
                (pr1 (encode_line ll)) pp
              = (pr1 (encode_point pp)) ll.

Lemma isofhlevel2_hPropset: isofhlevel 2 hPropset.
  exact isasethProp.
Defined.

Lemma isofhlevel2_nat: isofhlevel 2 nat.
  exact isasetnat.
Defined.

Lemma isofhlevel0_unit: isofhlevel 0 unit.
  exact iscontrunit.
Defined.

Definition NormalIncidence : UU -> UU -> UU
  := hlevelIncidence hPropset hProptoType isofhlevel2_hPropset .

Definition UnitIncidence : UU -> UU -> UU
  := hlevelIncidence unit (λ _, unit) isofhlevel0_unit.

Definition BoolIncidence : UU -> UU -> UU
  := hlevelIncidence unit (λ _, unit) isofhlevel0_unit.

Definition NaturalIncidence : UU -> UU -> UU
  := hlevelIncidence nat stn isofhlevel2_nat .
          

Definition lineset {Points Lines}
  (structure : PreIncidence Points Lines) :
  Lines -> linesover Points := pr1 structure.
Defined.

(* I think we need a stricter form of "property" *)
Definition property (st: hSet): UU := st -> hPropset.
Definition subset_with {st} (property: property st) : UU.
  exact (hfiber property htrue).
Defined.

Definition isaset_subset_with {st} {property : property st}
    : isaset (subset_with property).
  unfold subset_with.
  apply isaset_hfiber.
  apply st.
  apply hPropset.
Defined.

Definition propertyset {st: hSet} (property : property st): hSet :=
  make_hSet
  (subset_with property)
  isaset_subset_with.
 
Definition subsets_set (st:hSet) : hSet.
  refine (make_hSet (∑ propert : (property st), propertyset propert) _).
  apply isaset_total2.
  - unfold property.
    apply isasethsubtype.
  - intros.
    apply propertyset.
Defined.

Definition subtype_from_subset {Points: hSet} : subsets_set Points -> subtype_set Points.
  intro.
  induction X.
  refine (_ pr1).
  intros fn point.
  exact (fn point).
Defined.

Definition inhabited_subtype (Points: _) : UU :=
  ∑ subtype : hsubtype Points,
  (∑ x : Points, subtype x = htrue).


Definition subset_from_inhabited_subtype {Points: hSet} (inhabited_subtype : inhabited_subtype Points)
  (*(subtype : subtype_set Points)  
                      (inhabitance : ∑ x : Points, subtype x = htrue) *)
  : subsets_set Points.
  induction inhabited_subtype as [subtype inhabitance]. 
  exists subtype.
  exact inhabitance.
Defined.

Definition isinhabited_subtype_from_subset
  {Points: hSet}
  (subset : subsets_set Points) :
  (∑ x : Points, (subtype_from_subset subset) x = htrue).
  unfold subsets_set in subset.
  simpl in subset.
  unfold subtype_from_subset.
  induction subset as [property promise].
  unfold subset_with in promise.
  induction promise as [really promise].
  exists really.
  exact promise.
Defined.

Definition make_inhabited_subtype {Points}
  (subtype: linesover Points)
  (inhabitance : ∑ x : Points, subtype x = htrue) 
  : inhabited_subtype Points.
  exists subtype.
  exact inhabitance.
Defined.
  

Definition inhabited_subtype_from_subset
  {Points: _}
  (subset : subsets_set Points) :
  inhabited_subtype Points.
Proof. 
  unfold inhabited_subtype.
  exists (subtype_from_subset subset).
  exact (isinhabited_subtype_from_subset subset).
Defined.

Definition lines_over (Points: hSet) : hSet := subsets_set Points.

Definition point_on
  {Points: hSet}
  (line : lines_over Points) :
  Points.
  pose proof (inhabited_subtype_from_subset line).
  induction X.
  induction pr2.
  exact pr0.
Defined.

Definition point_really_on
  {Points: hSet}
  (line : lines_over Points) :
  ∑ point: Points, (pr1 line) point = htrue.
  exists (pr1 (pr2 (inhabited_subtype_from_subset line))).
  simpl.
  simpl in line.
  induction line.
  induction pr2.
  exact pr2.
Defined.


Definition quasiinverse_inhabited_subtype_to_subset {Points: hSet} (x:inhabited_subtype Points) : (inhabited_subtype_from_subset ( subset_from_inhabited_subtype x)) = x.
Proof. reflexivity.
Defined.

Definition quasiinverse_subset_to_inhabited_subtype {Points : hSet} (x:inhabited_subtype Points) : inhabited_subtype_from_subset (subset_from_inhabited_subtype x) = x.
Proof. reflexivity.
Defined.
Definition lemma_003 {Points} (y: inhabited_subtype Points) : (∑ x : inhabited_subtype Points,
         x = y).
 exists y.
 reflexivity.
Defined.

Definition isaset_inhabitedsubtype (Points: hSet) : isaset (inhabited_subtype Points).
      ++ apply isaset_total2.
         +++ unfold hsubtype.
             apply impred_isaset.
             intro.
             exact isasethProp.
         +++ intros.
             apply isaset_total2.
             ++++ apply Points.
             ++++ intro.
                  pose proof (isasethProp).
                  unfold isaset in X.
                  apply isasetaprop.
                  exact (X (x x0) htrue).
Defined.

Definition isequivalence_subset_from_inhabited_subtype {Points: hSet}
  : isEquivalence (subset_from_inhabited_subtype: inhabited_subtype Points -> subsets_set Points).
  unfold isEquivalence.
  exists inhabited_subtype_from_subset.
  exists quasiinverse_subset_to_inhabited_subtype.
  exists quasiinverse_inhabited_subtype_to_subset.
  intros.
  reflexivity.
Defined.

Definition subsets_are_inhabited_subtypes {Points: hSet}
  : Equivalence (inhabited_subtype Points) (subsets_set Points).
  unfold Equivalence.
  exists subset_from_inhabited_subtype.
  exact isequivalence_subset_from_inhabited_subtype.
Defined.
  

Definition subsets_weq_inhabited_subtypes {Points : hSet} :
   weq (lines_over Points) (inhabited_subtype Points).  
  unfold weq.
  exists (inhabited_subtype_from_subset).
  apply isEquivalence_to_isweq.
  exact isequivalence_subset_from_inhabited_subtype .
Defined.

Definition Inc0 (Points : hSet) : UU := weq Points Points.
Definition Inc1 (Points Lines : hSet) : UU := incl Lines (lines_over Points).
Definition Inc1_function {Points Lines : hSet} : Inc1 Points Lines -> Lines -> (lines_over Points).
  intros.
  unfold Inc1 in X.
  unfold incl in X.
  induction X.
  exact (pr1 X0).
Defined.
Coercion Inc1_function : Inc1 >-> Funclass.

(* We can compose an equivalence of lines with an incidence structure easily *)
Definition Inccompose_01_line {Points Lines} (inc0 : Inc0 Lines) (inc1 : Inc1 Points Lines) : Inc1 Points Lines.
  apply weqtoincl in inc0.
  exists (inc1 ∘ (pr1 inc0)).
  exact (isinclcomp _ _ ).
Defined.

Definition compose_0_linesover {Points: hSet} (path: weq Points Points) : lines_over Points -> lines_over Points.
  intros.
  induction X as [propert st].
  exists (propert ∘ path).
  exists (invmap path (pr1 st)).
  induction st as [point lieson].
  simpl.
  unfold invmap.
  unfold hfiberpr1.
  unfold weqccontrhfiber.
  unfold iscontrpr1.
  unfold weqproperty.
  induction path.
  simpl.
  induction pr2.
  simpl.
  induction pr0.
  simpl.
  rewrite pr4.
  exact lieson.
Defined.

Definition compose_0_linesover' {Points: hSet} (path: weq Points Points) : lines_over Points -> lines_over Points.
  intros.
  induction X as [propert st].
  pose proof (invweq path) as path'.
  exists (propert ∘ path').
  exists ((invmap path') (pr1 st)).
  induction st as [point lieson].
  simpl.
  unfold invmap.
  simpl.
  unfold weqccontrhfiber.
  simpl.
  unfold weqproperty.
  simpl.
  unfold hfiberpr1.
  unfold iscontrpr1.
  induction path'.
  simpl.
  induction pr2.
  simpl.
  induction pr0.
  simpl.
  rewrite pr4.
  exact lieson.
Defined.

Definition compose_0_linesoverEquivalence {Points: hSet} (path: Equivalence Points Points) : lines_over Points -> lines_over Points.
  intros.
  induction X as [propert st].
  exists (propert ∘ path).
  exists (Equivalence_toInverseFunction path (pr1 st)).
  induction st as [point lieson].
  simpl.
  rewrite (Equivalence_toTargetHomotopy path point).
  exact lieson.
Defined.

Definition compose_0_linesoverEquivalence' {Points: hSet} (path: Equivalence Points Points) : lines_over Points -> lines_over Points
  := compose_0_linesoverEquivalence (inverseEquivalence path).
(*
  intros.
  induction X as [propert st].
  exists (propert ∘ Equivalence_toInverseFunction path).
  exists (path (pr1 st)).
  induction st as [point lieson].
  simpl.
  rewrite (Equivalence_toSourceHomotopy path point).
  exact lieson.
Defined.
*)
Set Printing Coercions.
Definition compose_0_invertible_left {Points: hSet} (path: weq Points Points) (line : lines_over Points)
  : (pr1 (compose_0_linesover path (compose_0_linesover' path line))) (pr12 line) = htrue.
  induction line as [line [point incidence]].
  unfold pr2. unfold pr1.
  simpl.
  unfold invweq. unfold make_weq. unfold invmap. simpl.
  unfold pr1weq.
  unfold pr1.
  unfold hfiberpr1.
  unfold weqccontrhfiber.
  unfold weqproperty.
  induction path as [path isweqpath].
  unfold pr2.
  induction isweqpath.
  simpl.
  pose proof (pr2 (make_hfiber path point (idpath (path point)))).
  rewrite <- X.
  simpl.
  exact incidence.
Defined.

Definition compose_0_invertible_right {Points: hSet} (path: weq Points Points) (line : lines_over Points)
  : (pr1 (compose_0_linesover' path (compose_0_linesover path line))) (pr12 line) = htrue.
  induction line as [line [point incidence]].
  unfold pr2. unfold pr1.
  simpl.
  unfold invweq. unfold make_weq. unfold invmap. simpl.
  unfold pr1weq.
  unfold pr1.
  unfold hfiberpr1.
  unfold weqccontrhfiber.
  unfold weqproperty.
  induction path as [path isweqpath].
  unfold pr2.
  induction isweqpath.
  simpl.
  induction pr1.
  simpl.
  rewrite pr0.
  exact incidence.
Defined.


Definition compose0 {Points: hSet} (action : Inc0 Points)
  : (linesover Points) ≃ (linesover Points).
  unfold pr1hSet.
  unfold linesover.
  unfold subtype_set.
  unfold make_hSet.
  unfold pr1.
  unfold hsubtype.
  unfold weq.
  exists (λ line, λ point, line ((pr1 action) point)).
  unfold isweq.
  unfold iscontr.
  intro line.
  assert (hfiber
           (λ (line0 : pr1hSet Points → hProp) (point : pr1hSet Points), line0 (pr1 action point))
           line).
  - unfold hfiber.
    pose proof (invmap action) as inverse.
    exists (line ∘ (invmap action)).
    simpl.
    unfold invmap.
    unfold hfiberpr1.
    unfold weqccontrhfiber.
    unfold iscontrpr1.
    unfold weqproperty.
    induction action as [action action_isweq].
    simpl.
    unfold isweq in action_isweq.
    unfold iscontr in action_isweq.
    unfold hfiber in action_isweq.
    assert (∏ point, pr11 (action_isweq (action point)) = point).
    -- intro.
       pose proof (action_isweq (action point)).
       
       induction X.
       induction pr1.
       pose proof (pr2 (Preamble.pr1 (action_isweq (action point)))).
       rewrite X.
       assert (∑ x : pr1hSet Points, action x = action point).
       exists point; reflexivity.
       pose proof (pr2 ((point,, idpath (action point)) : ∑ x : pr1hSet Points, action x = action point)).
       rewrite <- X1.
       simpl.
       reflexivity.
    -- apply funextfun.
       unfold homot.
       intro.
       assert ( ∏ point1 point2 : pr1hSet Points,
                  point1 = point2 -> line point1 = line point2).
       --- intros.
           rewrite X0.
           auto.
       --- apply (X0 (pr11 (action_isweq (action x))) x).
           exact (X x). (*weird...*)
  - exists X.
    intros.
    assert (iscontr (hfiber
        (λ (line0 : pr1hSet Points → hProp) (point : pr1hSet Points),
         line0 (pr1 action point)) line)).
    + refine (iscontrhfiberl2 _ _ _ _ _).
      ++
        unfold homot.
        intro.
        Unshelve.
        Focus 2.
        intros some_line some_point.
        exact (some_line (pr1 action some_point)).
        reflexivity.
      ++
        assert ((λ (line : pr1hSet Points → hProp) (point : pr1hSet Points),
         line (pr1 action point)) = (λ (some_line : pr1hSet Points → hProp) (some_point : pr1hSet Points),
                                      some_line (pr1 action some_point))).
        reflexivity.
        unfold iscontr.
         exists t.
         intros.
         induction t0.
         induction t.
         refine (total2_paths_f _ _).
         unfold transportf.
         unfold constr1.
         simpl.
         unfold paths_rect.
         simpl.
         Unshelve.
         Focus 2.
         simpl.
         induction action as[action actionisweq].
         unfold isweq in actionisweq.
         unfold Preamble.pr1 in pr2.
        

    apply pathshfiber.
    unfold hfiber in t.
    unfold hfiber in X.
    induction t.
    induction X.
    refine (total2_paths_f _ _).
    unfold transportf.
    unfold constr1.
    unfold Preamble.pr1.
    unfold Preamble.pr2.
    simpl.
    unfold paths_rect.
    simpl.
    Unshelve.
    Focus 2.
    simpl.
    rewrite <- pr2 in pr3.
    simpl in pr3.
    U.
    
    split.
    
    exists (compose_0_linesover' action line).
  exists (make_hfiber line ).
  weqfp _ _.

Definition isweq_compose0 {Points: hSet} {action : Inc0 Points}: isweq (compose_0_linesover action).
  unfold isweq.
  intro.
  unfold Inc0 in action.
  unfold iscontr.
  assert (hfiber (compose_0_linesover action) y). (*(line,, point,, incidence)).*)
  - unfold hfiber.
    pose proof (compose_0_linesover' action y).
    exists (compose_0_linesover' action y).
    unfold compose_0_linesover.
    unfold compose_0_linesover'.
    refine (total2_paths_f _ _).
    simpl.
    unfold invmap. unfold invweq.
    apply 
    
  exists (make_hfiber (compose_0_linesover action) ((invmap action) point)). 
  (lines_over Points) (lines_over Points).

Definition compose_0_invleft {Points: hSet} (path: weq Points Points) (line : lines_over Points)
  : compose_0_linesover path (compose_0_linesover' path line) = line.
  unfold compose_0_linesover.
  unfold compose_0_linesover'.
  simpl.
  induction line as [line [point incidence]].
  induction path as [path iswq].
  unfold invmap. simpl.
  unfold hfiberpr1. unfold pr1weq.
  simpl.
  unfold weqccontrhfiber.
  simpl.
  unfold iscontrpr1.
  unfold weqproperty.
  simpl.
  simpl.
  unfold isweq in iswq.
  pose proof (iswq (path point)).
  induction X as [cntr frall].
  pose proof ((pr2 (iswq (path point))) (make_hfiber path point (idpath (path point)))).
  assert (line ∘ (λ y : pr1hSet Points, pr11 (iswq y)) ∘ path = line).
  - unfold funcomp.
    apply funextfun.
    unfold homot.
    intro.
    pose proof ((pr2 (iswq (path x))) (make_hfiber path x (idpath (path x)))).
    rewrite <- X0.
    reflexivity.
  - assert (pr11 (iswq (path point)) = point).
    -- rewrite <- X.
       reflexivity.
    -- assert ((pr11 (iswq (path (pr11 (iswq (path point)))))) = point).
       --- repeat rewrite X1.
           reflexivity.
       --- 
         assert ((line (pr11 (iswq (path (pr11 (iswq (path point)))))) = line point)).
         rewrite X2.
         reflexivity.
         ---- unfold homotinvweqweq.
              unfold homotinvweqweq0.
              simpl.
              apply (total2_paths_f X0).
              refine (total2_paths2 X0 (total2_paths2 X3 _) ).
                        
              assert((internal_paths_rew_r (pr1hSet Points) (path point) 
    (path point) (λ p : pr1hSet Points, line (p) = htrue)
    (internal_paths_rew_r (pr1hSet Points) ((path point)) point
       (λ p : pr1hSet Points, line p = htrue) incidence
       (! (! homotinvweqwe) @ idpath point)) (idpath (path point))) = incidence).
         ---- unfold internal_paths_rew_r.
              simpl.
              apply X3.
              rewrite X3.

    refine (total2_paths2 X0 _) .
  exists.
  rewrite <- X. 
  unfold make_hfiber in X.
  
  refine (total2_paths2 _ _ : ?Goal).

Definition compose_0_invright {Points: hSet} (path: weq Points Points) (line : lines_over Points)
  : compose_0_linesover' path (compose_0_linesover path line) = line.

Definition compose_0_invertible_leftEquivalence
  {Points: hSet} (path: Equivalence Points Points) (line : lines_over Points) (point : Points)
  : (compose_0_linesoverEquivalence' path) (compose_0_linesoverEquivalence path line) = line.
  
  simpl.
  (* induction line as[property [point fiber]]*)
  unfold compose_0_linesoverEquivalence'.
  unfold compose_0_linesoverEquivalence.
  unfold funcomp.
  simpl.
  pose proof (Equivalence_toTargetHomotopy path) as target.
  unfold Equivalence_toInverseFunction in target.
  pose proof (target point).
  rewrite X.
  pose proof (Equivalence_toSourceHomotopy path) as source.
  pose proof (Equivalence_toTargetHomotopy (inverseEquivalence path)) as target'.
  pose proof (Equivalence_toSourceHomotopy (inverseEquivalence path)) as source'.
  induction line as [property [point lieson]].
  refine (total2_paths_f _ _).
  unfold transportf.
  unfold pr1.
  unfold pr2.
  simpl.
  induction path as [pathl].
  induction pr2 as [pathr iseq].
  unfold inverseEquivalence.
  unfold Equivalence_toInverseFunction.
  unfold makeEquivalence.
  unfold pr1.
  unfold pr2.
  unfold pr1.
  unfold pr2.
  unfold pr1.
  unfold pr2.
  repeat unfold pr1.
  repeat unfold pr2.
  simpl.
  unfold Equivalence_toInverseFunction in target.
  unfold pr1 in target.
  unfold pr2 in target.
  unfold Equivalence_toFunction in target.
  unfold pr1 in target.
  pose proof (target point).
  simpl.
  refine (total2_paths_f _ _ : linesover Points = linesover Points).
  
  unfold compose_0_linesoverEquivalence'.
  unfold transportf.
  unfold pr1.
  unfold pr2.
  rewrite (target point).
  simpl.

Definition isEquivalence_compose_0_linesover {Points: hSet} (path: Equivalence Points Points): isEquivalence (compose_0_linesoverEquivalence path).
  unfold isEquivalence.
  exists (compose_0_linesoverEquivalence' path).
  exists 
  assert (∏ p : ∏ y : lines_over Points,
       compose_0_linesoverEquivalence path (compose_0_linesoverEquivalence' path y) = y,
  ∏ q : ∏ x : lines_over Points,
       compose_0_linesoverEquivalence' path (compose_0_linesoverEquivalence path x) = x,
  ∏ x : lines_over Points,
  maponpaths (compose_0_linesoverEquivalence path) (q x) =
    p (compose_0_linesoverEquivalence path x)).
  - 
    intros.
    simpl.
    unfold compose_0_linesoverEquivalence.
    simpl.
    unfold maponpaths.
    simpl.
    unfold 
    

  intro.
  unfold compose_0_linesover.
Defined.

Definition induces_left {Points: hSet} (path: weq Points Points) : ∏ y : lines_over Points, compose_0_linesover (invweq path) (compose_0_linesover path y) = y.
  intros.
  simpl.
  pose proof (invinv path).
  unfold compose_0_over.
  induction y as[propert yset].
  unfold property in propert.
  simpl.
  unfold hfiberpr1.
  simpl.
  assert (invmap path (path (invmap path (pr12 y))) = invmap path (pr12 y)).
  - apply homotinvweqweq.
  - rewrite X. unfold invweq. simpl.

Definition induced_path {Points: hSet} (path: weq Points Points) : Equivalence (lines_over Points) (lines_over Points).
  exists (compose_0_linesover path).
  unfold isEquivalence.
  exists (compose_0_linesover (invweq path)).

Definition permutation_inclusion {Points: hSet} (path: weq Points Points) : incl (lines_over Points) (lines_over Points).
  pose proof (weqtoincl path).
  refine (inclcomp _ _).
  - 
  exists (compose_0_linesover path). 
  unfold compose_0_linesover.
  unfold internal_paths_rew_r .
  simpl.
  unfold homotinvweqweq.
  simpl.
  unfold isincl.
  unfold isofhlevelf.
  intro.
  unfold isofhlevel.
  unfold hfiber.
  simpl.
  intros.
  rewrite (homotinvweqweq path (pr12 H)).
(* Doing it with an equivalence of points is just a bit trickier.*) 
Definition Inccompose_01_point {Points Lines} (inc0 : Inc0 Points) (inc1 : Inc1 Points Lines) : Inc1 Points Lines.
  unfold Inc0 in inc0; unfold Inc1 in inc1.
  unfold Inc1.
  pose proof (λ line, compose_0_linesover inc0 ((pr1 inc1) line)).
  exists ((compose_0_linesover inc0) ∘ (pr1 inc1)).
  refine (isinclcomp (compose_0_linesover inc0) inc1 ).

  unfold isofhlevel.
  pose proof (weqtoincl inc0).
  induction inc1.
  assert ( Lines -> (lines_over Points)).
  - 
    intro line.
    
    induction (pr1 line) as [property set].
    exists (λ point, property (inc0 point)).
    induction set as [point pointis].
    exists ((invmap inc0) point).
    rewrite homotweqinvweq.
    exact pointis.
  - exists ( property (inc0 point)).
    exists X0.
    unfold isincl.
    
  
  

Definition SetPreIncidence (Points Lines : hSet) : UU :=
  incl Lines (subsets_set Points). 
Definition SetPreIncidence_from_PreIncidence {Points Lines}
  (spi : PreIncidence Points Lines)
  : SetPreIncidence Points Lines.
  unfold PreIncidence in spi.
  unfold SetPreIncidence.
  unfold incl.
  induction spi as [fn is].
  unfold subsets_set.
  simpl.
  exists (λ line, pr1 (fn line)).

Definition increl {Points Lines}
  (structure : PreIncidence Points Lines)
  : Points -> Lines -> hProp.
  induction structure.
  intros point line.
  exact ((pr1 line) point).
Defined.

Definition increl' {Points Lines}
  (structure : PreIncidence Points Lines)
  : Lines -> Points -> hProp.
  intros line point.
  exact ((increl structure) point line). 
Defined.

Coercion lineset : PreIncidence >-> Funclass.
Coercion increl : PreIncidence >-> Funclass.

Definition incidences {Points Lines : hSet}
  (structure : PreIncidence Points Lines):
  linesover (Points × Lines).
  unfold linesover.
  unfold subtype_set.
  simpl.
  unfold hsubtype.
  intro; induction X as [point line].
  exact ((increl structure) point line).
Defined.
                 
(* Coercion incidences : PreIncidence >-> pr1hSet. *)

Definition lineset {Points Lines : hSet}
  (structure : PreIncidence Points Lines):
  hSet.


Coersion lineset : PreIncidence >-> pr1hSet.


Definition Hitpre : PreIncidence unitset unitset.
  unfold PreIncidence.
  unfold incl.
  unfold hsubtype.
  exists (λ _, λ _, htrue).
  apply isinclfromunit .
  exact (isasethsubtype unitset).
Defined.

Definition Misspre : PreIncidence unitset unitset.
  unfold PreIncidence.
  unfold incl.
  unfold hsubtype.
  exists (λ _, λ _, hfalse).
  apply isinclfromunit .
  exact (isasethsubtype unitset).
Defined.

Definition linesinhabited {Points Lines}
  (pointson : PreIncidence Points Lines)
  :
  UU :=
  ∏ l1: Lines,
    subtype_notEqual (pointson l1) (emptysubtype Points).

Definition IncidenceStructure (Lines Points: hSet) : UU
  := ∑ inc : PreIncidence Lines Points,
     linesinhabited inc.

Definition preincidence {Lines Points} :
  IncidenceStructure Lines Points -> PreIncidence Lines Points
  := pr1.
Coercion preincidence
  : IncidenceStructure >-> PreIncidence.

Definition isincidence {Lines Points}
  (inc: IncidenceStructure Lines Points)
  : linesinhabited (preincidence inc).
  induction inc.
  exact pr2.
Defined.

Coercion isincidence : IncidenceStructure >-> linesinhabited.

Definition Hit : IncidenceStructure unitset unitset.
  exists Hitpre.
  unfold linesinhabited.
  intro.
  induction l1.
  simpl.
  unfold ishinh_UU.
  intros.
  apply X.
  left.
  intros.
  apply X0.
  exists tt.
  split.
  exact tt.
  unfold neg.
  intros.
  exact X1.
Defined.

Definition TwoHitspre : PreIncidence
                       hPropset
                       unitset.
  unfold PreIncidence.
  unfold incl.
  exists (λ _, (λ _, htrue)).
  apply isinclfromunit.
  simpl.
  exact (isasethsubtype hPropset).
Defined.

Definition TwoHits : IncidenceStructure
                       hPropset
                       unitset.   
  exists TwoHitspre.
  unfold linesinhabited.
  intro.
  induction l1.
  simpl.
  unfold ishinh_UU.
  intros.
  apply X.
  left.
  intros.
  apply X0.
  exists htrue.
  (* exists hfalse. *)
  split. exact tt.
         unfold neg; intro falsity; apply falsity.
Defined.

Definition TrueHitpre : PreIncidence hPropset unitset.
  exists (λ _,
      (* the line goes through true, but not false *)
      (λ bb: hPropset, bb)).
  apply isinclfromunit.
  exact (isasethsubtype hProp).
Defined.
  
Definition FalseHitpre : PreIncidence hPropset unitset.
  exists (λ _,
      (* the line goes through true, but not false *)
      (λ bb: hPropset, (hneg (hProptoType bb)))).
  apply isinclfromunit.
  exact (isasethsubtype hProp).
Defined.

Definition TrueHit: IncidenceStructure hPropset unitset.
  exists TrueHitpre.
  unfold linesinhabited.
  intros.
  induction l1.
  simpl.
  unfold ishinh_UU.
  intros.
  apply X.
  left.
  intros; apply X0.
  exists htrue.
  split.
  exact tt.
  unfold neg.
  intro falsity; exact falsity.
Defined.

Definition FalseHit: IncidenceStructure hPropset unitset.
  exists FalseHitpre. 
  unfold linesinhabited.
  intros.
  induction l1.
  simpl.
  unfold ishinh_UU.
  intros.
  apply X.
  left.
  intros; apply X0.
  exists hfalse.
  split;
    unfold neg;
    intros;
    exact X1.
Defined.

Definition DoubleHitpre : PreIncidence
                            hPropset
                            unitset.
  exists (λ _, λ _, htrue).
  simpl.
  apply isinclfromunit.
  exact (isasethsubtype hProp).
Defined.

Definition DoubleHit : IncidenceStructure
                         hPropset
                         unitset.
  exists DoubleHitpre.
  unfold linesinhabited.
  intro.
  induction l1.
  simpl.
  unfold ishinh_UU.
  intros.
  apply X.
  left.
  intros.
  apply X0.
  exists htrue.
  split.
  - exact tt.
  - unfold neg. intro falsity.
    exact falsity.
Defined.

Theorem AllIncidencesAreEquivalent {Points} {Lines}
  (ii1 ii2 : IncidenceStructure Points Lines)
  : ii1  ii2.

Definition TwoLoops : PreIncidence
                        boolset
                        boolset.
  unfold PreIncidence.
  simpl.
  unfold hsubtype.
  exists (λ bb1,λ bb2,
      ishinh (bb1 = bb2)).
      
  apply isinclweqonpaths.
  
  

  
