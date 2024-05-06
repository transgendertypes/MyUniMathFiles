Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Equivalences.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Section iRelation.
  Context (Points Lines : UU).

  Definition iRelation := Points -> Lines -> UU.

End iRelation.

Section Polarity.
  Context {Points Lines : UU}.

  Definition polarity (incidence: iRelation Points Lines)
    : iRelation Lines Points. 
    exact (λ line, λ point, incidence point line).
  Defined.
End Polarity.

Section Composition.
  Context {Points Points' Lines Lines' Faces : UU}.

  Definition icompose (lower : iRelation Points Lines) (higher : iRelation Lines Faces)
    : iRelation Points Faces.
  unfold iRelation in lower,higher.
  unfold iRelation.
  intros point face.
  exact (∑ edges : Lines,
            lower point edges × higher edges face).
  Defined.

  Definition _2relation: UU
    :=     ∑ lower : iRelation Points Lines,
            ∑ higher : iRelation Lines Faces,
              ∑ composition : iRelation Points Faces,
                icompose lower higher = composition. 

  Definition make_2relation (lower : iRelation Points Lines) (higher : iRelation Lines Faces)
    : _2relation.
    exists lower. exists higher. exists (icompose lower higher).
    exact (idpath _).
  Defined.

  (* incidence structures are like fibrations in a model category, in the sense that
we can compose them with weak equivalences.  Yet, an incidence relation is never a weak
equivalence. *)
  Definition iweq_left {PP PP' LL}
    (weq : weq PP PP')
    :
    iRelation PP LL -> iRelation PP' LL.
    intro incidence.
    exact (λ point, λ line, incidence ((invmap weq) point) line).
  Defined.

  Definition iweq_right {PP LL LL'}
    (weq : weq LL LL' )
    : iRelation PP LL -> iRelation PP LL'.
    intro incidence.
    exact (λ point, λ line, incidence point ((invmap weq) line)).
  Defined.

  Lemma iweq_assoc :
    ∏ incidence : iRelation Points Lines,
        ∏ weqp : weq Points Points',
          ∏ weql : weq Lines Lines',

            (iweq_left weqp ( iweq_right weql incidence ))
            = (iweq_right weql (iweq_left weqp incidence)). 
    intros.
    unfold iweq_left, iweq_right.
    exact (idpath _).
  Defined.

  Definition iweqcompose (lower : iRelation Points Lines)
                         (weq : weq Lines Lines')
                         (higher : iRelation Lines' Faces)
     : iRelation Points Faces.
    unfold iRelation in lower,higher.
    unfold iRelation.
    intros point face.
    exact (∑ line : Lines,
              lower point line ×
                higher (weq line) face).
  Defined.
End Composition.

Section Polarity_Basics.
  Theorem polarity_own_inverse :
    ∏ Points Lines : UU,
        ∏ incidence : iRelation Points Lines,
          (polarity (polarity incidence)) = incidence.
    intros.
    exact (idpath incidence).
  Defined.

  (* In the polarity composition, the incidence of pp1 pp2
     are ∑ ll : Lines, pp1 and pp2 are coincident on ll *)
  Definition polarity_composition {Points Lines}
    : iRelation Points Lines -> iRelation Points Points :=
    (λ relation, icompose relation (polarity relation)). 
                
End Polarity_Basics.
Section SubRelation.
  Context {Points Lines: UU}.

  Definition isasubrelation
    (incidence subincidence : iRelation Points Lines) :=
    ∏ point: Points,
        ∏ line: Lines,
          subincidence point line -> incidence point line.

  Notation isanextension incidence superincidence := (isasubrelation superincidence incidence).

  Definition ilogeq (incidence1 incidence2 : iRelation Points Lines) :=
                                  isasubrelation incidence1 incidence2
                                × isanextension  incidence1 incidence2.                

  Definition iunrelation : iRelation Points Lines.
    exact (λ point, λ line, ∅).
  Defined.

  Definition iunitrelation : iRelation Points Lines.
    exact (λ point, λ line, unit).
  Defined.

  Lemma unit_check : ilogeq iunitrelation iunitrelation.
    split.
    unfold isasubrelation; intros.
    exact tt.
    unfold isanextension; intros.
    exact tt.
  Defined.
  
  Lemma un_check : ilogeq iunrelation iunrelation.
    split.
    unfold isanextension; intros.
    inversion X.
    unfold isanextension; intros.
    inversion X.
  Defined.

  Lemma unrelation_isasubrelation : ∏ incidence : iRelation Points Lines,
        isasubrelation incidence iunrelation.
    intros.
    unfold isasubrelation.
    intros.
    inversion X.
  Defined.

  Lemma unitrelation_isanextension : ∏ incidence : iRelation Points Lines,
        isanextension incidence iunitrelation.
    intros.
    unfold isanextension.
    unfold isasubrelation.
    intros.
    exact tt.
  Defined.

End SubRelation.

Section Coproduct.

  Context {Points Lines : UU}.
  Definition icoprod
    (incidence1 incidence2 : iRelation Points Lines)
    : iRelation Points Lines.
    unfold iRelation.
    intros point line.
    exact (coprod (incidence1 point line) (incidence2 point line)).
  Defined.

  Definition icopi1 {incidence1 incidence2 : iRelation Points Lines}:
    ∏ point: Points,
        ∏ line: Lines,
          incidence1 point line -> (icoprod incidence1 incidence2) point line.
    intros.
    left; assumption.
  Defined.

  Definition icopi2 {incidence1 incidence2 : iRelation Points Lines} :
    ∏ point: Points,
        ∏ line: Lines,
          incidence2 point line -> (icoprod incidence1 incidence2) point line.
    intros.
    right; assumption.
  Defined.
    
End Coproduct.

Section Product.
  Context {Points Lines : UU}.
  
  Definition itimes
    (incidence1 incidence2 : iRelation Points Lines)
    : iRelation Points Lines.
    unfold iRelation.
    intros point line.
    exact ((incidence1 point line) × (incidence2 point line)).
  Defined.

  Definition ipi1 {incidence1 incidence2 : iRelation Points Lines}
    : ∏ point : Points, ∏ line: Lines,
          (itimes incidence1 incidence2) point line -> incidence1 point line.
    intros.
    exact (pr1 X).
  Defined.

  Definition ipi2 {incidence1 incidence2 : iRelation Points Lines}
    : ∏ point : Points, ∏ line: Lines,
          (itimes incidence1 incidence2) point line -> incidence2 point line.
    intros.
    exact (pr2 X).
  Defined.

End Product.

Section OverUnder.
  Definition iRelationOver (Points : UU) :=
    ∑ Lines : UU, iRelation Points Lines.
  Definition iRelationUnder (Lines : UU) :=
    ∑ Points : UU, iRelation Points Lines.

  Definition toOver {Points Lines}
    : iRelation Points Lines -> iRelationOver Points.
    intro.
    exists Lines.
    exact X.
  Defined.
  Definition toUnder {Points Lines}
    : iRelation Points Lines -> iRelationUnder Lines.
    intro.
    exists Points.
    exact X.
  Defined.

  Definition dircoprod_over {Points : UU} :
    iRelationOver Points -> iRelationOver Points -> iRelationOver Points.
    unfold iRelationOver; intros.
    induction X as [Lines1 rel1].
    induction X0 as [Lines2 rel2].
    exists (coprod Lines1 Lines2).
    unfold iRelation; intros.
    induction X0.
    + exact (rel1 X a).
    + exact (rel2 X b).
  Defined.

  Definition dirprod_over {Points : UU} :
    iRelationOver Points -> iRelationOver Points -> iRelationOver Points.
    unfold iRelationOver; intros.
    induction X as [Lines1 rel1].
    induction X0 as [Lines2 rel2].
    exists (Lines1 × Lines2).
    unfold iRelation; intros.
    induction X0.
    exact (rel1 X pr1 × rel2 X pr2).
  Defined.

  Definition dircoprod_under {Lines : UU} :
    iRelationUnder Lines -> iRelationUnder Lines -> iRelationUnder Lines.
    unfold iRelationUnder; intros.
    induction X as [Points1 rel1].
    induction X0 as [Points2 rel2].
    exists (coprod Points1 Points2).
    unfold iRelation; intros.
    induction X.
    + exact (rel1 a X0).
    + exact (rel2 b X0).
  Defined.

  Definition dirprod_under {Lines : UU} :
    iRelationUnder Lines -> iRelationUnder Lines -> iRelationUnder Lines.
    unfold iRelationUnder; intros.
    induction X as [Points1 rel1].
    induction X0 as [Points2 rel2].
    exists (Points1 × Points2).
    unfold iRelation; intros.
    induction X.
    exact (rel1 pr1 X0 × rel2 pr2 X0).
  Defined.

  (* From two incidence structures over (under) the same type of points (lines),
     we can form their "swizzle product": for every pair of lines (points), coming
     from the cartesian product of the unequal types of the pairing, the lines (points)
     fall on the point (line) if *either* of the original lines (points) did.
*)
  Definition swizzle_product_under {Lines : UU} :
    iRelationUnder Lines -> iRelationUnder Lines -> iRelationUnder Lines.
    unfold iRelationUnder; intros.
    induction X as [Points1 rel1].
    induction X0 as [Points2 rel2].
    exists (Points1 × Points2).
    unfold iRelation; intros.
    induction X.
    exact (coprod (rel1 pr1 X0) (rel2 pr2 X0)).
  Defined.

  Definition swizzle_product_over {Points : UU} :
    iRelationOver Points -> iRelationOver Points -> iRelationOver Points.
    unfold iRelationOver; intros.
    induction X as [Lines1 rel1].
    induction X0 as [Lines2 rel2].
    exists (Lines1 × Lines2).
    unfold iRelation; intros.
    induction X0.
    exact (coprod (rel1 X pr1) (rel2 X pr2)).
  Defined.

  Definition compose_overunder {Edges}
    (lower : iRelationUnder Edges)
    (higher: iRelationOver Edges)
        : ∑ Points Faces : UU, iRelation Points Faces.
    induction lower as [Points lower].
    induction higher as [Faces higher].
    exists Points. exists Faces.
    exact (icompose lower higher).
  Defined.
End OverUnder.

Section Utilities.

  Context {Points Points' Lines Lines' Faces Faces' : UU}.

  Context (Pointsonlines : iRelation Points Lines).
  Context (Linesonpoints : iRelation Lines Points).
  Context (Linesonfaces : iRelation Lines Faces).
  Context (Facesonlines : iRelation Faces Lines).
  Context (Pointsonfaces : iRelation Points Faces).
  Context (Facesonpoints : iRelation Faces Points).
  Context (Pointsonlines2 : iRelation Points Lines).
  Context (Linesonpoints2 : iRelation Lines Points).
  Context (Linesonfaces2 : iRelation Lines Faces).
  Context (Facesonlines2 : iRelation Faces Lines).
  Context (Pointsonfaces2 : iRelation Points Faces).
  Context (Facesonpoints2 : iRelation Faces Points).

  Context (Overpoints : iRelationOver Points).
  Context (Underpoints : iRelationUnder Points).
  Context (Overlines : iRelationOver Lines).
  Context (Underlines : iRelationUnder Lines).
  Context (Overfaces : iRelationOver Faces).
  Context (Underfaces : iRelationUnder Faces).
            
  Context (Overpoints2 : iRelationOver Points).
  Context (Underpoints2 : iRelationUnder Points).
  Context (Overlines2 : iRelationOver Lines).
  Context (Underlines2 : iRelationUnder Lines).
  Context (Overfaces2 : iRelationOver Faces).
  Context (Underfaces2 : iRelationUnder Faces).


  Definition points (rel : iRelation Points Lines) := Points.
  Definition facets (rel : iRelation Points Lines) := Lines.
  Definition lines (rel : iRelation Points Lines) := Lines.
  Definition edges (rel : iRelation Points Lines) := Lines.

  Definition incidences (rel : iRelation Points Lines) :=
    ∑ pp : Points, ∑ ll : Lines, rel pp ll.

  Definition cayley (rel : iRelation Points Lines)
    : iRelation (coprod Points Lines) (incidences rel).
    unfold iRelation.
    intros.
    rename X0 into incidence.
    induction incidence as [point [line incidence]].
    induction X.
    exact (a = point).
    exact (b = line).
  Defined.

  Definition lr_weq
               {PP LL PP' LL'}
    (weql : weq PP PP')
    (weqr : weq LL LL')

    : iRelation PP LL -> iRelation PP' LL'.
    intro rel.
    exact (iweq_left weql (iweq_right weqr rel)).
  Defined.

  Lemma iweql_lemma ( y : iRelation Points' Lines ) (path : weq Points Points') :
    ∑ x : iRelation Points Lines,
         (λ (point : Points') (line : Lines), x (invmap path point) line) = y.
      + exists (iweq_left (invweq path) y).
        unfold invweq,invmap,iweq_left.
        simpl.
        unfold invmap.
        unfold make_weq.
        simpl.
        unfold weqccontrhfiber.
        unfold weqproperty.
        unfold iscontrpr1.
        unfold hfiberpr1.
        induction path.
        simpl.
        apply funextfun; unfold homot; intro.
        apply funextfun; unfold homot; intro.
        simpl.
        induction pr2.
        simpl.
        induction pr0.
        simpl.
        rewrite pr4.
        exact (idpath _).
     Defined.

  Definition icurry : iRelation Points Lines ->
                      (Points × Lines) -> UU.
    intro relation.
    exact (λ product, relation (pr1 product) (pr2 product)).
  Defined.
  Definition iuncurry (relation : Points × Lines -> UU) : iRelation Points Lines.
    exact

 (λ point, λ line, relation (point,, line)).
  Defined.

  Definition curryeq : Equivalence (iRelation Points Lines) (Points × Lines -> UU).
    unfold Equivalence.
    exists icurry.
    unfold isEquivalence.
    exists iuncurry.
    exists (λ _, idpath _).
    exists (λ _, idpath _).
    intro.
    exact (idpath _).

  Defined.
  Definition curry_path : (iRelation Points Lines) = (Points × Lines -> UU).
    apply univalence.
    apply Equivalence_to_weq. 
    exact curryeq.
  Defined.
        
  Definition iweql : weq Points
                         Points'
                   -> weq (iRelation Points Lines)
                         (iRelation Points' Lines).
    intro.
    unfold weq.
    exists (iweq_left X).
    - 
      unfold iweq_left.
      refine (isweq_iso
                (λ (incidence : iRelation Points Lines)
                   (point : Points') (line : Lines),
                  incidence (invmap X point) line)
                (λ (incidence : iRelation Points' Lines)
                (point : Points) (line : Lines),
               incidence (X point) line)
        _ _).
      intros.
      apply funextfun; unfold homot; intro.
      apply funextfun; unfold homot; intro.
      rewrite <- (homotinvweqweq0 X). 
      exact (idpath _).
      
      intros.
      apply funextfun; unfold homot; intro.
      apply funextfun; unfold homot; intro.
      rewrite homotweqinvweq.
      exact (idpath _).
  Defined.

  Theorem isweq_lr_weq
    (weql : weq Points Points')
    (weqr : weq Lines Lines')
    : isweq (lr_weq weql weqr).
    refine (isweq_iso (lr_weq weql weqr) (lr_weq (invweq weql) (invweq weqr) : iRelation Points' Lines' -> iRelation Points Lines) _ _).
    intro.
    apply funextfun; unfold homot; intro.
    apply funextfun; unfold homot; intro.
    unfold lr_weq , iweq_left , iweq_right.
    rewrite invinv.
    rewrite <- homotinvweqweq0.
    rewrite invinv.
    rewrite <- homotinvweqweq0.
    exact (idpath _).
    intro.
    apply funextfun; unfold homot; intro.
    apply funextfun; unfold homot; intro.
    unfold lr_weq.
    unfold lr_weq , iweq_left , iweq_right.
    rewrite invinv.
    rewrite invinv.
    rewrite homotweqinvweq.
    rewrite homotweqinvweq.
    exact (idpath _).
  Defined.

  Definition raise_weq 
    (weqlweqr : weq Points Points' ×
                weq Lines Lines')
                : weq (iRelation Points Lines) (iRelation Points' Lines').
    
    induction weqlweqr as [weql weqr].
    unfold weq.
    exists (lr_weq weql weqr).
    exact (isweq_lr_weq weql weqr).
  Defined.

  Definition lower_weq (idPoints : weq Points Points') (idLines : weq Lines Lines')  
                : weq (iRelation Points Lines) (iRelation Points' Lines') ->
    weq Points Points' ×
                weq Lines Lines'.
    intros.
    split.
    unfold iRelation in X.
    Abort.
  (* of course this and the next lemma are impossible. After all, polar incidence is a weak equivalence of incidence structures, which
     does not give rise to corresponding weak equivalence of the underlying Points and Lines spaces *) 
    

  Definition isweq_raise_weq : weq (weq Points Points' × weq Lines Lines') (weq (iRelation Points Lines) (iRelation Points' Lines')).
    unfold weq.
    exists raise_weq.
    refine (isweq_iso raise_weq _ _ _).
    Abort.
  (* What we are trying to do is form a model category in which the fibrations are ways of "building up" polytopes,
    and the cofibrations are ways of "tearing down" polytopes, with the usual weak equivalences playing the role of equivalence
   It isn'trivial clear there are "enough" fibrations and cofibrations in reality to form auto model category, but it is easy to
   find the classes of distinguished morphisms and indeed construct a category with these morphisms.*)

End Utilities.

Section IncidenceStructures.
  
  (* The incidence structures themselves are the incidences of the following incidence relation *)

  Definition IncidenceStructures : iRelation UU UU.
    exact (λ Points, λ Lines, iRelation Points Lines).
  Defined.
  Definition IncidenceStructure := incidences IncidenceStructures.

  Definition structures {Points Lines} : iRelation Points Lines -> IncidenceStructures Points Lines. 
    intro relation. exact relation.
  Defined.
  Definition structure {Points Lines} : iRelation Points Lines -> IncidenceStructure. 
    intro relation. exists Points. exists Lines. exact relation.
  Defined.
  Coercion structure : iRelation >-> IncidenceStructure.
  Coercion structures : iRelation >-> IncidenceStructures.

  Definition iRelationFromIncidenceStructure : IncidenceStructure -> ∑ Points Lines, iRelation Points Lines.
    unfold IncidenceStructure.
    unfold incidences.
    intros.
    induction X as [points [lines structure]].
    exists points. exists lines.
    exact structure.
  Defined.

  Definition iRelationFromiStructure (structure : IncidenceStructure) := pr2 (pr2 (iRelationFromIncidenceStructure structure)).

  Coercion iRelationFromiStructure : IncidenceStructure >-> iRelation.

  Definition ipoints : IncidenceStructure -> UU.
    unfold IncidenceStructure.
    unfold incidences.
    intros.
    exact (pr1 X).
  Defined.

  Definition ilines : IncidenceStructure ->   UU.
    unfold IncidenceStructure.
    unfold incidences.
    intros.
    exact (pr1 (pr2 X)).
  Defined.

  Example iHit : IncidenceStructure.
  exists unit.
  exists unit.
  exact (λ point, λ line, unit).
  Defined.

  Example iHit2 : IncidenceStructure.
  exists unit.
  exists unit.
  exact (structures (icompose (λ point: unit, λ line: unit, unit) (λ point: unit, λ line: unit, unit))).
  Defined.

  Example iBox (Value : UU) : IncidenceStructure.
  exists unit.
  exists unit.
  exact (λ _ _, Value).
  Defined.

  Example iMiss : IncidenceStructure.
  exists unit.
  exists unit.
  exact (λ point, λ line, empty).
  Defined.

  Example iEmpty : IncidenceStructure.
  exists empty.
  exists empty.
  exact fromempty.
  Defined.
  
  (* This is  the beautiful part *)
  Definition Incidence2Structures := icompose IncidenceStructures IncidenceStructures. 

  Definition Incidence2Structure := incidences Incidence2Structures.

  Example hit2 : Incidence2Structure.
  exists unit.
  exists unit.
  exists unit.
  split;
  exact (λ _, λ _, unit).
  Defined.

  Definition Paths : iRelation UU UU
    := (λ X, λ Y, X = Y). 

  Definition Path := incidences Paths.

  Definition Weqs : iRelation UU UU
    := (λ X, λ Y, weq X Y). 

  Definition wApply {X Y} : Weqs X Y -> (X -> Y) := pr1.
  
  Coercion wApply : Weqs >-> Funclass.

  Definition Weq := incidences Weqs.

  Definition Identity (X : UU) : Path.
    exists X. exists X. exact (idpath X).
  Defined.

  (* This subsection collects various other abstract incidence structures
     of general interest, though not as important for our present purposes
     as the IncidenceStructures or Paths structures *) 

  (* In the "proofs are functions" paradigm, incidences in 'proofs' are proofs *)
  Definition Proofs : iRelation UU UU :=
    λ Context, λ Proposition, Context -> Proposition.

  Definition Proof := incidences Proofs.

  Definition Nonequals (Points : UU) : iRelation Points Points :=
    λ p1, λ p2, p1 != p2.

  Definition distinct_pair_of (Points: UU) := incidences (Nonequals Points).

  Definition Propertied (Points : UU) : iRelation Points (Points -> UU) :=

    λ point, λ property, property point.

  Definition PJudgment (Points: UU) := incidences (Propertied Points).

  Definition Coproducts : iRelation UU UU :=
    λ X, λ Y, coprod X Y.

  Definition Coproduct := incidences Coproducts.

  Definition Products : iRelation UU UU :=
    λ X, λ Y,  X × Y.

  Definition Product := incidences Products.

  Definition iEquivalences_covariant {Points Lines Points' Lines'} :
    iRelation (iRelation Points Lines) (iRelation Points' Lines') :=
    λ X, λ Y,
      ∑ point_path : Weqs Points Points',
      ∑ line_path  : Weqs Lines  Lines',
      ∑ inci_path  : Weqs (incidences X) (incidences Y),
            ∏ incidence :incidences X,
            ∑ incidence' : incidences Y, 
          (inci_path incidence = incidence')
            × (point_path
                 (pr1 incidence) = (pr1 incidence'))
            × (line_path
                 (pr1 (pr2 incidence)) = (pr1 (pr2 incidence'))).

  Definition iEquivalences_contravariant {Points Lines Points' Lines' : UU} :
    iRelation (iRelation Points Lines) (iRelation Lines' Points') :=
    λ X, λ Y,
      ∑ point_path : Weqs Points Points',
      ∑ line_path  : Weqs Lines  Lines',
      ∑ inci_path  : Weqs (incidences X) (incidences Y),
            ∏ incidence :incidences X,
            ∑ incidence' : incidences Y, 
          (inci_path incidence = incidence')
            × (point_path
                 (* Note the differences here, and in the type signature *)
                 (pr1 incidence) = (pr1 (pr2 incidence')))
            × (line_path
                 (pr1 (pr2 incidence)) = (pr1 incidence')).

  Definition coEquivalences : iRelation IncidenceStructure IncidenceStructure.
    unfold iRelation.
    intros.
    unfold IncidenceStructure in X,X0.
    induction X as [Points [Lines Incidence]].
    induction X0 as [Points' [Lines' Incidence']].
    unfold IncidenceStructures in Incidence', Incidence.
    exact (iEquivalences_covariant Incidence Incidence').
  Defined.
  Definition contraEquivalences : iRelation IncidenceStructure IncidenceStructure.
    unfold iRelation.
    intros.
    unfold IncidenceStructure in X,X0.
    induction X as [Points [Lines Incidence]].
    induction X0 as [Lines' [Points' Incidence']].
    unfold IncidenceStructures in Incidence', Incidence.
    exact (iEquivalences_contravariant Incidence Incidence').
  Defined.
  Definition coEquivalence := incidences coEquivalences.
  Definition contraEquivalence := incidences coEquivalences.


  (* Notice how weak this definition of equivalence is.    *)
  Lemma  fn_for_next_example : (incidences (λ _ _ : unit, unit)) -> (incidences (icompose iHit iHit)).
    unfold incidences, icompose, iHit. intro.
    exists tt.
    exists tt.
    exists tt.
    split.
    split.
    split.
  Defined.
  
  Lemma fn_for_next_example_isweq : isweq fn_for_next_example.
    unfold isweq.
    intro.
    unfold hfiber.
    simpl.
    unfold iscontr.
    simpl.
    unfold incidences.
    assert (∑ x : ∑ _ _ : unit, unit, fn_for_next_example x = y).
    -
    exists (tt,, tt,, tt).
    induction y.
    induction pr1.
    simpl.
    unfold fn_for_next_example.
    induction pr2.
    induction pr2.
    induction pr2.
    induction pr1.
    induction pr0.
    induction pr2.
    induction pr3.
    apply idpath.
    -
    exists X. 
    intros.
    induction X,t.
    induction pr1,pr2.
    induction pr0.
    induction pr2,pr4.
    induction pr0.
    induction pr2.
    induction pr5.
    induction pr1.
    induction pr4.
    induction pr6.
    simpl in pr3.
    unfold fn_for_next_example in pr3.
  Abort.
  (* maybe it is stronger than i thought...*) 
  Lemma  for_next_example : Weqs (incidences (λ _ _ : unit, unit)) (incidences (icompose iHit iHit)).
      unfold Weqs.
      Abort.
  Example truncation_is_equivalence : coEquivalence.
  exists iHit.
  exists (icompose iHit iHit).
  unfold coEquivalences.
  exists (idweq _).
  exists (idweq _).
  simpl.
     Abort.

  Definition lemma_Univalence :((∑ (pp ll : UU) (f : pp → ll), isweq f) → ∑ pp ll : UU, pp = ll).
    intro.
    induction X as [X [X' [path isweqpath]]].
    pose proof (path,, isweqpath).
    apply univalence in X0.
    exists X. exists X'. exact X0.
  Defined.

  Definition lemma_Univalence' :(∑ pp ll : UU, pp = ll) -> ∑ (pp ll : UU) (f : pp → ll), isweq f.
    intro.
    induction X as [X [X' path]].
    exists X. exists X'.
    apply univalence.
    exact path.
  Defined.

  Definition lemma_q : ∏ x : ∑ pp ll : UU, pp ≃ ll, lemma_Univalence' (lemma_Univalence x) = x.
    intros.
    unfold lemma_Univalence.
    unfold lemma_Univalence'.
    simpl.
    induction x as [X [X' path]].
    Abort.

  Definition lemma_p : ∏ y : ∑ pp ll : UU, pp = ll, lemma_Univalence (lemma_Univalence' y) = y.
    intros.
    unfold lemma_Univalence.
    unfold lemma_Univalence'.
    simpl.
    induction y as [X [X' path]].
    refine (total2_paths2_f _ _).
    unfold transportf.
    simpl.
    Unshelve. Focus 2.
    apply idpath.
    simpl.
    refine (total2_paths2_f _ _).
    simpl.
    Unshelve. Focus 2.
    apply idpath.
    simpl.
    unfold eqweqmap.
    simpl.
    unfold paths_rect, idweq.
    simpl.
    Abort.
 


  Definition Univalence : Weq.
    exists Weq.
    exists Path.
    unfold Weq, Path, incidences, Weqs, Paths.
    exists lemma_Univalence.
    unfold isweq.
    unfold lemma_Univalence.
    intro.
    unfold hfiber.
  admit.
  Admitted.

  Definition PathTypes : IncidenceStructure.
    exists UU.
    exists UU.
    exact (λ X Y, ∑ type : UU, type = (X = Y)).
  Defined.

  Definition PathType := incidences (pr2 (pr2 PathTypes)).

  Definition ringsum : binop PathType.
    unfold binop, PathType, incidences.
    intros.
    unfold iRelationFromIncidenceStructure.
    unfold iRelationFromIncidenceStructure in X0, X.
    induction X as [X [X' pathtypeX]].
    induction X0 as [Y [Y' pathtypeY]].
    exists (X ⨿ Y).
    exists (X' ⨿ Y').
    unfold PathTypes.
    simpl.
    exists (X ⨿ Y = X' ⨿ Y').
    apply idpath.
  Defined.

  Definition ringprod : binop PathType.
    unfold binop, PathType, incidences.
    intros.
    unfold iRelationFromIncidenceStructure.
    unfold iRelationFromIncidenceStructure in X0, X.
    induction X as [X [X' pathtypeX]].
    induction X0 as [Y [Y' pathtypeY]].
    exists ((X × Y) ⨿ (X' × Y')).
    exists ((X' × Y) ⨿ (X × Y')).
    unfold PathTypes.
    simpl.
    exists ((X × Y) ⨿ (X' × Y') = (X' × Y) ⨿ (X × Y')).
    apply idpath.
  Defined.
  Definition ringnegation : PathType -> PathType.
    unfold PathType, incidences. simpl.
    intro.
    induction X as [X [Y path]].
    exists Y. exists X.
    exists (Y = X).
    apply idpath.
  Defined.

  Definition ringzero : PathType.
    exists ∅.
    exists ∅.
    simpl.
    exists (∅ = ∅).
    apply idpath.
  Defined.

  Definition ringone : PathType.
    exists ∅.
    exists unit.
    simpl.
    exists (∅ = unit).
    apply idpath.
  Defined.

  Definition ptype : PathType -> UU.
    intro.

    induction X.
    simpl in pr1.
    induction pr2.
    simpl in pr2.
    induction pr2.
    exact pr2.
  Defined.

  Coercion ptype : PathType >-> UU.

  Theorem zero_inhabited : ishinh ringzero.
    unfold ringzero.
    unfold ishinh.
    unfold ishinh_UU.
    unfold make_hProp.
    simpl.
    intros.
    apply X.
    apply idpath.
  Defined.

  Theorem mere_negation : ∏ pathtype : PathType,
     ishinh (ringsum pathtype (ringnegation pathtype)).
    intros.
    induction pathtype as [X [Y Path]].
    unfold ringsum.
    unfold ringnegation.
    unfold ringzero.
    unfold ishinh.
    unfold ishinh_UU. simpl.
    intros.
    apply X0.
    (* apply idpath. *)
    
    apply univalence.
    apply weqcoprodcomm.
   
  Defined.

  Lemma rdistrcoprod {X Y Z} :(X × Y) ⨿ (X × Z) = (X × (Y ⨿ Z)).
    apply univalence.
    exact (weqrdistrtoprod X Y Z).
  Defined.

  Theorem directsum_to_ringprod : ∏ X Y : PathType,
       (ptype X) ⨿ (ptype Y) -> ptype (ringprod X Y).
    intros.
    unfold ptype in X0.
    simpl in X0.
    induction X as [X [X' Xpath]].
    induction Y as [Y [Y' Ypath]].
    unfold ptype.
    induction Ypath as[ypath yrest]. 
    induction Xpath as[xpath xrest]. 
    simpl in X,X',Y,Y',xpath,ypath.
    rewrite xrest in X0. rewrite yrest in X0.
    simpl.
    induction X0.
    - rewrite a. apply idpath.
    - rewrite b. apply univalence. exact (weqcoprodcomm (X × Y') (X' × Y')).
  Defined.

  Theorem ringdistributive : ∏ x y z : PathType,
        ptype (ringprod x (ringsum y z)) = ptype (ringsum (ringprod x y) (ringprod x z)).
    intros.
    unfold ringprod, ringsum, ptype.
    simpl.
    induction x as [x [x' xpath]].
    induction y as [y [y' ypath]].
    induction z as [z [z' zpath]].
    simpl.
    rewrite <- rdistrcoprod.
    rewrite <- rdistrcoprod.
    rewrite <- rdistrcoprod.
    rewrite <- rdistrcoprod.
    (* this is  clearly solvable but tedious. *) 
    admit.
  Admitted.

  Theorem ringcommutative :  ∏ x y : PathType,
        ptype (ringprod x y) = ptype (ringprod y x).
        unfold ptype.
        intros.
        induction x as [x [x' [xpath xxx]]].
        induction y as [y [y' [ypath yyy]]].
        simpl.
        (* again, this intros  highly tedious. *)
        (* of course, I'll want to come back and prove these. todo *)
        admit.
  Admitted.

  Theorem mere_annihilation : ∏ x : PathType,
        ishinh (ptype (ringprod x ringzero)).
    intro path. induction path as [x [x' [path ppp]]].
    unfold ishinh.
    unfold ringprod.
    simpl.
    unfold ishinh_UU.
    unfold ptype.
    intros.
    apply X.
    apply univalence. exact (weqcoprodcomm _ _).
  Defined.

  (* instead of hprop, a "subset" of the ring  takes values in the ring  *)
  (* this isa sort of self-sheafification *)
  Definition subtype_of_pathring : UU := PathType -> PathType.
  Definition UUideal : UU :=
    ∑ ideal : UU -> UU,
        ∏ x y : UU,
          ((ideal x) × (ideal y) -> ideal (x × y))
            × ((ideal x) ⨿ (ideal y) -> ideal (x ⨿ y)).
  Definition UUidealsubtype : UUideal -> (UU -> UU).
    exact pr1.
  Defined.
  
  Coercion UUidealsubtype : UUideal>->Funclass.

  Definition UUprimeideal : UU :=
    ∑ ideal : UUideal,
        ∏ x y : UU,
          ideal (x × y) ->
          (ideal x) ⨿ (ideal y).

  Definition UUideal_union : UUideal -> UUideal -> UUideal.
    intros x y.
    exists (λ z, x z ⨿ y z).
    intros.
    induction x as [X Xconditions].
    induction y as [Y Yconditions].
    remember (Xconditions x0 y0) as XX.
    simpl.
    induction XX as [XXmult XXadd].
    induction YY as [YYmult YYadd].
          
          

  Definition pathideal: UU :=
    ∑ subtype : subtype_of_pathring,
        ∏ x y : PathType,
          ((subtype x) × (subtype y) -> subtype (ringprod x y))
        × ((subtype x)
         
          
        

  

  



  (**** What follows is  different *)

  Definition add_paths : binop Path.
    unfold binop, Path, incidences, Path.
    intros.
    induction X as [X [X' PathX]].
    induction X0 as [Y [Y' PathY]].
    exists (X ⨿ Y).
    exists (X' ⨿ Y').
    rewrite PathX.
    rewrite PathY.
    apply idpath.
  Defined.

  Definition multiply_paths : binop Path.
    unfold binop, Path, incidences, Path.
    intros.
    induction X as [X [X' PathX]].
    induction X0 as [Y [Y' PathY]].
    exists (X × Y).
    exists (X' × Y').
    rewrite PathX.
    rewrite PathY.
    apply idpath.
  Defined.


  Definition add_commutative {X Y} : add_paths X Y = add_paths Y X.
    induction X as [X [X' PathX]].
    induction Y as [Y [Y' PathY]].
    unfold add_paths.
    simpl.
    pose proof (weqcoprodcomm X Y).
    apply univalence in X0.
    unfold internal_paths_rew_r.
    simpl.
    refine (total2_paths2_f _ _).
    refine (total2_paths2_f _ _).
    Unshelve. Focus 2.
    exact X0.
    simpl.
    Unshelve. Focus 2.
    simpl.
    Unshelve. Focus 1.

  
  
  Definition add_weqs : binop Weq.
    unfold binop, Weq, incidences, Weqs; intros X Y.
    induction X as [X [X' pathX]].
    induction Y as [Y [Y' pathY]].
    exists (X ⨿ Y).
    exists (X' ⨿ Y').
    apply weqcoprodf.
    exact pathX.
    exact pathY.
  Defined.

  Definition multiply_weqs : binop Weq.
    unfold binop, Weq, incidences, Weqs; intros X Y.
    induction X as [X [X' pathX]].
    induction Y as [Y [Y' pathY]].
    exists (X × Y).
    exists (X' × Y').
    apply univalence in pathX.
    apply univalence in pathY.
    apply univalence.
    rewrite pathX. rewrite pathY.
    apply idpath.
  Defined.


  

  (* Since we aren't "allowed" to consider negative types, the definition of
     lines in the affine plane is nonobvious.  The situation is superficially
     similar to algebra in the days of Tartaglia, when negative numbers were
     looked on with ire.

     We choose to represent lines as equations A*X = Y + B, to avoid needing
     to take formal quotients.  The disadvantage is an implicit asymmetry between
     X and Y in the linear equations.

     We are interested in statements about incidence in this structure.
    For instance,  if two lines, l1 l2 each pass through the points p1 p2, then (when)
    are they the same line? 
   *)
  Definition affine_plane_points := UU × UU.
  Definition affine_plane_lines := UU × UU.
  Definition affine_line_equation : affine_plane_lines -> (UU × UU -> UU).
    intros line point.
    induction point as [X Y].
    induction line as [A B].
    exact ((A × X) = (Y ⨿ B)).
  Defined.
  Coercion affine_line_equation: affine_plane_lines >-> Funclass.
    

  Definition affine_plane : IncidenceStructure.
    exists affine_plane_points.
    exists affine_plane_lines.
    exact (λ point, λ line,
            line point). 
  Defined.

  (* 4 * 1 = 3 + 1 *)
  Example finite_examples_are_easy_to_find : incidences affine_plane.
  unfold incidences.
  simpl.
    exists (unit,, unit ⨿ unit ⨿ unit).
    exists (unit ⨿ unit ⨿ unit ⨿ unit,, unit).
    apply univalence.
    apply invweq.
    apply weqtodirprodwithunit.
  Defined.

  (* 2 * nat = nat + 0 *)
  Lemma coprodempty_f {Points : UU} : Points ⨿ ∅ -> Points.
    intro.
    induction X.
    exact a.
    inversion b.
  Defined.
  Lemma coprodempty_b {Points : UU} : Points -> Points ⨿ ∅ .
    intro.
    left. exact X.
  Defined.
  Lemma coprodempty_lemma {Points} : (∏ x : Points ⨿ ∅, coprodempty_b (coprodempty_f x) = x).
    intro.
    induction x.
    apply idpath.
    inversion b.
  Defined.

  Lemma coprodempty {Points : UU} : Points ⨿ ∅ = Points.
    apply univalence.
    apply Equivalence_to_weq.
    unfold Equivalence.
    exists coprodempty_f.
    exists coprodempty_b.
    exists (λ y, idpath y).
    exists coprodempty_lemma.
    intro.
    induction x.
    apply idpath.
    inversion b.
  Defined.
        
  Example encode_mod2 : nat -> (unit ⨿ unit) × nat.
  intros.
  pose proof (natrem X 2) as remainder.
  pose proof (natdiv X 2) as quotient.
  exact (match remainder with 0 => ((inl tt),, quotient)
                             | _ => (inr tt,, quotient) end).
  Defined.

  Example decode_mod2 : (unit ⨿ unit) × nat -> nat.
  intros.
  induction X as [remainder quotient].
  induction remainder.
  - exact (2 * quotient).
  - exact (2 * quotient + 1).
  Defined.

  Example encode_mod2_linverse : ∏ y : unit ⨿ unit × nat, encode_mod2 (decode_mod2 y) = y.
  intro.
  induction y.
  rename pr1 into remainder. rename pr2 into quotient.
  induction remainder.
  - simpl.
    unfold encode_mod2.
    replace 2 with (2 * 1). 
    replace (quotient + quotient) with (2 * quotient).
    rewrite (natdivandmultl _ _ _ (natneqsx0 0)).
    
    simpl.
    unfold natrem.
    induction pr2.
    + apply idpath.
    + simpl.
      unfold nat_rect.
      unfold coprod_rect.
      simpl.
      unfold natlthorgeh.
      unfold natgthorleh.
      simpl.
      induction pr2.
      simpl.
      simpl in IHpr2.
      --  
  

  Example transfinite_examples_oft_involve_fixpoints : incidences affine_plane.
  unfold incidences.
  simpl.
    exists (nat,, nat).
    exists (unit ⨿ unit,, empty).
    apply univalence.
    apply invweq.
    rewrite coprodempty.
    apply Equivalence_to_weq.
    exists encode_mod2.
    exists decode_mod2.
    

  Defined.
               
  (* A few more lemmas *)
                                        
  Definition IncidenceStructureOfIncidenceStructures : IncidenceStructure.
    exists UU. exists UU. unfold IncidenceStructures. exact IncidenceStructures.
  Defined.
  Definition IncidenceStructureOfIncidence2Structures : IncidenceStructure.
    exists UU. exists UU. unfold IncidenceStructures. exact Incidence2Structures.
  Defined.
  Definition polyhedron_to_polygon : incidences Incidence2Structures -> incidences IncidenceStructures.
  unfold incidences.
  intros.
  induction X as [points [lines incidences]].
  exists points. exists lines.
  unfold IncidenceStructures.
  induction incidences.
  induction pr2.
  exact (icompose pr0 pr2).
  Defined.


  (* The main definition is to define a usable type of Polytopes (of arbitrary dimension).
     What is convenient intros  that the composition of IncidenceStructures with iteself
     faithfully models a 2-polytope.  The trouble is actually writing all the algorithms
     for working with polytopes. 
  *)


  (* This definition takes some getting used to but it works really well! *)
  Definition Polytopes (n : nat) : iRelation UU UU.
    induction n.
    - exact Paths.
    - induction n.
      + exact IncidenceStructures.
      + exact (icompose IncidenceStructures IHn0).
  Defined.

  (* This definition is even simpler, but there seem to be advantages to either approach *)
  Definition iPolytopes (n : nat) : iRelation UU UU.
    induction n as [_ | lower].
    - exact Paths.
    - exact (icompose IHlower IncidenceStructures).
  Defined.

  (* This one too; a polytope is an incidence in the incidence structure of polytopes *)
  Definition Polytope (n : nat) := incidences (Polytopes n).

  Definition iPolytope (n : nat) := incidences (iPolytopes n).

  Definition polytope {n} (poly: Polytope n) : Polytopes n (pr1 poly) (pr1 (pr2 poly)).
    exact (pr2 (pr2 poly)).
  Defined.

  Definition ipolytope {n} (poly: iPolytope n) : iPolytopes n (pr1 poly) (pr1 (pr2 poly)).
    exact (pr2 (pr2 poly)).
  Defined.

  Definition PolytopeOver (n : nat) (Points : UU) :=
    ∑ polytope : Polytope n, pr1 polytope = Points.
  Definition PolytopeUnder (n : nat) (Facets : UU) :=
    ∑ polytope : Polytope n, pr1 (pr2 polytope) = Facets.

  Definition iPolytopeOver (n : nat) (Points : UU) :=
    ∑ polytope : iPolytope n, pr1 polytope = Points.
  Definition iPolytopeUnder (n : nat) (Facets : UU) :=
    ∑ polytope : iPolytope n, pr1 (pr2 polytope) = Facets.

  Notation Poly n over Points := (PolytopeOver n Points).
  Notation Poly' n under Points := (PolytopeUnder n Points).


  Notation over Points n := (iPolytopeOver n Points) .
  Notation under Faces n := (iPolytopeUnder n Faces).

  Example phit2 : Polytope 2.
  exists unit
.
  exists unit.
  exists unit.
  unfold nat_rect.
  split;
  exact (λ _, λ _, unit).
  Defined.

  Example iphit2 : iPolytope 2.
  exists unit.
  exists unit.
  exists unit.
  unfold nat_rect.
  split.
  - unfold iPolytopes, icompose; simpl .
    exists unit. exact (idpath unit,, λ _, λ _, unit).
    - unfold iPolytopes.
      exact (λ _, λ _, unit).
  Defined.

  Example phit3 : Polytope 3.
  exists unit.
  exists unit.
  exists unit.
  split.
  exact (λ _, λ _, unit).
  simpl.
  exact (polytope phit2).
  Defined.


  Example iphit3 : iPolytope 3.
  exists unit.
  exists unit.
  exists unit.
  split.
  exact (ipolytope iphit2).
  exact (λ _, λ _, unit).
  Defined.

  Example Hit2 : Poly 2 over unit.
  exists phit2.
  exact (idpath _).
  Defined.

  Example iHit3 : Poly 3 over unit.
  exists phit3.
  exact (idpath _).
  Defined.

  Example iHit3' : Poly 3 under unit.
  exists phit3.
  exact (idpath _).
  Defined.

  Definition pCompose0 {n} {Lines} :
    Poly' n under Lines -> Poly 0 over Lines ->
      Poly' n under Lines.
    intros.
    unfold PolytopeUnder.
    induction X,X0.
    induction pr1 as [points [lines incidence]].
    induction pr0 as [lines' [lines'' equivalence]].
    simpl in pr2, pr3.
    unfold Polytope.
    unfold incidences.
    exists (points,, lines,, incidence).
    simpl.
    assumption.
  Defined.

  Definition ipCompose0 {n} {Lines} :
    under Lines n -> over Lines 0 ->
      under Lines n.
    intros.
    unfold iPolytopeUnder.
    induction X,X0.
    induction pr1 as [points [lines incidence]].
    induction pr0 as [lines' [lines'' equivalence]].
    simpl in pr2, pr3.
    unfold iPolytope.
    unfold incidences.
    exists (points,, lines,, incidence).
    simpl.
    assumption.
  Defined.

  
  Definition pCompose0' {n} {Lines} :
    Poly' 0 under Lines -> Poly n over Lines ->
      Poly n over Lines.
    intros.
    simpl.
    induction X,X0.
    induction pr1 as [lines [lines' equivalence]].
    induction pr0 as [lines'' [faces incidence]].
    simpl in pr2, pr3.
    rewrite pr2 in equivalence; rewrite pr3 in incidence.
    unfold Polytopes in equivalence; simpl in equivalence.
    rewrite <- equivalence in incidence.
    exists (lines,, faces,, incidence).
    exact equivalence.
  Defined.

  Definition pCompose11 {Lines} :
    Poly' 1 under Lines -> Poly 1 over Lines ->
    Polytope 2.
    unfold PolytopeUnder, PolytopeOver, Polytope, incidences, Polytopes.
    simpl.
    intros lower higher.
    induction lower as [lower lowpath].
    induction higher as [higher highpath].
    induction lower as [pp [ll lower]].
    induction higher as [ll' [ff higher]].
    simpl in highpath, lowpath.
    exists pp. exists ff.
    unfold icompose, IncidenceStructures.
    exists Lines.
    rewrite lowpath in lower; rewrite highpath in higher.
    exact (lower,,higher).
  Defined.

  Definition ipCompose11 {Lines} :
    under Lines 1 -> over Lines 1 ->
    iPolytope 2.
    unfold PolytopeUnder, PolytopeOver, Polytope, incidences, Polytopes.
    simpl.
    intros lower higher.
    induction lower as [lower lowpath].
    induction higher as [higher highpath].
    induction lower as [pp [ll lower]].
    induction higher as [ll' [ff higher]].
    simpl in highpath, lowpath.
    exists pp. exists ff.
    unfold icompose, IncidenceStructures.
    induction higher as [lines [path incidence]].
    simpl in path.
    unfold Paths in path.
    exists lines.
    split.
    - unfold iPolytopes.
      simpl.
      unfold icompose, Paths.
      induction lower as [ppp [path' lower]].
      simpl in path'.
      unfold Paths in path'.
      exists ppp.
      rewrite lowpath in lower.
      rewrite <- path. rewrite highpath.
      exact (path',, lower).
    - exact incidence.
  Defined.

  Definition Polytope1_to_istructure : Polytope 1 -> IncidenceStructure.
    unfold Polytope, IncidenceStructure.
    unfold incidences.
    unfold Polytopes. simpl.
    exact (λ x, x).
  Defined.

  Definition iPolytope1_to_istructure : iPolytope 1 -> IncidenceStructure.
    unfold iPolytope, IncidenceStructure.
    unfold incidences.
    unfold iPolytopes. simpl.
    intro.
    induction X as [points [lines [points' [path incidence]]]].
    exists points'. exists lines. exact incidence.
  Defined.

  Definition istructure_to_iPolytope : IncidenceStructure -> iPolytope 1.
    unfold iPolytope, IncidenceStructure.
    unfold incidences.
    unfold iPolytopes. simpl.
    intro.
    induction X as [points [lines incidence]].
    exists points. exists lines. unfold icompose.
    exists points. exact (idpath points,, incidence).
  Defined.

  Coercion Polytope1_to_istructure : Polytope >-> IncidenceStructure.
  Coercion iPolytope1_to_istructure : iPolytope >-> IncidenceStructure.

  Coercion istructure_to_iPolytope : IncidenceStructure >-> iPolytope.

  Definition idecomposeOver {n} {Points} (skyscraper: over Points (S n)) :
      over Points n × under (pr1 (pr2 (pr1 skyscraper))) 1.
    induction skyscraper as [polytope basepath].
    induction polytope as [points [facets polytope]].
    unfold incidences in polytope.
    unfold over.
    unfold iPolytope.
    unfold incidences.
    unfold iPolytopes in polytope.
    simpl in polytope.
    unfold icompose in polytope.
    induction polytope as [edges [long short]].
    split.
    exists (points,, edges,, long).
    exact basepath. 
    unfold under.
    simpl.
    unfold iPolytope, incidences.
    unfold iPolytopes.
    simpl.
    unfold icompose, Paths.
    exists (edges,, facets,, edges,, (idpath edges,, short)).
    exact (idpath facets).
  Defined.

  Definition icompose1n {n} {Points} (skyscraper: under Points n)
    (penthouse: over Points 1) : iPolytope (S n).
    unfold iPolytope.
    unfold incidences, iPolytopes.
    induction penthouse. induction pr1 as [topfloor [roof penthouse]].
    unfold iPolytopes in penthouse.
    simpl in penthouse.
    induction penthouse.
    induction pr0 as [basepath penthouse].
    simpl in pr2.
    rewrite <- basepath in penthouse.
    rewrite pr2 in penthouse.
    induction skyscraper.
    clear pr2.
    clear basepath. clear topfloor.
    induction pr0 as [groundfloor [topfloor skyscraper]].
    simpl in pr3. rewrite pr3 in skyscraper. clear pr1.
    exists groundfloor

.
    exists roof.
    simpl.
    
    unfold icompose.
    exists Points.
    unfold iPolytopes in skyscraper.
    exact (skyscraper,, penthouse).
  Defined.

  Definition iDecompose1 {n} {roof} (skyscraper : under roof (S n)) :
      ∑ topfloor : UU, under topfloor n × over topfloor 1.
    induction  skyscraper as [skyscraper _].
    clear roof.
    induction n.
    - 
      induction skyscraper.
      rename pr1 into points.
      induction pr2.
      rename pr1 into lines.
      exists points.
      split.
      unfold under.
      induction pr2 as [points' [path incidence]].
      unfold iPolytope, incidences.
      exists (points,, points',, path).
      simpl.
      unfold iPolytopes in path.
      simpl in path.
      unfold Paths in path.
      symmetry in path.
      exact path.
      unfold over.
      induction pr2.
      unfold iPolytope.
      induction pr2 as [path incidence].
      unfold incidences, iPolytopes.
      simpl.
      unfold icompose.
      exists (points,, lines,, pr1,, path,, incidence).
      exact (idpath _).
    - unfold under.
      induction skyscraper as [ground [roof skyscraper]].
      unfold iPolytopes in skyscraper.
      simpl in skyscraper.
      induction skyscraper as [pent rest].
      induction rest.
      exists pent.
      split.
      unfold iPolytope, incidences, iPolytopes.
      simpl.
      exists (ground,, pent,, pr1).
      exact (idpath pent).
      unfold over.
      unfold iPolytope, incidences.
      unfold iPolytopes.
      simpl.
      unfold icompose.
      refine ((pent,, roof,, pent,, _,, _),, idpath pent).  
      exact (idpath _).
      exact pr2.
  Defined.

  Definition underover1 {floor} : under floor 1 ->
                          ∑ flor, over flor 1.
    intros.
    induction X.
    induction pr1.
    induction pr0.
    simpl in pr2.
    exists pr1.
    exists (pr1,, pr0,, pr3).
    exact (idpath _).
  Defined.

  Definition overunder1 {floor} : over floor 1 ->
                          ∑ flor, under flor 1.
    intros.
    induction X.
    induction pr1.
    induction pr0.
    simpl in pr2.
    exists pr0.
    exists (pr1,, pr0,, pr3).
    exact (idpath _).
  Defined.
  
  Definition firstFloor {n} (skyscraper : iPolytope (S n)) :
    ∑ floor : UU, over floor 1.
    induction n.
    - induction skyscraper.
      exists pr1.
      unfold over. 
      unfold iPolytope, incidences.
      exists (pr1,, pr2).
      exact (idpath _).
    - apply IHn.
      induction skyscraper.
      induction pr2.
      induction pr2.
      induction pr3.
      exists pr1. exists pr2. exact pr3.
  Defined.


  Fixpoint invertPolytope_helper {n n0} {Points} (polytope : under Points n) (acc : over Points n0)
    : over Points (n + n0).
  induction n.
  exact acc.
  simpl.
  induction polytope.
  rename pr2 into path.
  induction pr1.
  induction pr2.
  induction pr2.
  induction pr3 as [long short].
  pose proof ((λ x, λ y, short y x) : IncidenceStructures pr0 pr2).
  simpl in path.
  assert (over Points (S n0)).
  + unfold over, iPolytope. unfold incidences.
    simpl.
    unfold icompose.
    simpl.  assert (∑ pp ll edges : UU, iPolytopes n0 pp edges × IncidenceStructures edges ll).
    rewrite path in short, X.
  - 
    induction acc.                     
    induction pr3.
    induction pr5.
    exists Points. exists pr2. exists pr5.
    simpl in pr4.
    exact (pr6,, 
    induction pr3.
    induction pr5.
    simpl in pr4.
    rewrite pr4 in pr6.
    rewrite path.

  Definition invertPolytope {n} (polytope : iPolytope n) : iPolytope n.
    unfold iPolytope, incidences. unfold iPolytope, incidences in polytope.
    induction polytope as [pp [ll polytope]].
    exists ll. exists pp.
    induction n.


  Definition nthFloor {dim} {n : stn dim} (skyscraper : iPolytope dim) :
    ∑ floor : UU, over floor (dim - (pr1 n)).
    induction dim.
    - inversion n.
      inversion pr2.
    - remember n.
      induction n as [n nlth].
      induction n.
      + induction skyscraper.
        induction pr2.
        rename pr0 into faces.
        rename pr2 into edges.
        rename pr1 into points.
        exists points.
        simpl.
        rewrite Heqs.
        exists (points,, faces,, edges).
        exact (idpath points).
      + simpl in IHn.
        pose proof (IHdim s).
        induction pr3.
        simpl in IHdim.
        simpl.
        exists  (edges,, faces,, edges,, idpath _,, pr2).
        simpl.
        exact (idpath _).
      + induction skyscraper.
        induction pr2. induction pr2.
        induction pr3.
        induction pr3.

        
    - induction skyscraper.
      exists pr1.
      unfold over. 
      unfold iPolytope, incidences.
      exists (pr1,, pr2).
      exact (idpath _).
    - apply IHn.
      induction skyscraper.
      induction pr2.
      induction pr2.
      induction pr3.
      exists pr1. exists pr2. exact pr3.
  Defined.

  Definition NonFirstFloor {n} (skyscraper : iPolytope (S n)) :
    ∑ floor : UU, over floor n.
    induction n.
    - induction skyscraper.
      induction pr2.
      exists pr0.
      unfold over.
      unfold iPolytope.
      exists (pr0,, pr0,, idpath pr0). exact (idpath pr0).
    - exists (pr1 (firstFloor skyscraper)).
      unfold firstFloor.
      simpl.
      unfold over.
      simpl.
      induction n.
      + simpl.
        induction skyscraper as [points [faces skyscraper]].
        induction skyscraper.
        exists (points,, pr1,, (Preamble.pr1 pr2)).
        exact (idpath points).
      + simpl.
        induction skyscraper as [points [faces skyscraper]].
        induction skyscraper.
        simpl.
        unfold iPolytopes.
        unfold Preamble.pr1.
        exists (pr1,, faces,, Preamble.pr2 pr2).
        simpl.
        induction skyscra
 
      

  Fixpoint iDecompose {n} {roof} (skyscraper : under roof (S n)) :
    ∏ n0 : stn n,
      ∑ floor : UU, over floor 1.
    intros.
    induction n0 as [n0 condition].
    pose proof (iDecompose1 skyscraper) as decomposition.
    induction n0.
    induction decomposition as [floor [long short]].
    exists floor. exact short.
    - induction n.
        

 
  Definition decomposeOver {n} {Points} :
    over Points (S n) -> over Points n × IncidenceStructure.
    intro entire.
    induction entire as [[points structure] path].
    induction structure as [lines structure].
    simpl in path.
    unfold PolytopeUnder.
    unfold Polytope, incidences.
    induction n.
    - (* we can obtain an (identity) path from an incidence structure *)
      + split.
        unfold over.
        unfold iPolytope, incidences.
        exists (points,, Points,, path).
        exact path.
        exists points. exists lines.
        induction structure.
        induction pr2 as [pathh incidence].
        rewrite <- pathh in incidence.
        exact incidence.
    - (* we can obtain an n-polytope from an (n+1)-polytope *)
      induction structure.
      induction pr2.
      split.
      clear IHn.
      + unfold over, Polytopes, PolytopeUnder,Polytope, IncidenceStructures.
        simpl.
        unfold iPolytope.
        unfold incidences.
        exists (points,, pr1,, pr0).
        exact path.
      + exists pr1. exists lines. exact pr2.
   Defined.
        
       
