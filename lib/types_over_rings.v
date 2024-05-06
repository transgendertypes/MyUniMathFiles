Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.All.
Require Import UniMath.NumberSystems.All.


(* To each point of a monoid (say a ring) we assign a type.*)
Definition typeon (𝔾 : UU) := 𝔾 -> UU.
  
Check ℤ.

Example Fin : typeon hz.
unfold typeon.
intro x.
remember (hzabsval x) as absval. 
exact (stn absval).
Defined.

Example booland : binop boolset.
  unfold binop. 
  unfold boolset.
  simpl.
  exact andb.
Defined.

Lemma isassoc_booland : isassoc booland.
  unfold booland, isassoc.
  simpl.
  intros.
  induction x,x',x''; apply idpath.
Defined.

Lemma isunital_booland : isunital booland.
  exists true.
  unfold isunit,islunit,isrunit,booland;
  split; intros; induction x;
  apply idpath.
Defined.

Lemma iscomm_booland : iscomm booland.
  unfold booland, iscomm.
  simpl.
  intros.
  induction x,x'; apply idpath.
Defined.
Example boolor : binop boolset.
  unfold binop. 
  unfold boolset.
  simpl.
  exact orb.
Defined.

Lemma isassoc_boolor : isassoc boolor.
  unfold boolor, isassoc.
  simpl.
  intros.
  induction x,x',x''; apply idpath.
Defined.

Lemma isunital_boolor : isunital boolor.
  exists false.
 
 unfold isunit,islunit,isrunit,boolor;
  split; intros; induction x;
  apply idpath.




Defined.

Lemma iscomm_boolor : iscomm boolor.
  unfold boolor, iscomm.
  simpl.
  intros.
  induction x,x'; apply idpath.
Defined.

Definition xorb : bool -> bool -> bool.
  intros.
  induction X;
  induction X0.
  - exact true.
  - exact false.
  - exact false.
  - exact true.
Defined.

Example boolxor : binop boolset.
  unfold binop. 
  unfold boolset.
  simpl.
  exact xorb.



Defined.

Lemma isassoc_boolxor : isassoc boolxor.
  unfold boolxor, isassoc.
  simpl.
  intros.
  induction x,x',x''; apply idpath.
Defined.

Lemma isunital_boolxor : isunital boolxor.
  exists true.
  unfold isunit,islunit,isrunit,boolxor;
  split; intros; induction x;
  apply idpath.
Defined.

Lemma iscomm_boolxor : iscomm boolxor.
  unfold boolxor, iscomm.
  simpl.
  intros.
  induction x,x'; apply idpath.
Defined.

Example boolandmonoid : monoid.
  exists (boolset,, booland).
  exact (isassoc_booland,, isunital_booland).
Defined.
Example boolormonoid : monoid.
  exists (boolset,, boolor).
  exact (isassoc_boolor,, isunital_boolor).
Defined.

Example boolxorgr : gr.
exists (boolset,, boolxor).
unfold isgrop.
unfold ismonoidop.
exists (isassoc_boolxor,, isunital_boolxor).
unfold invstruct.
simpl.
exists (λ x, x).
unfold isinv, booland, negb, unel_is.
unfold islinv, isrinv, andb. simpl.
split;
  intros; induction x; simpl;
  apply idpath.
Defined.

Example BoolXor : typeon boolxorgr.
unfold typeon. intros.
induction X.
- exact unit.
- exact ∅.
Defined.

Example BoolAnd : typeon boolandmonoid.
unfold typeon; intros.
induction X.
- exact unit.
- exact ∅.
Defined.

Example BoolOr : typeon boolormonoid.
unfold typeon; intros.
induction X.
- exact unit.
- exact ∅.
Defined.


(* sometimes its easier to define the opmaps in terms
of the zeromaps and invmaps. The opmaps are the primary construct *)
(* x * 0 -> x *)
Definition zeromaps {𝔾 : monoid} (on : typeon 𝔾) : UU :=
  ∏ x : 𝔾, on x × (on (unel 𝔾)) -> on x.
(* x + 0 -> x *)
Definition zeromaps_co {𝔾 : monoid} (on : typeon 𝔾) : UU :=
  ∏ x : 𝔾, on x ⨿ (on (unel 𝔾)) -> on x.

(* x / x -> 1 *)
Definition invmaps {𝔾: gr} (on : typeon 𝔾) : UU :=
  ∏ x : 𝔾, (on x) × (on (grinv 𝔾 x)) -> on (unel 𝔾).
(* x - x -> 0 *)
Definition invmaps_co {𝔾: gr} (on : typeon 𝔾) : UU :=
  ∏ x : 𝔾, (on x) ⨿ (on (grinv 𝔾 x)) -> on (unel 𝔾).

(* x + y = z *)
Definition opmaps {𝔾: monoid} (on : typeon 𝔾) : UU :=
  ∏ x y : 𝔾, (on x) × (on y) -> on (op x y).
Definition opmaps_co {𝔾: monoid} (on : typeon 𝔾) : UU :=
  ∏ x y : 𝔾, (on x) ⨿ (on y) -> on (op x y).
  
Example xormaps : opmaps BoolXor.
unfold opmaps, BoolXor.
intros.
induction x,y; simpl.
- exact tt.
- inversion X.
  exact pr2.
- inversion X.
  exact pr1.
- exact tt.
Defined.

Definition andmaps : opmaps BoolAnd.
  unfold opmaps, BoolAnd.
  simpl; intros.
  induction x,y; simpl; simpl in X.
  - exact tt.
  - exact (pr2 X).
  - exact (pr1 X).
  - exact (pr1 X).
Defined.

(* notice that the proofs of ormaps and ormaps_co are identical, even though
the statements are far from identical *)
Definition ormaps : opmaps BoolOr.
  unfold opmaps, BoolOr. simpl. intros.
  induction x,y; simpl in X; simpl; try exact tt.
  induction X; assumption.
Defined.

Definition ormaps_co : opmaps_co BoolOr.
  unfold opmaps_co, BoolOr. simpl. intros.
  induction x,y; simpl in X; simpl; try exact tt.
  induction X; assumption.
Defined.

Definition isabmonoidop_boolor : isabmonoidop boolor.
  exact ( (isassoc_boolor,, isunital_boolor),, iscomm_boolor).
Defined.

Definition abmonoid_boolor : abmonoid.
  exists (boolset,, boolor).
  exact isabmonoidop_boolor.
Defined.

Definition isabmonoidop_boolxor : isabmonoidop boolxor.
  exact ( (isassoc_boolxor,, isunital_boolxor),, iscomm_boolxor).
Defined.
  
Definition abmonoid_boolxor : abmonoid.
  exists (boolset,, boolxor).
  exact isabmonoidop_boolxor.
Defined.

Definition ismonoidop_booland : ismonoidop booland.
  exact (isassoc_booland,, isunital_booland).
Defined.
Definition isabmonoidop_booland : isabmonoidop booland.
  exact ( ismonoidop_booland,, iscomm_booland).
Defined.

Definition abmonoid_booland : abmonoid.
  exists (boolset,, booland).
  exact isabmonoidop_booland.
Defined.

Definition boolrig : rig.
  unfold rig.
  exists (boolset,, boolor,, booland).
  unfold isrigops.
  split.
- unfold op1,op2.
  simpl.
  exists (isabmonoidop_boolor ,, ismonoidop_booland).
  split;
  intros;
  induction x; unfold unel_is ; apply idpath.
- unfold isdistr.
  unfold op1,op2, isrdistr, isldistr.
  simpl.
  split;
  intros;
  induction x,x',x'';
  apply idpath.
Defined.

Definition typedrig : UU :=
  ∑ rr : rig,
      ∑ on : typeon rr,
        ∏ x y : rr,
          ((on x ⨿ on y) -> on (op1 x y))
            × ((on x × on y) -> on (op2 x y)).

Definition cotypedrig : UU :=
  ∑ rr : rig,
      ∑ on : typeon rr,
        ∏ x y : rr,
          ((on x ⨿ on y) <- on (op1 x y))
            × ((on x × on y) <- on (op2 x y)).

Definition beautifulrig : UU :=
  ∑ rr : rig,
      ∑ on : typeon rr,
        ∏ x y : rr,
          ((on x ⨿ on y) -> on (op1 x y))
        × ((on x × on y) <- on (op2 x y)).
Definition beautifulrig_torig : beautifulrig -> rig.
  exact pr1. Defined.
Coercion beautifulrig_torig : beautifulrig >-> rig.

Definition beautifulring : UU :=
  ∑ rr : ring,
      ∑ on : typeon rr,
        ∏ x y : rr,
          ((on x ⨿ on y) -> on (op1 x y))
        × ((on x × on y) <- on (op2 x y)).

Definition beautifulring_to_beautifulrig :
  beautifulring -> beautifulrig.
  intros.
  exists (pr1 X). exact (pr2 X).
Defined.
Coercion beautifulring_to_beautifulrig : beautifulring >-> beautifulrig.

Definition beautifulcommring : UU :=
  ∑ rr : commring,
      ∑ on : typeon rr,
        ∏ x y : rr,
          ((on x ⨿ on y) -> on (op1 x y))
        × ((on x × on y) <- on (op2 x y)).

Definition beautifulcommring_to_beautifulring :
  beautifulcommring -> beautifulring.
  intros.
  exists (pr1 X). exact (pr2 X).
Defined.
Coercion beautifulcommring_to_beautifulring : beautifulcommring >-> beautifulring.

Definition uglyrig : UU :=
  ∑ rr : rig,
      ∑ on : typeon rr,
        ∏ x y : rr,
          ((on x ⨿ on y) -> on (op1 x y))
        × ((on x × on y) <- on (op2 x y)).
  
(* Our path type "ring" is  a nice example of charm ring
  (a = b) × (c = d) -> (a + c = b + d)
  (a = b) ⨿ (c = d) -> (ac + bd = ad + bc)
(a-b)+(c-d) = a+c-b-d
(a-b)(c-d)=ac-ad-bc+bd
 *)

Definition charmrig : UU :=
  ∑ rr : rig,
      ∑ on : typeon rr,
        ∏ x y : rr,
          ((on x ⨿ on y) -> on (op2 x y))
        × ((on x × on y) -> on (op1 x y)).
  

Definition typedring : UU :=
  ∑ rr : ring,
      ∑ on : typeon rr,
        ∏ x y : rr,
          ((on x ⨿ on y) -> on (op1 x y))
            × ((on x × on y) -> on (op2 x y)).
Definition typedring_to_typedrig : typedring -> typedrig.
  intros;induction X.
  exists pr1;exact pr2.
Defined.
Coercion typedring_to_typedrig : typedring >-> typedrig.

Definition typedring_co : UU :=
  ∑ rr : ring,
      ∑ on : typeon rr,
        ∏ x y : rr,
          ((on x ⨿ on y) <- on (op1 x y))
            × ((on x × on y) <- on (op2 x y)).

Definition typedring_co_to_typedrig_co : typedring -> typedrig.
  intros;induction X.
  exists pr1;exact pr2.
Defined.
Coercion typedring_co_to_typedrig_co : typedring >-> typedrig.

Definition commtypedring : UU :=
  ∑ rr : commring,
      ∑ on : typeon rr,
        ∏ x y : rr,
          ((on x ⨿ on y) -> on (op1 x y))
            × ((on x × on y) -> on (op2 x y)).
Definition commtypedring_to_typedring : commtypedring -> typedring.
  intros;induction X.
  exists pr1;exact pr2.
Defined.
Coercion commtypedring_to_typedring
  : commtypedring >-> typedring.

Definition commtypedring_co : UU :=
  ∑ rr : commring,
      ∑ on : typeon rr,
        ∏ x y : rr,
          ((on x ⨿ on y) <- on (op1 x y))
            × ((on x × on y) <- on (op2 x y)).

Definition commtypedring_co_to_typedring_co : commtypedring_co -> typedring_co.
  intros;induction X.
  exists pr1;exact pr2.
Defined.
Coercion commtypedring_co_to_typedring_co
  : commtypedring_co >-> typedring_co.

Definition weqtypedrig : UU :=
  ∑ rr : rig,
      ∑ on : typeon rr,
        ∏ x y : rr,
          (weq (on x ⨿ on y)  (on (op1 x y)))
            × (weq (on x × on y)  (on (op2 x y))).

Definition pathtypedrig : UU :=
  ∑ rr : rig,
      ∑ on : typeon rr,
        ∏ x y : rr,
          ( (on x ⨿ on y) = (on (op1 x y)))
        × ((on x × on y) = (on (op2 x y))).

Definition therig (rr : typedrig) : rig.
  induction rr.
  exact pr1.
Defined.
Coercion therig : typedrig >-> rig.

Definition on (rr : typedrig) : rr -> UU.
  induction rr.
  induction pr2.
  exact pr0.
Defined.

Coercion on : typedrig >-> Funclass.

Definition thetype {r : typedrig} (rr : r) : UU.
  exact (r rr).
Defined.

Definition function_on_the_sum {r : typedrig} (x y : r)
  : (thetype x) ⨿ (thetype y) -> thetype (op1 x y).
  induction r. induction pr2.
  exact (Preamble.pr1 (pr2 x y)).
Defined.
Notation "x ⨥ y" := (function_on_the_sum x y) (at level 300).

Definition function_on_the_product {r : typedrig} (x y : r)
  : (thetype x) × (thetype y) -> thetype (op2 x y).
  induction r. induction pr2.
  exact (Preamble.pr2 (pr2 x y)).
Defined.
Notation "x ⨱ y" := (function_on_the_product x y) (at level 300).

Definition functiontypes_from (ℵ : UU) : UU -> UU.
  intros.
  exact (ℵ -> X).
Defined.
Definition functiontypes_to (ℶ : UU) : UU -> UU.
  intros.
  exact (X -> ℶ).
Defined.
Definition rigof_functiontypes_from (ℵ : UU) : typedrig -> typedrig.
  unfold typedrig.
  intros.
  induction X as [therig therest].
  induction therest as [on therest].
  exists therig.
  exists (functiontypes_from ℵ ∘ on).
  intros. unfold functiontypes_from.
  simpl.
  remember (therest x y).
  induction d as [adding multiplying].
  clear Heqd. clear therest.
  split.
  - clear multiplying.
    intro either. intro aleph.
    induction either.
    + exact (adding (inl (a aleph))).
    + exact (adding (inr (b aleph))).
  - clear adding.
    intro both. intro aleph.
    induction both as [north south].
    remember (north aleph) as northpole.
    remember (south aleph) as southpole.
    exact (multiplying (northpole,, southpole)).
Defined.

Definition rigof_pathtypes : typedrig -> typedrig.
  unfold typedrig.
  intros.
  induction X as [therig therest].
  induction therest as [on therest].
  exists therig.
  exists ((λ x, x = x) ∘ on).
  simpl.
  intros.
  split.
  intros.
  apply idpath.
  intros.
  apply idpath.
Defined.

Definition corigof_pathtypes : typedrig -> cotypedrig.
  unfold typedrig, cotypedrig.
  intros.
  induction X as [therig therest].
  induction therest as [on therest].
  exists therig.
  exists ((λ x, x = x) ∘ on).
  simpl.
  intros.
  split; intros.
  left; apply idpath.
  split; apply idpath.
Defined.

Definition zero {R  : rig} : R .
  induction R.
  induction pr1.
  induction pr0.
  induction pr2.
  induction pr2.
  induction pr5.
  simpl.
  refine (unel ((pr1,, _),,  _)).
  exact (Preamble.pr2 pr2).
Defined.

Definition one {R  : rig} : R .
  induction R.
  induction pr1.
  induction pr0.
  induction pr2.
  induction pr2.
  induction pr5.
  simpl.
  refine (unel ((pr1,, _),, _)).
  exact (Preamble.pr1 pr2).
Defined.

Definition zerotype ( R : typedrig ) : UU :=
  thetype (zero : R).
Definition onetype ( R : typedrig ) : UU :=
  thetype (one : R ).

Definition iszeroempty ( R : typedrig ) : UU :=
  zerotype R = ∅.
Definition iszerounit ( R : typedrig ) : UU :=
  zerotype R = unit.
Definition isoneempty ( R : typedrig ) : UU :=
  onetype R = ∅.
Definition isoneunit ( R : typedrig ) : UU :=
  onetype R = unit.

(* cation and anion are just arbitrary notation *)
Definition iscation ( R : typedrig ) : UU :=
  iszeroempty R × isoneunit R .
Definition isanion ( R : typedrig ) : UU :=
  iszerounit R × isoneempty R .
Definition isneutral ( R : typedrig ) : UU :=
  zerotype R = onetype R. 

(* *)
Definition istypedrigconstant ( R : typedrig ) : UU :=
  ∑ ℵ : UU,
      ∏ rr : R,
        thetype rr = ℵ.
  
Lemma isaconstant_neutral {𝕣} : istypedrigconstant 𝕣 -> isneutral 𝕣.
  unfold istypedrigconstant,isneutral.
  intros.
  induction X.
  pose proof (pr2 zero).
  unfold zerotype,onetype.
  rewrite X.
  symmetry. exact (pr2 one).
Defined.

Notation Ω := thetype.

Definition theimage_oversum {𝕣 : typedrig}
  (x y : 𝕣)
  (xy : Ω x ⨿ Ω y)
  := (x ⨥ y) xy.

Definition theimage_overprod {𝕣 : typedrig}
  (x y : 𝕣)
  (xy : Ω x × Ω y)
  := (x ⨱ y) xy.

Definition mixed_sum_r {𝕣 : typedrig}
  {x : 𝕣}
  (xx : Ω x)
  (y : 𝕣): Ω (x + y)%ring
  := (x ⨥ y) (inl xx : Ω x ⨿ Ω y).
Definition mixed_sum_l {𝕣 : typedrig}
  {y : 𝕣}
  (x : 𝕣)
  (yy : Ω y) : Ω (x + y)%ring
  := (x ⨥ y) (inr yy : Ω x ⨿ Ω y).

Definition internal_mult {𝕣 : typedrig}
  {x y : 𝕣}
  (xx : Ω x)
  (yy : Ω y): Ω (x * y)%ring
  := (x ⨱ y) (xx,,yy).

Notation "xx ⧝ yy" := (internal_mult xx yy) (at level 250).
Notation "xx ⟴ y" := (mixed_sum_r xx y) (at level 250). 
Notation "x ⬲ yy" := (mixed_sum_l x yy) (at level 250). 

Definition internal_mult3_l {𝕣: typedrig}  
  {x y z : 𝕣}
  (xx : Ω x)
  (yy : Ω y)
  (zz : Ω z): Ω (x * (y * z): 𝕣)%ring
  := (xx ⧝ (yy ⧝ zz)).

Definition internal_mult3_r {𝕣: typedrig}  
  {x y z : 𝕣}
  (xx : Ω x)
  (yy : Ω y)
  (zz : Ω z): Ω (x * y * z : 𝕣)%ring
  := ((xx ⧝ yy) ⧝ zz).

Lemma types_assoc_prod (𝕣 : typedrig) :
  ∏ x y z : 𝕣,
      Ω (x * y * z)%ring = Ω (x * (y * z))%ring .
  intros.
  induction 𝕣.
  induction pr1.
  induction pr2.
  simpl in x,y,z.
  simpl in pr2.
  unfold isrigops in pr0.
  induction pr0.
  induction pr0.
  induction pr0.
  induction pr6.
  pose proof (pr6 x y z).
  unfold op2.
  unfold op2 in X.
  simpl. simpl in X.
  rewrite X.
  apply idpath.
Defined.

Lemma types_assoc_sum (𝕣 : typedrig) :
  ∏ x y z : 𝕣,
      Ω (x + y + z)%ring = Ω (x + (y + z))%ring .
  intros.
  induction 𝕣.
  induction pr1.
  induction pr2.
  simpl in x,y,z.
  simpl in pr2.
  unfold isrigops in pr0.
  induction pr0.
  induction pr0.
  induction pr0.
  induction pr0.
  induction pr0.
  pose proof (pr0 x y z).
  simpl. simpl in X.
  rewrite X.
  apply idpath.
Defined.

Definition assoc_prod_on_types {𝕣 : typedrig} {x y z : 𝕣}
      : Ω (x * y * z : 𝕣)%ring -> Ω (x * (y * z) : 𝕣)%ring .
  intros. rewrite types_assoc_prod in X.
  exact X.
Defined.
Definition assoc_prod_on_types' {𝕣 : typedrig} {x y z : 𝕣}
      : Ω (x * y * z : 𝕣)%ring <- Ω (x * (y * z) : 𝕣)%ring .
  intros. rewrite <- types_assoc_prod in X.
  exact X.
Defined.

Definition assoc_sum_on_types {𝕣 : typedrig} {x y z : 𝕣}
      : Ω (x + y + z : 𝕣)%ring -> Ω (x + (y + z) : 𝕣)%ring .
  intros. rewrite types_assoc_sum in X.
  exact X.
Defined.

Definition assoc_sum_on_types' {𝕣 : typedrig} {x y z : 𝕣}
      : Ω (x + y + z : 𝕣)%ring <- Ω (x + (y + z) : 𝕣)%ring .
  intros. rewrite <- types_assoc_sum in X.
  exact X.
Defined.

Definition isinternal_assoc_prod (𝕣 : typedrig) : UU :=
  ∏ x y z : 𝕣,
      ∏ xx : Ω x, ∏ yy : Ω y, ∏ zz : Ω z,
       internal_mult3_l xx yy zz =
       assoc_prod_on_types ( 
        internal_mult3_r xx yy zz).

Definition isinternal_assoc_sum_rr (𝕣 : typedrig) : UU :=
  ∏ x y z : 𝕣,
      ∏ xx : Ω x,
       assoc_sum_on_types ( 
       (xx ⟴ y) ⟴ z) =
       (xx ⟴ (y + z)%ring).

Definition isinternal_assoc_sum_lr (𝕣 : typedrig) : UU :=
  ∏ x y z : 𝕣,
      ∏ yy : Ω y,
       assoc_sum_on_types ( 
       (x ⬲ yy) ⟴ z) =
       (x ⬲ (yy ⟴ z)).
Definition isinternal_assoc_sum_ll (𝕣 : typedrig) : UU :=
  ∏ x y z : 𝕣,
      ∏ zz : Ω y,
       assoc_sum_on_types ( 
       (x + y)%ring ⬲ zz) =
       (x ⬲ (y ⬲ zz)).
Definition isinternal_assoc_sum (𝕣 : typedrig) : UU :=
  isinternal_assoc_sum_ll 𝕣
× isinternal_assoc_sum_lr 𝕣
× isinternal_assoc_sum_rr 𝕣.

Definition isfullyassoc (𝕣 : typedrig) : UU :=
  isinternal_assoc_sum 𝕣
× isinternal_assoc_prod 𝕣.

Lemma types_commute_sum {𝕣 : typedrig} :
  ∏ x y : 𝕣,
      Ω (x + y)%ring = Ω (y + x)%ring .
  intros.
  induction 𝕣.
  induction pr1.
  induction pr2.
  simpl in x,y.
  simpl in pr2.
  unfold isrigops in pr0.
  induction pr0.
  induction pr0.
  induction pr0.
  induction pr0.
  pose proof (pr7 x y).
  unfold op1.
  unfold op1 in X.
  simpl. simpl in X.
  rewrite X.
  apply idpath.
Defined.

Lemma types_commute_prod {𝕣 : commtypedring} :
  ∏ x y : 𝕣,
      Ω (x * y)%ring = Ω (y * x)%ring .
  intros.
  induction 𝕣.
  induction pr1.
  induction pr2.
  simpl in x,y.
  simpl in pr2.
  unfold isrigops in pr0.
  induction pr0.
  induction pr0.
  pose proof (pr4 x y).
  unfold op1.
  unfold op1 in X.
  simpl. simpl in X.
  rewrite X.
  apply idpath.
Defined.

Definition comm_sum_on_types {𝕣 : typedrig} {x y : 𝕣}
      : Ω (x + y : 𝕣)%ring -> Ω (y + x : 𝕣)%ring .
  intros. rewrite (types_commute_sum x y) in X.
  exact X.
Defined.

Definition comm_prod_on_types {𝕣 : commtypedring} {x y : 𝕣}
      : Ω (x * y : 𝕣)%ring -> Ω (y * x : 𝕣)%ring .
  intros. rewrite (types_commute_prod x y) in X.
  exact X.
Defined.

Definition isinternal_comm_sum (𝕣 : typedrig) : UU :=
  ∏ x y : 𝕣,
      ∏ xx : Ω x,
       (y ⬲ xx) =
       comm_sum_on_types( 
        xx ⟴ y).

Definition isinternal_comm_prod ( 𝕣 : commtypedring ) : UU :=
  ∏ x y : 𝕣,
      ∏ xx : Ω x, ∏ yy : Ω y,
       (xx ⧝ yy) =
       comm_prod_on_types( 
        yy ⧝ xx).

Lemma types_distr_l {𝕣 : typedrig} :
  ∏ x y z : 𝕣,
      Ω (x * (y + z))%ring = Ω (x * y + x * z)%ring .
intros.
induction 𝕣 as [rig [on rest]].
induction rig.
induction pr1 as [set [plus times]].
simpl in on.
induction pr2.
rename pr2 into distr.
unfold isdistr in distr.
induction distr as [ldistr rdistr].
remember (ldistr y z x).
unfold op1, op2.
unfold op1, op2 in p.
simpl. simpl in p.
rewrite p;apply idpath.
Defined.

Lemma types_distr_r {𝕣 : typedrig} :
  ∏ x y z : 𝕣,
      Ω ((y + z) * x)%ring = Ω (y * x + z * x)%ring .
intros.
induction 𝕣 as [rig [on rest]].
induction rig.
induction pr1 as [set [plus times]].
simpl in on.
induction pr2.
rename pr2 into distr.
unfold isdistr in distr.
induction distr as [ldistr rdistr].
remember (rdistr y z x).
unfold op1, op2.
unfold op1, op2 in p.
simpl; simpl in p.
rewrite p;apply idpath.
Defined.

Definition distr_l_on_types {𝕣 : typedrig} {x y z : 𝕣}
      : Ω ((x * y) + (x * z) : 𝕣)%ring <- Ω (x * (y + z) : 𝕣)%ring .
  intros. rewrite (types_distr_l x y) in X.
  exact X.
Defined.
Definition distr_r_on_types {𝕣 : typedrig} {x y z : 𝕣}
      : Ω ((y * x) + (z * x) : 𝕣)%ring <- Ω ((y + z) * x : 𝕣)%ring .
  intros. rewrite (types_distr_r x y) in X.
  exact X.
Defined.

Definition isinternal_distr_l_l (𝕣 : typedrig) : UU :=
  ∏ x y z : 𝕣,
      ∏ xx : Ω x, ∏ yy : Ω y,
       distr_l_on_types 
       (xx ⧝ (z ⬲ yy)) =
        ((x * z)%ring ⬲ (xx ⧝ yy)) .

Definition isinternal_distr_l_r (𝕣 : typedrig) : UU :=
  ∏ x y z : 𝕣,
      ∏ xx : Ω x, ∏ yy : Ω y,
       distr_l_on_types 
       (xx ⧝ (yy ⟴ z)) =
        ((xx ⧝ yy) ⟴ (x * z)%ring) .

Definition isinternal_distr_r_r (𝕣 : typedrig) : UU :=
  ∏ x y z : 𝕣,
      ∏ xx : Ω x, ∏ yy : Ω y,
       distr_r_on_types 
       ((yy ⟴ z) ⧝ xx) =
        ((yy ⧝ xx) ⟴ (z * x)%ring) .

Definition isinternal_distr_r_l (𝕣 : typedrig) : UU :=
  ∏ x y z : 𝕣,
      ∏ xx : Ω x, ∏ yy : Ω y,
       distr_r_on_types 
       ((z ⬲ yy) ⧝ xx) =
         ( (z * x)%ring  ⬲ (yy ⧝ xx)) .

Definition isinternal_distr_r (𝕣 : typedrig) : UU :=
  isinternal_distr_r_r 𝕣 
                       × 
  isinternal_distr_r_l 𝕣. 


Definition isinternal_distr_l (𝕣 : typedrig) : UU :=
  isinternal_distr_l_r 𝕣 
                       × 
  isinternal_distr_l_l 𝕣. 

Definition isinternal_distr (𝕣 : typedrig) : UU :=
  isinternal_distr_l 𝕣 × isinternal_distr_r 𝕣.

Definition spacedrig : UU :=
  ∑ ϡ : typedrig,
      isfullyassoc ϡ 
    × isinternal_comm_sum ϡ
    × isinternal_distr ϡ.

Definition spacedring : UU :=
  ∑ ϡ : typedring,
      isfullyassoc ϡ 
    × isinternal_distr ϡ
    × isinternal_comm_sum ϡ.

Definition spacedcommring : UU :=
  ∑ ϡ : commtypedring,
      isfullyassoc ϡ 
    × isinternal_distr ϡ
    × isinternal_comm_sum ϡ
    × isinternal_comm_prod ϡ.

(* I think this is the "true" definition, with the arrows on the sum opposite the arrows on the product 
Definition beautyrig : UU :=
  ∑ ϡ : beautifulrig,
      isfullyassoc ϡ 
    × isinternal_comm_sum ϡ
    × isinternal_distr ϡ.
*)

Example unittypedrig (ℜ : rig) : typedrig.
  intros.
  exists ℜ.
  exists (λ _, unit).
  intros.
  split; exact (λ _, tt).
Defined.

Example constanttypedrig_left (ℜ : rig) (Points : UU) : typedrig.
  intros.
  exists ℜ.
  exists (λ _, Points).
  intros.
  split.
  + intro either; induction either.
    - exact a.
    - exact b.
  + exact pr1.
Defined.
Example constanttypedrig_right (ℜ : rig) (Points : UU) : typedrig.
  intros.
  exists ℜ.
  exists (λ _, Points).
  intros.
  split.
  + intro either; induction either.
    - exact a.
    - exact b.
  + exact pr2.
Defined.

Example unitspacedrig (ℜ : rig) : spacedrig.
exists (unittypedrig ℜ).
    induction ℜ as[theset [rest distr]].
    induction rest as[axs rest].
    induction axs as[sum product].
    induction sum as[summonoid sumcommutes].
    induction summonoid as[assocsum unitalsum].
    induction product as[assocprod unitalprod].
    simpl in rest.
split. unfold isfullyassoc.
- unfold isinternal_assoc_sum, isinternal_assoc_prod, unittypedrig.
  split.
  -- split.
  + unfold isinternal_assoc_sum_ll.
    intros.
    simpl in x,y,z.
    unfold thetype in zz.
    simpl in zz.
    unfold mixed_sum_l.
    unfold function_on_the_sum.
    simpl.
    unfold assoc_sum_on_types.
    unfold types_assoc_sum.
    unfold internal_paths_rew.
    unfold internal_paths_rew_r.
    simpl.
    unfold thetype.
    simpl.
    unfold isassoc in assocsum.
    simpl.
    induction (assocsum x y y).
    apply idpath.
  + simpl. split.
    ++ 
       unfold isinternal_assoc_sum_lr.
       intros.
       unfold thetype in yy.
       simpl in x,y,z,yy.
       unfold assoc_sum_on_types.
       unfold thetype.
       unfold internal_paths_rew.
       unfold types_assoc_sum.
       unfold internal_paths_rew_r.
       induction (assocsum x y z).
       apply idpath.
    ++  unfold isinternal_assoc_sum_rr.
        intros.
        unfold thetype in xx.
       simpl in x,y,z,xx.
       unfold assoc_sum_on_types.
       unfold thetype.
       unfold internal_paths_rew.
       unfold types_assoc_sum.
       unfold internal_paths_rew_r.
       induction (assocsum x y z).
       unfold mixed_sum_r.
       unfold function_on_the_sum.
       simpl.
       exact (idpath tt).
    -- intros.
       unfold internal_mult3_l.
       unfold internal_mult3_r.
       unfold assoc_prod_on_types.
       simpl.
       unfold internal_paths_rew.
       unfold types_assoc_prod.
       simpl. unfold internal_paths_rew_r.
       induction (assocprod x y z).
       unfold internal_mult.
       unfold function_on_the_product.
       simpl.
       exact (idpath tt).
- split.
  + unfold isinternal_comm_sum.
    intros.
    unfold comm_sum_on_types.
    unfold internal_paths_rew.
    unfold types_commute_sum.
    unfold internal_paths_rew_r.
    simpl.
    induction (sumcommutes x y).
    unfold mixed_sum_l,mixed_sum_r.
    unfold function_on_the_sum.
    simpl.
    exact (idpath tt).
  + induction distr as [ldistr rdistr].
    unfold isinternal_distr.
    split.
    -- unfold isinternal_distr_l.
       split.
       ++ unfold isinternal_distr_l_r.
          intros.
          unfold distr_l_on_types.
          unfold internal_paths_rew.
          unfold types_distr_l.
          unfold internal_paths_rew_r.
          simpl.
          unfold thetype.
          simpl.
          induction (ldistr y z x).
          unfold mixed_sum_r,internal_mult.
          unfold function_on_the_product, function_on_the_sum.
          simpl.
          exact (idpath tt).
       ++ unfold isinternal_distr_l_l.
          intros.
          unfold distr_l_on_types.
          unfold internal_paths_rew.
          unfold types_distr_l.
          simpl.
          unfold internal_paths_rew_r.
          simpl.
          induction (ldistr z y x).
          unfold mixed_sum_l.
          unfold internal_mult.
          unfold function_on_the_product, function_on_the_sum.
          simpl.
          exact (idpath tt).
       -- (*finally, *)
         unfold isinternal_distr_r.
         unfold isinternal_distr_r_r.
         unfold isinternal_distr_r_l.
         unfold internal_paths_rew.
         simpl.
         unfold distr_r_on_types.
         unfold internal_paths_rew.
         unfold types_distr_r.
         unfold internal_paths_rew_r.
         unfold thetype.
         simpl.
         split; intros;
         induction (rdistr y z x);
         induction (rdistr z y x);
         simpl;
           unfold mixed_sum_r , mixed_sum_l,internal_mult;
           unfold function_on_the_sum, function_on_the_product;
           exact (idpath tt).
Defined.


Example constantspacedrig_left (ℜ : rig) (Points : UU) : spacedrig.
  exists (constanttypedrig_left ℜ Points).
    induction ℜ as[theset [rest distr]].
    induction rest as[axs rest].
    induction axs as[sum product].
    induction sum as[summonoid sumcommutes].
    induction summonoid as[assocsum unitalsum].
    induction product as[assocprod unitalprod].
    simpl in rest.

  split.
  - split.
    + split;
         unfold isinternal_assoc_sum_ll;
         unfold isinternal_assoc_sum_lr;
         intros;
         unfold assoc_sum_on_types;
         unfold internal_paths_rew;
         unfold types_assoc_sum;
         simpl;
        unfold internal_paths_rew_r.
      -- induction assocsum.
         unfold mixed_sum_l.
         unfold function_on_the_sum.
         simpl.
         exact (idpath zz).
      -- intros. split.
            ++ intros. induction assocsum.
            unfold mixed_sum_l,mixed_sum_r.
            unfold function_on_the_sum.
            simpl.
            exact (idpath yy).
            ++ unfold isinternal_assoc_sum_rr.
            intros.
            unfold assoc_sum_on_types.
            unfold internal_paths_rew;
            unfold types_assoc_sum;
            simpl;
            unfold internal_paths_rew_r.
            induction assocsum.
            unfold mixed_sum_r.
            unfold function_on_the_sum.
            simpl.
            exact (idpath xx).
    + unfold isinternal_assoc_prod.
      intros.
      unfold internal_mult3_l . 
      unfold internal_mult3_r.
      unfold internal_mult.
      unfold function_on_the_product.
      simpl.
      unfold assoc_prod_on_types.
            unfold internal_paths_rew;
            unfold types_assoc_prod;
            simpl;
            unfold internal_paths_rew_r.
            induction assocprod.
            exact (idpath xx).
  - unfold isinternal_comm_sum, isinternal_distr, constanttypedrig_left.
    unfold isinternal_distr_r, isinternal_distr_l .
    unfold isinternal_distr_r_l, isinternal_distr_l_r.
    unfold isinternal_distr_r_r, isinternal_distr_l_l.
    unfold comm_sum_on_types.
    unfold distr_l_on_types, distr_r_on_types.
    unfold internal_paths_rew.
    unfold types_distr_r , types_distr_l.
    unfold types_commute_sum.
    unfold internal_paths_rew_r.
    split; intros.
    + induction sumcommutes.
      unfold mixed_sum_l,mixed_sum_r.
      unfold function_on_the_sum.
      exact (idpath xx).
    + split; intros.
      -- split; intros; induction distr;
         induction pr1;
            unfold mixed_sum_r,internal_mult;
            unfold function_on_the_product, function_on_the_sum;
            exact (idpath xx).
      -- split; induction distr;
         intros; induction pr2;
           unfold mixed_sum_r,mixed_sum_l,internal_mult;
           unfold function_on_the_product, function_on_the_sum;
           exact (idpath yy).
Defined.

Section BeautifulRigs.

  (* We want to define the "same" properties, but for the case in which
the rings are "beautiful", meaning that the function on the sum goes in
the opposite direction of the function on the product.
   This is supposed to match better with the sense of product and coproduct
   as universal constructions. 
   *)
  Definition theprettyrig ( σ : beautifulrig ) : rig.
    exact (pr1 σ).
  Defined.
  Coercion theprettyrig : beautifulrig >-> rig.
  Definition theprettyfunctor ( σ : beautifulrig ) : σ -> UU.
    induction σ. induction pr2.
    exact pr0.
  Defined.
  Coercion theprettyfunctor : beautifulrig >-> Funclass.

  Definition theprettytype { σ : beautifulrig } (x : σ) : UU.
    exact (σ x).
  Defined.

  Definition function_on_pretty_sum { σ : beautifulrig } (x y : σ)
    : (σ x) ⨿ (σ y) -> σ ( x + y )%ring .
    induction σ. induction pr2.
    exact (Preamble.pr1 (pr2 x y)).
  Defined.
  Notation "x ♭ y" := (function_on_pretty_sum x y) (at level 300).
  Definition function_on_pretty_product { σ : beautifulrig } (x y : σ)
    : (σ x) × (σ y) <- σ ( x * y )%ring .
    induction σ. induction pr2.
    exact (Preamble.pr2 (pr2 x y)).
  Defined.
  Notation "x ♯ y" := (function_on_pretty_product x y) (at level 300).

  Section BeautyUnits.
    Context {σ : beautifulrig}.
    
  Definition beauty0 : σ.
  induction σ.
  induction pr1.
  induction pr0.
  induction pr0.
  induction pr0.
  induction pr1.
  induction pr6.
  simpl.
  refine (unel ((pr1,, pr6),, _)).
  exact (Preamble.pr1 pr0).
  Defined.
  
  Definition beauty1 : σ.
  induction σ.
  induction pr1.
  induction pr0.
  induction pr0.
  induction pr0.
  induction pr1.
  induction pr6.
  simpl.
  refine (unel ((pr1,, pr7),, _)).
  exact pr5.
  Defined.
  End BeautyUnits.

  Notation "𝟘" := beauty0.
  Notation "𝟙" := beauty1.

  Section BeautyCharges.

  Context ( σ : beautifulrig).

  Definition beauty0type  := (σ 𝟘).
  Definition beauty1type  := (σ 𝟙).

  Definition isbeauty0empty  := (σ 𝟘 = ∅).
  Definition isbeauty1empty  := (σ 𝟙 = ∅).
  Definition isbeauty0unit  := (σ 𝟘 = unit).
  Definition isbeauty1unit  := (σ 𝟙 = unit).


  Definition isnegativelycharged  :=
    (isbeauty0empty × isbeauty1unit).
  Definition ispositivelycharged  : UU :=
    isbeauty0unit × isbeauty1empty.
  Definition isneutrallycharged  : UU :=
    σ 𝟘 = σ 𝟙.
  End BeautyCharges.

  Definition isbeautifulrigconstant (σ : beautifulrig) : UU :=
    ∑ ℵ : UU,
      ∏ o : σ,
        σ o = ℵ.
  
  Lemma isconstant_neutral {σ} : isbeautifulrigconstant σ -> isneutrallycharged σ.
    unfold isbeautifulrigconstant,isneutrallycharged.
    intros.
    induction X.
    pose proof (pr2 𝟘).
    pose proof (pr2 𝟙).
    rewrite X.
    rewrite X0.
    apply idpath.
  Defined.

Definition beautiful_sum {σ : beautifulrig}
  {x y : σ}
  (xy : σ x ⨿ σ y)
  := (x ♭ y) xy.
Definition beautiful_product {σ : beautifulrig}
  (x y : σ)
  (xy : σ (x * y)%ring)
  := (x ♯ y) xy.
Definition beautiful_sum_r  {σ : beautifulrig}
  {x : σ}
  (xx : σ x)
  (y : σ) : σ (x + y)%ring
   := (x ♭ y) (inl xx : σ x ⨿ σ y).

Definition beautiful_sum_l  {σ : beautifulrig}
  {y : σ}
  (x : σ)
  (yy : σ y) : σ (x + y)%ring
   := (x ♭ y) (inr yy : σ x ⨿ σ y).

Definition beautiful_mult {σ : beautifulrig} 
  {x y : σ}
  (xy : σ (x * y)%ring )
  : σ x × σ y
    := (x ♯ y) xy.

Notation "♯♯" := beautiful_mult (at level 250).
Notation "xx ⥅ y" := (beautiful_sum_r xx y) (at level 250).
Notation "x ⥆ yy" := (beautiful_sum_l x yy) (at level 250).

Definition mult_3 {σ : beautifulrig}
  {x y z : σ}
  (xyz : σ (x * y * z)%ring  )
  : σ x × σ y × σ z.
  intros.
  remember ((x * y)%ring ♯  z) as fxy_z.
  remember (fxy_z xyz) as intermediate.
  induction intermediate as [xy sz].
  remember ((x ♯ y) xy).
  induction d as [sx sy].
  split; try split. exact sx. exact sy. exact sz.
Defined.

Definition mult_3_assoc {σ : beautifulrig}
  {x y z : σ}
  (xyz : σ (x * (y * z))%ring  )
  : σ x × σ y × σ z.
  intros.
  remember (x ♯  (y * z)%ring) as fx_yz.
  remember (fx_yz xyz) as intermediate.
  induction intermediate as [sx yz].
  remember ((y ♯ z) yz).
  induction d as [sy sz].
  split; try split. exact sx. exact sy. exact sz.
Defined.

Definition beautiful_assoc_prod {σ : beautifulrig} { x y z : σ }
  :  σ ((x * y) * z)%ring  -> σ (x * (y * z))%ring.
  intros.
  induction σ.
  induction pr1.
  induction pr0.
  induction pr0.
  induction pr0.
  induction pr5.
  remember (pr5 x y z).
  unfold theprettyfunctor.
  unfold on.
  induction pr2.
  unfold op2.
  unfold op2 in p.
  simpl . simpl in p.
  rewrite <- p.
  assumption.
Defined.

Definition isbeautiful_assoc_prod (σ : beautifulrig) : UU :=
  ∏ x y z : σ,
      ∏ xyz : σ ((x * y) * z)%ring ,
        mult_3_assoc (beautiful_assoc_prod xyz)
        = mult_3 xyz.

Definition beautiful_comm_prod {σ : beautifulcommring} {x y : σ}
  : σ (x * y)%ring -> σ (y * x)%ring.
  unfold op2.
  intros.
  induction σ.
  induction pr1.
  induction pr0.
  unfold op2 in pr3.
  unfold iscomm in pr3.
  simpl. simpl in pr3.
  rewrite (pr3 y x).
  assumption.
Defined.
Definition swap { X Y } : X × Y -> Y × X.
  intros. induction X0.
  split. exact pr2. exact pr1.
Defined.
Definition coswap { X Y } : X ⨿ Y -> Y ⨿ X.
  intros. induction X0.
  right. exact a.
  left. exact b.
Defined.

Definition isbeautiful_comm_prod (σ : beautifulcommring) : UU :=
  ∏ x y : σ,
      ∏ xy : σ ( x * y)%ring ,
        swap (♯♯ xy) = ♯♯ (beautiful_comm_prod xy). 

Definition beautiful_comm_sum {σ : beautifulrig} {x y : σ}
                              : σ (x + y)%ring -> σ (y + x)%ring.
  unfold op1.
  intros.
  induction σ.
  induction pr1.
  induction pr0.
  induction pr0.
  induction pr0.
  induction pr0.
  unfold op1 in pr6.
  simpl . simpl in pr6.
  rewrite (pr6 y x).
  assumption.
Defined.

Definition beautiful_assoc_sum {σ : beautifulrig } {x y z : σ}
  : σ (x + y + z)%ring  ->  σ (x + (y + z))%ring  .
  intros.
  induction σ.
  induction pr1. repeat induction pr0.
  unfold op1 in pr0. unfold op1.
  simpl in pr0. simpl.
  rewrite <- (pr0 x y z).
  assumption.
Defined.

Definition beautiful_assoc_sum_rightright (σ : beautifulrig) : UU :=
  ∏ x y z : σ,
      ∏ xx : σ x,
        beautiful_assoc_sum (
            (xx ⥅ y) ⥅ z) =
          (xx ⥅ (y + z)%ring ).

Definition beautiful_assoc_sum_leftright (σ : beautifulrig) : UU :=
  ∏ x y z : σ,
      ∏ yy : σ y,
       beautiful_assoc_sum ( 
       (x ⥆ yy) ⥅ z) =
       (x ⥆ (yy ⥅ z)).

Definition beautiful_assoc_sum_leftleft (σ : beautifulrig) : UU :=
  ∏ x y z : σ,
      ∏ zz : σ z,
       beautiful_assoc_sum ( 
       (x + y)%ring ⥆ zz) =
       (x ⥆ (y ⥆ zz)).

Definition isbeautiful_assoc_sum (σ : beautifulrig) : UU :=
  beautiful_assoc_sum_leftleft σ
× beautiful_assoc_sum_leftright σ
× beautiful_assoc_sum_rightright σ.

Definition isbeautifully_associative (σ : beautifulrig) : UU :=
  isbeautiful_assoc_sum σ × isbeautiful_assoc_prod σ.

Definition beautiful_distr_l {σ : beautifulrig} (x y z : σ):
      σ (x * (y + z))%ring = σ (x * y + x * z)%ring .
induction σ as [rig [on rest]].
induction rig.
induction pr1 as [set [plus times]].
simpl in on.
induction pr2.
rename pr2 into distr.
unfold isdistr in distr.
induction distr as [ldistr rdistr].
remember (ldistr y z x).
unfold op1, op2.
unfold op1, op2 in p.
simpl. simpl in p.
rewrite p;apply idpath.
Defined.

Definition beautifully_distr_l {σ : beautifulrig} {x y z : σ}:
      σ (x * (y + z))%ring -> σ (x * y + x * z)%ring .
  rewrite beautiful_distr_l.
  exact (idfun _).
Defined.
Definition beautifully_factor_l {σ : beautifulrig} {x y z : σ} :
  σ (x * y + x * z)%ring  -> σ (x * (y + z))%ring .
  rewrite beautiful_distr_l.
  exact (idfun _).
Defined.

Definition beautiful_distr_r {σ : beautifulrig} ( x y z : σ ):
      σ ((y + z) * x)%ring = σ (y * x + z * x)%ring .
induction σ as [rig [on rest]].
induction rig.
induction pr1 as [set [plus times]].
simpl in on.
induction pr2.
rename pr2 into distr.
unfold isdistr in distr.
induction distr as [ldistr rdistr].
remember (rdistr y z x).
unfold op1, op2.
unfold op1, op2 in p.
simpl; simpl in p.
rewrite p;apply idpath.
Defined.
Definition beautifully_distr_r {σ : beautifulrig} {x y z : σ}:
      σ ((y + z) * x)%ring -> σ (y * x + z * x)%ring .
  rewrite beautiful_distr_r.
  exact (idfun _).
Defined.

Check beautiful_sum.
Definition isbeautiful_distr_left_up (σ : beautifulrig) : UU :=
  ∏ x y z : σ,
      ∏ xyz : σ (x * (y + z))%ring,
      ∑ xy_or_xz : σ (x * y)%ring ⨿ σ (x * z)%ring,
          beautiful_sum xy_or_xz
          =
          beautifully_distr_l xyz.
Definition isbeautiful_distr_left_down (σ : beautifulrig) : UU :=
  ∏ x y z : σ,
    ∏ xy_or_xz : σ (x * y)%ring ⨿ σ (x * z)%ring,
      ∑ xyz : σ (x * (y + z))%ring,
          beautiful_sum xy_or_xz
          =
          beautifully_distr_l xyz.
Definition isbeautiful_distr_right_up (σ : beautifulrig) : UU :=
  ∏ x y z : σ,
      ∏ xyz : σ ((x + y) * z)%ring,
      ∑ xz_or_yz : σ (x * z)%ring ⨿ σ (y * z)%ring,
          beautiful_sum xz_or_yz
          =
          beautifully_distr_r xyz.
Definition isbeautiful_distr_right_down (σ : beautifulrig) : UU :=
  ∏ x y z : σ,
    ∏ xy_or_xz : σ (x * y)%ring ⨿ σ (x * z)%ring,
      ∑ xyz : σ (x * (y + z))%ring,
          beautiful_sum xy_or_xz
          =
          beautifully_distr_l xyz.
Definition isbeautiful_distr_left (σ : beautifulrig) : UU :=
  isbeautiful_distr_left_down σ ×
  isbeautiful_distr_left_up σ.

Definition isbeautiful_distr_right (σ : beautifulrig) : UU :=
  isbeautiful_distr_right_down σ ×
  isbeautiful_distr_right_up σ.

Definition isbeautiful_distr_up (σ : beautifulrig) : UU :=
  isbeautiful_distr_left_up σ ×
  isbeautiful_distr_right_up σ.

Definition isbeautiful_distr_down (σ : beautifulrig) : UU :=
  isbeautiful_distr_left_down σ ×
  isbeautiful_distr_right_down σ.

Definition isbeautiful_distr (σ : beautifulrig) : UU :=
  isbeautiful_distr_left σ × isbeautiful_distr_right σ.

Definition isbeautiful_comm_sum (σ : beautifulrig) : UU :=
  ∏ x y : σ,
     beautiful_comm_sum ∘ (x ♭ y) = (y ♭ x) ∘ coswap.
  
Definition beautyrig : UU :=
  ∑ ϡ : beautifulrig,
      isbeautifully_associative ϡ
   ×  isbeautiful_comm_sum ϡ
   ×  isbeautiful_distr ϡ.

Section beautyrigs.
  Definition beautyrig_to_beautifulrig: beautyrig -> beautifulrig.
    exact pr1.
  Defined.
  Coercion beautyrig_to_beautifulrig: beautyrig >-> beautifulrig.

  Definition beautyring : UU :=
    ∑ ϡ : beautifulring,
      isbeautifully_associative ϡ
   ×  isbeautiful_comm_sum ϡ
   ×  isbeautiful_distr ϡ.

  Definition beautyring_to_beautyrig : beautyring -> beautyrig.
    intros; induction X.
    exists pr1.
    exact pr2.
  Defined.
  Coercion beautyring_to_beautyrig : beautyring >-> beautyrig.

  Definition beautycommring : UU :=
    ∑ ϡ : beautifulcommring,
      isbeautifully_associative ϡ
   ×  isbeautiful_comm_sum ϡ
   ×  isbeautiful_comm_prod ϡ (* the additional requirement *)
   ×  isbeautiful_distr ϡ.

  Definition beautycommring_to_beautyring : beautycommring -> beautyring.
    intros; induction X.
    exists pr1.
    split; induction pr2.
    - exact pr0.
    - induction pr2. induction pr3.
      split. exact pr2. exact pr4.
  Defined.

  Coercion beautycommring_to_beautyring : beautycommring >-> beautyring.

  Context {ϡ : beautifulrig}.
  Context {α β ℵ ℶ: ϡ}.

  Definition beautiful_fibers (data : ϡ α × ϡ β) : UU
    := ∑ x : ϡ (α * β)%ring, ♯♯ x = data.
  Definition beautiful_cofibers_left (data : ϡ (α + β)%ring) : UU
    := ∑ aa : ϡ α, (aa ⥅ β) = data.
  Definition beautiful_cofibers_right (data : ϡ (α + β)%ring) : UU
    := ∑ bb : ϡ β, (α ⥆ bb) = data.
   
  (* I think this is  what makes beautiful rings beautiful. *)
  Definition raise_beautifully
    (path : ϡ α × ϡ β -> ϡ ℵ ⨿ ϡ ℶ) : ϡ (α * β)%ring -> ϡ (ℵ + ℶ)%ring .  
    intro ab.
    remember (♯♯ ab) as aandb.
    remember (path aandb) as alephorbeth.
    exact ((ℵ ♭ ℶ) alephorbeth).
  Defined.
  Definition lower_beautifully
    (path : ϡ (α * β)%ring <- ϡ (ℵ + ℶ)%ring )  
    : ϡ α × ϡ β <- ϡ ℵ ⨿ ϡ ℶ.
    intro alephorbeth.
    remember ((ℵ ♭ ℶ) alephorbeth) as lflat.
    remember (path lflat) as wflat.
    exact (♯♯ wflat).
  Defined.
  (* In particular, logical equivalences factor through the ring  *)
  Definition combine_beautifully
    (path :
    
    

                               
        





    
    

  

          
        
    

