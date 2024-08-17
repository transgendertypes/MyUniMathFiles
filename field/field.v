Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Inductive expression :=
| Atype : UU → expression
| minus:  expression → expression → expression
| divide: expression → expression → expression
| scalar : expression → expression → expression .

Notation "X ⨪ Y" := (minus X Y) (at level 400).
Notation "X // Y" := (divide X  Y).
Notation "X ** Y" := (scalar X  Y) (at level 400).

Definition addd (X Y : expression) : expression :=
  (X ⨪ ((Atype ∅) ⨪ Y)). 

Notation "X ⨥ Y" := (minus X Y) (at level 400).

Fixpoint multiplytype (X : expression) : UU → expression.
  intro Y.
  induction X.
  exact (Atype (u × Y)). 
  exact ((multiplytype X1 Y) ⨪ (multiplytype X2 Y)).
  exact ((multiplytype X1 Y) // (multiplytype X2 Y)). (* notice this is weird*)
  exact (X1 ** (multiplytype X2 Y)).
Defined.

Notation "X *ty Y" := (multiplytype X Y) (at level 60).
  
Fixpoint addtype (X : expression) : UU → expression.
  intro Y.
  induction X.
  (* Just a type *)
  - exact (Atype (u ⨿ Y)).
  (* Formal difference *)
  - exact ((addtype X1 Y) ⨪ X2).
  (* Formal quotient *)
  - exact (((X2 *ty Y) ⨥ X1) // X2). 
  (* Formal scalar multiply *)
  - exact (X1 ** ((Atype Y // X1) ⨥ X2)). 
Defined.

Notation "X +ty Y" := (addtype X Y) (at level 80).

Fixpoint timesex (X : expression) : expression → expression.
  intro Y.
  induction X as [Xtype | Xdiff0 _ Xdiff1 | Xnumer _ Xdenom| Xscalar _ Xvector].
  - induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Yscalar _ Yvector].
    + exact (Atype (Xtype × Ytype)).
    + exact (Ydiff0 *ty Xtype ⨪ Ydiff1 *ty Xtype).
    + exact ((Ynumer *ty Xtype) // Ydenom).
    + exact (Yscalar ** (Yvector *ty Xtype)).
  - induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Yscalar _ Yvector].
    + exact (Xdiff0 *ty Ytype ⨪ Xdiff1 *ty Ytype).
      (* This line iskey to the entire file *)
    + exact ((addd (timesex Xdiff0 Ydiff0) (timesex Xdiff1 Ydiff1)) ⨪
         (addd (timesex Xdiff1 Ydiff0) (timesex Xdiff0 Ydiff1))). 
    + exact (((timesex Xdiff0 Ynumer) ⨪ (timesex Xdiff1 Ynumer)) // Ydenom).
    + exact (Yscalar ** ((timesex Xdiff0 Yvector) ⨪ (timesex Xdiff1 Yvector))).
  - exact ((timesex Xnumer Y) // Xdenom).
  - exact (Xscalar ** (timesex Xvector Y)).
Defined.

Fixpoint addex (X : expression) : expression → expression.
  intro Y.
  induction X as [Xtype | Xdiff0 _ Xdiff1 | Xnumer _ Xdenom| Xscalar _ Xvector].
  - induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Yscalar _ Yvector].
    + exact (Atype (Xtype ⨿ Ytype)).
    + exact (Ydiff0 +ty Xtype ⨪ Ydiff1).
    + exact (((Ydenom *ty Xtype) ⨥ Ynumer) // Ydenom).
    + exact (Yscalar ** ((Atype Xtype // Yscalar) ⨥ Yvector)).
  - induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Yscalar _ Yvector].
    + exact (Xdiff0 +ty Ytype ⨪ Xdiff1).
    + exact (addex Xdiff0 Ydiff0 ⨪ addex Xdiff1 Ydiff1).
    + exact ((Ynumer ⨥ (timesex Ydenom Xdiff0)) ⨪ (timesex Ydenom Xdiff1) // Ydenom).
    + exact (addex Xdiff0 (Yscalar ** Yvector) ⨪ Xdiff1).
  - induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Yscalar _ Yvector].
    + exact ((addex Xnumer (Xdenom *ty Ytype)) // Xdenom).
    + exact ((addex Xnumer (timesex Xdenom Ydiff0)) ⨪ (timesex Xdenom Ydiff1) // Xdenom).
    + exact (((timesex Xnumer Xdenom) ⨥ (timesex Xdenom Ynumer)) // (Ydenom ** Xdenom)).
    + exact ((addex Xnumer ((timesex Xdenom (Yscalar ** Yvector)))) // Xdenom).
  - 
    induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Yscalar _ Yvector].
    + exact (Xscalar ** ((Atype Ytype // Xscalar) ⨥ Xvector)).
    + exact ((Ydiff0 ⨥ (Xscalar ** Xvector)) ⨪ Ydiff1).
    + exact ((Ynumer ⨥ ((timesex Ydenom (Xscalar ** Xvector)))) // Ydenom).
    + exact ((Xscalar ** Yscalar) ** (timesex Xvector Yvector)).
Defined.

Fixpoint equals (X : expression) : expression → UU.
  intros Y.
  induction X as [Xtype | Xdiff0 _ Xdiff1 | Xnumer _ Xdenom| Xscalar _ Xvector].
  induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Yscalar _ Yvector].
  (* now X is a simple type*)
  - exact (Xtype = Ytype).
  - exact (Xtype = (equals Ydiff0 Ydiff1)).
  - exact (equals (multiplytype Ydenom Xtype) Ynumer). 
  - exact (equals (divide (Atype Xtype) Yscalar) Yvector).
   
  - (* now X is a difference *)
    induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Yscalar _ Yvector].
    + exact ((equals Xdiff0 Xdiff1) = Ytype).
    + exact (equals (addex Xdiff0 Ydiff1) (addex Xdiff1 Ydiff0)).
    + exact (equals (timesex Ydenom Xdiff0)
               (addex Ynumer
                  (timesex Ydenom Xdiff1))).
    + exact (equals Xdiff0 (addex Xdiff1 (Yscalar ** Yvector))).
  - (* Now X is a quotient *)
    induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Yscalar _ Yvector].
    + exact (equals Xnumer (Xdenom *ty Ytype)).
    + exact (equals (timesex Xdenom Ydiff0) (addex Xnumer (timesex Xdenom Ydiff1))).
    + exact (equals (timesex Xnumer Ydenom) (timesex Ynumer Xdenom)).
    + exact (equals Xnumer (timesex Xdenom (Yscalar ** Yvector))).
  -  
    induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Yscalar _ Yvector].
    + exact (equals (divide (Atype Ytype) Xscalar) Xvector).
    + exact (equals Ydiff0 (addex Ydiff1 (Xscalar ** Xvector))).
    + exact (equals Ynumer (timesex Ydenom (Xscalar ** Xvector))).
    + exact (equals (timesex Xvector Xscalar) (timesex Yvector Yscalar)).
Abort.


Fixpoint decode (X: expression) : UU.
  induction X.
  - assumption.
  - exact (X1 = X2).     (* minus *)
  - exact ((decode X1) × (¬ decode X2)). (* division *)
  - exact ((decode X2) × (¬ ¬ decode X1)).
Defined.

Definition exlessthan : expression → expression → UU.
  intros X Y.
  exact (incl (decode X) (decode Y)).
Defined.
Definition UUlessthan : UU → UU → UU.
  intros X Y.
  exact (incl X Y).
Defined.
Definition mixedLessthan : expression → UU → UU.
  intros X Y.
  exact (incl (decode X) Y).
Defined.

Definition family (X : UU) := X → expression.
Definition upper_bounds {X} (FF : family X) : UU :=
  ∑ Bound : UU, ∏ Y : X, mixedLessthan (FF Y) Bound.
Definition least_upper_bound {X} (FF : family X) : UU :=
  ∑ least_bound: upper_bounds FF, ∏ bound : upper_bounds FF,
        incl (pr1 least_bound) (pr1 bound).

Axiom least_upper_bound_property :
  ∏ X : UU,
      ∏ FF : family X,
        least_upper_bound FF.
    
    
