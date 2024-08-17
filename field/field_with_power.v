Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Inductive expression :=
| Atype : UU → expression
| minus:  expression → expression → expression
| divide: expression → expression → expression
| scalar : expression → expression → expression
| power : expression -> expression -> expression
| log : expression -> expression -> expression.

Notation "X ⨪ Y" := (minus X Y) (at level 400).
Notation "X // Y" := (divide X  Y).
Notation "X ** Y" := (scalar X  Y) (at level 400).
Notation "X ^^ Y" := (power X  Y) (at level 400).

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
  exact (Atype Y ** (X1 ^^ X2)).
  exact (Atype Y ** (log X1 X2)).
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
  (* Formal exponentiation  *)
  - exact (Atype Y ⨥ (X1 ^^ X2)).
  (* Formal logarithm  *)
  - exact (Atype Y ⨥ (log X1 X2)).
Defined.

Notation "X +ty Y" := (addtype X Y) (at level 80).

Fixpoint timesex (X : expression) : expression → expression.
  intro Y.
  induction X as [Xtype | Xdiff0 _ Xdiff1 | Xnumer _ Xdenom| Xscalar _ Xvector | Xbase _ Xexponent | Xbase _ Xlogarithm].
  - induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Yscalar _ Yvector | Ybase _ Yexponent | Ybase _ Ylogarithm].
    + exact (Atype (Xtype × Ytype)).
    + exact (Ydiff0 *ty Xtype ⨪ Ydiff1 *ty Xtype).
    + exact ((Ynumer *ty Xtype) // Ydenom).
    + exact (Yscalar ** (Yvector *ty Xtype)).
    + exact (Atype Xtype ** (Ybase ^^ Yexponent)).
    + exact (Atype Xtype ** (log Ybase Ylogarithm)).
  - induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Yscalar _ Yvector | Y | Y].
    + exact (Xdiff0 *ty Ytype ⨪ Xdiff1 *ty Ytype).
      (* This line iskey to the entire file *)
    + exact ((addd (timesex Xdiff0 Ydiff0) (timesex Xdiff1 Ydiff1)) ⨪
         (addd (timesex Xdiff1 Ydiff0) (timesex Xdiff0 Ydiff1))). 
    + exact (((timesex Xdiff0 Ynumer) ⨪ (timesex Xdiff1 Ynumer)) // Ydenom).
    + exact (Yscalar ** ((timesex Xdiff0 Yvector) ⨪ (timesex Xdiff1 Yvector))).
    + exact (Y ** (Xdiff0 ⨪ Xdiff1)).
    + exact (Y ** (Xdiff0 ⨪ Xdiff1)).
  - exact ((timesex Xnumer Y) // Xdenom).
  - exact (Xscalar ** (timesex Xvector Y)).
  - exact ((Xbase ^^ Xexponent) ** Y).
  - exact ((log Xbase Xlogarithm) ** Y).
Defined.

Fixpoint addex (X : expression) : expression → expression.
  intro Y.
  induction X as [Xtype | Xdiff0 _ Xdiff1 | Xnumer _ Xdenom| Xscalar _ Xvector | Xbase _ Xexponent | Xbase _ Xlogarithm].
  - induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Yscalar _ Yvector | Y | Y].
  (* Just a type *)
    + exact (Atype (Xtype ⨿ Ytype)).
    + exact (Ydiff0 +ty Xtype ⨪ Ydiff1).
    + exact (((Ydenom *ty Xtype) ⨥ Ynumer) // Ydenom).
    + exact (Yscalar ** ((Atype Xtype // Yscalar) ⨥ Yvector)).
    + exact (Atype Xtype ⨥ Y).
    + exact (Atype Xtype ⨥ Y).
  - induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Y | Y | Y].
  (* Formal difference *)
    + exact (Xdiff0 +ty Ytype ⨪ Xdiff1).
    + exact (addex Xdiff0 Ydiff0 ⨪ addex Xdiff1 Ydiff1).
    + exact ((Ynumer ⨥ (timesex Ydenom Xdiff0)) ⨪ (timesex Ydenom Xdiff1) // Ydenom).
    + exact ((addex Xdiff0 Y) ⨪ Xdiff1).
    + exact ((addex Xdiff0 Y) ⨪ Xdiff1). 
    + exact ((addex Xdiff0 Y) ⨪ Xdiff1). 
  - induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Y | Y | Y].
  (* Formal quotient *)
    + exact ((addex Xnumer (Xdenom *ty Ytype)) // Xdenom).
    + exact ((addex Xnumer (timesex Xdenom Ydiff0)) ⨪ (timesex Xdenom Ydiff1) // Xdenom).
    + exact (((timesex Xnumer Ydenom) ⨥ (timesex Ynumer Xdenom)) // (Ydenom ** Xdenom)).
    + exact ((addex Xnumer ((timesex Y Xdenom))) // Xdenom).
    + exact ((addex Xnumer ((timesex Y Xdenom))) // Xdenom).
    + exact ((addex Xnumer ((timesex Y Xdenom))) // Xdenom).
  - induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Yscalar _ Yvector | Y | Y].
  (* Formal scalar multiply *)
    + exact (Xscalar ** ((Atype Ytype // Xscalar) ⨥ Xvector)).
    + exact ((Ydiff0 ⨥ (Xscalar ** Xvector)) ⨪ Ydiff1).
    + exact ((Ynumer ⨥ ((timesex Ydenom (Xscalar ** Xvector)))) // Ydenom).
    + exact ((Xscalar ** Yscalar) ** (timesex Xvector Yvector)).
    + exact (Xscalar ** (timesex Xvector Y)).
    + exact (Xscalar ** (timesex Xvector Y)).
  - remember (Xbase ^^ Xexponent) as X.
    induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Y | Y | Y]. 
    + exact (Atype Ytype ⨥ X). 
    + exact ((X ⨥ Ydiff0) ⨪ Ydiff1).
    + exact (((timesex X Ydenom) ⨥ Ynumer) // Ydenom).
    + exact (X ⨥ Y).
    + exact (X ⨥ Y).
    + exact (X ⨥ Y).
  (* Formal logarithm  *)
  - remember (log Xbase Xlogarithm) as X.
    induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Y | Y | Y]. 
    + exact (Atype Ytype ⨥ X).
    + exact ((X ⨥ Ydiff0) ⨪ Ydiff1).
    + exact ((Ynumer ⨥ (timesex X Ydenom)) // Ydenom).
    + exact (X ⨥ Y).
    + exact (X ⨥ Y).
     (* This is the (potentially)  fun part of logarithm (but not yet) *)
    + exact (X ⨥ Y).
Defined.

Notation "X +ty Y" := (addtype X Y) (at level 80).

Fixpoint timesex2 (X : expression) : expression → expression.
  intro Y.
  induction X as [Xtype | Xdiff0 _ Xdiff1 | Xnumer _ Xdenom| Xscalar _ Xvector | Xbase _ Xexponent | Xbase _ Xlogarithm].
  - induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Yscalar _ Yvector | Ybase _ Yexponent | Ybase _ Ylogarithm].
    + exact (Atype (Xtype × Ytype)).
    + exact (Ydiff0 *ty Xtype ⨪ Ydiff1 *ty Xtype).
    + exact ((Ynumer *ty Xtype) // Ydenom).
    + exact (Yscalar ** (Yvector *ty Xtype)).
    + exact (Atype Xtype ** (Ybase ^^ Yexponent)).
    + exact (Atype Xtype ** (log Ybase Ylogarithm)).
  - induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Yscalar _ Yvector | Y | Y].
    + exact (Xdiff0 *ty Ytype ⨪ Xdiff1 *ty Ytype).
    (* This le
t # := # in #ne iskey to the entire file *)
    + exact ((addd (timesex Xdiff0 Ydiff0) (timesex Xdiff1 Ydiff1)) ⨪
         (addd (timesex Xdiff1 Ydiff0) (timesex Xdiff0 Ydiff1))). 
    + exact (((timesex Xdiff0 Ynumer) ⨪ (timesex Xdiff1 Ynumer)) // Ydenom).
    + exact (Yscalar ** ((timesex Xdiff0 Yvector) ⨪ (timesex Xdiff1 Yvector))).
    + exact (Y ** (Xdiff0 ⨪ Xdiff1)).
    + exact (Y ** (Xdiff0 ⨪ Xdiff1)).
  - exact ((timesex Xnumer Y) // Xdenom).
  - exact (Xscalar ** (timesex Xvector Y)).
  - exact ((Xbase ^^ Xexponent) ** Y).
  - exact ((log Xbase Xlogarithm) ** Y).
Defined.

Fixpoint equals (X : expression) : expression → UU.
  intros Y.
  induction X as [Xtype | Xdiff0 _ Xdiff1 | Xnumer _ Xdenom| Xscalar _ Xvector | Xbase _ Xexponent | Xbase _ Xlogarithm ].
  induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Yscalar _ Yvector | Ybase _ Yexponent | Ybase _ Ylogarithm ].
  (* now X is a simple type*)
  (* In many ways, this is the most important case *)
  - exact (Xtype = Ytype).
  (*- exact (Xtype = (equals Ydiff0 Ydiff1)).*)
  - exact (equals Ydiff0 (addex (Atype Xtype) Ydiff1)).
  - exact (equals Ynumer (multiplytype Ydenom Xtype)). 
  - exact (∑ Xleft Xright : UU, (Xtype = (Xright × Xleft )
                                  × (equals Yscalar (Atype Xleft))
                                  × (equals Yvector (Atype Xright)))).
  - exact (∑ Xsrc Xtarget : UU, 
                  ((Xsrc -> Xtarget) = Xtype)
                × (equals Yexponent (Atype Xsrc))
                × (equals Ybase (Atype Xtarget))).
  - induction Ybase as [Btype | Bdiff0 _ Bdiff1 | Bnumer _ Bdenom | Bscalar _ Bvector | Bbase _ Bexponent | Bbase _ Blogarithm].
    + induction Ylogarithm as [Ltype | Ldiff0 _ Ldiff1 | Lnumer _ Ldenom | Lscalar _ Lvector | Lbase _ Lexponent | Lbase _ Llogarithm].
      ++ exact ((Xtype -> Btype) = Ltype).
      ++ exact ((Xtype -> Btype) = (equals Ldiff0 Ldiff1)).
      ++ exact (∑ positive negative : UU,
                   ((Xtype -> Btype) = (positive × (negative -> ∅)))
                             × (equals (Atype positive) Lnumer)
                             × (equals (Atype negative) Ldenom)).
      ++ exact (∑ scalartype vectortype : UU,
                   ((Xtype → Btype) = (scalartype × vectortype))
                     × (equals Lscalar (Atype scalartype))
                     × (equals Lvector (Atype vectortype))).
      ++ exact (∑ base exponent : UU,
                   ((Xtype -> Btype) = (exponent -> base))
                   × (equals (Atype exponent) Lexponent)
                   × (equals (Atype base) Lbase)).
      ++ exact (∑ base powerexpression : UU,
                   ((Xtype -> Btype) -> base = powerexpression)
                     × (equals (Atype powerexpression) Llogarithm)
                     × (equals (Atype base) Lbase)).
    + remember (Bdiff0 = Bdiff1) as Btype.
      exact (∑ Ytype : UU, (equals (Atype Ytype) Ylogarithm)
                             × ((Xtype -> Btype) = Ytype)). 
    + exact (∑ Ytype Bnumertype Bdenomtype : UU,
                (equals (Atype Ytype) Ylogarithm)
                  × (equals (Atype Bnumertype) Bnumer)
                  × (equals (Atype Bdenomtype) Bdenom)
              × (((Xtype -> (Bnumertype × (Bdenomtype -> ∅))) = Ytype))).
    + exact (∑ Ytype Scatype Vectype : UU,
                (equals (Atype Ytype) Ylogarithm)
                  × (equals (Atype Scatype) Bscalar)
                  × (equals (Atype Vectype) Bvector)
                  × ((Xtype → (Scatype × Vectype)) = Ytype)).
    + exact (equals (Bexponent *ty Xtype) (log Bbase Ylogarithm)).
    + exact (∑ Ytype Basetype Logtype : UU,
                ∑ Exptype : UU,
                  (Exptype -> Basetype = Logtype)
                × (equals Ylogarithm (Atype Ytype))
                  × (equals Bbase (Atype Basetype))
                  × (equals Blogarithm (Atype Logtype))
                  × ((Xtype -> Exptype) = Ytype)).
  - (* now X is a difference *)
    induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Yscalar _ Yvector | Y | Y ].
    + exact ((equals Xdiff0 (addex Xdiff1 (Atype Ytype)))).
    + exact (equals Xdiff0 ((addex Xdiff1 Ydiff0) ⨪ Ydiff1)).
    + exact (equals Xdiff0
               ((addex Ynumer
                  (timesex Ydenom Xdiff1)) // Ydenom)).
    + exact (equals Xdiff0 (addex Xdiff1 (Yscalar ** Yvector))).
    + exact (equals Xdiff0 (addex Xdiff1 Y)).
    + exact (equals Xdiff0 (addex Xdiff1 Y)).
  - (* Now X is a quotient *)
    induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Yscalar _  Yvector | Y | Y].
    + exact (equals Xnumer (Xdenom *ty Ytype)).
    + exact (equals Xdenom ((addex Xnumer (timesex Xdenom Ydiff1)) // Ydiff0)).
    + exact (equals Xnumer ((timesex Ynumer Xdenom) // Ydenom)).
    + exact (equals Xnumer (timesex Xdenom (timesex Yscalar Yvector))).
    + exact (equals Xnumer (timesex Xdenom Y)).
    + exact (equals Xnumer (timesex Xdenom Y)).
  - induction Y as [Ytype | Ydiff0 _ Ydiff1 | Ynumer _ Ydenom| Y | Y | Y].
    + exact (equals Xvector ((Atype Ytype) // Xscalar)).
    + exact (equals Xvector (Ydiff0 ⨪ Ydiff1 // Xscalar)).
    + exact (equals Xvector (Ynumer // (timesex Ydenom Xscalar))).
    + exact (equals Xvector (Y // Xscalar)).
    + exact (equals Xvector (Y // Xscalar)).
    + exact (equals Xvector (Y // Xscalar)).
  - (* Now X is a exponentiation *)
    remember (Xbase ^^ Xexponent) as X.
    induction Y as [Ytype | Y | Y | Y | Ybase _ Yexponent | Ybase _ Ylogarithm ].
    + exact (∑ Ysrc Ytarget : UU, 
                  ((Ysrc -> Ytarget) = Ytype)
                × (equals Xexponent (Atype Ysrc))
                × (equals Xbase (Atype Ytarget))).
    + exact (equals Xexponent (log Xbase Y)).
    + exact (equals Xexponent (log Xbase Y)).
    + exact (equals Xexponent (log Xbase Y)).
    + remember (Ybase ^^ Yexponent) as Y.
      exact (equals Xexponent (log Xbase Y)).
      (* exact (equals (log (timesex Xexponent Yexponent) Y)
                    (log (timesex Xexponent Yexponent) X)). *)
    + remember (log Ybase Ylogarithm) as Y.
      exact (equals Xexponent (log Xbase Y)).
  - (* Now X is logarithm *) 
    remember (log Xbase Xlogarithm) as X.
    induction Y as [Ytype | Y | Y | Y | Y | Ybase _ Ylogarithm ].
   (* + exact (equals Xlogarithm (Xbase ^^ (Atype Ytype))). *)
    + exact (∑ Ysrc Ytarget : UU, 
              (equals Xlogarithm (Atype (Ysrc -> Ytarget)))
                × (Ysrc = Ytype)
                × (equals Xbase (Atype Ytarget))).
    + exact (equals Xlogarithm (Xbase ^^ Y)).
    + exact (equals Xlogarithm (Xbase ^^ Y)).
    + exact (equals Xlogarithm (Xbase ^^ Y)).
    + exact (equals Xlogarithm (Xbase ^^ Y)).
    + remember (log Ybase Ylogarithm) as Y.
      exact (equals Xlogarithm (Xbase ^^ Y)).
Defined.


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
    
    
