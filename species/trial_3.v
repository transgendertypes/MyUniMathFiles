Require Import UniMath.Foundations.All.

Inductive Polynomial : UU :=
| the : UU -> Polynomial
| plus : Polynomial → Polynomial → Polynomial
| times (fx : Polynomial) (gx : Polynomial) : Polynomial
| derive : Polynomial -> Polynomial -> Polynomial.

Fixpoint evaluate (fx: Polynomial) : Polynomial.
  induction fx.
  - exact (the u).
  - exact (plus IHfx1 IHfx2).
  - exact (plus (times IHfx1 fx2) (times fx1 IHfx2)).
  - 

  
