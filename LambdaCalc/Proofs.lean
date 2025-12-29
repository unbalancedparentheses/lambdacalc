/-
  Lambda Calculus Formal Proofs and Invariants

  This module contains formally verified proofs about the lambda calculus
  implementation.
-/

import LambdaCalc.Basic

namespace LambdaCalc

open Term

/-!
## Term Size and Structural Properties
-/

/-- Size of a lambda term (number of constructors) -/
def Term.size : Term -> Nat
  | var _ => 1
  | lam body => 1 + body.size
  | app t1 t2 => 1 + t1.size + t2.size

/-!
## Depth of Lambda Terms
-/

/-- Depth of a lambda term (longest path to a leaf) -/
def Term.depth : Term -> Nat
  | var _ => 0
  | lam body => 1 + body.depth
  | app t1 t2 => 1 + max t1.depth t2.depth

/-- Depth of application -/
theorem Term.depth_app (t1 t2 : Term) :
    (app t1 t2).depth = 1 + max t1.depth t2.depth := rfl

/-- Depth of lambda -/
theorem Term.depth_lam (body : Term) :
    (lam body).depth = 1 + body.depth := rfl

/-!
## Well-Formedness Predicate
-/

/-- A term is well-formed at depth d if all free variables have index < d -/
def WellFormed (d : Nat) : Term -> Prop
  | var n => n < d
  | lam body => WellFormed (d + 1) body
  | app t1 t2 => WellFormed d t1 /\ WellFormed d t2

/-- Boolean version of well-formedness check -/
def isWellFormed (d : Nat) (t : Term) : Bool :=
  match t with
  | var n => n < d
  | lam body => isWellFormed (d + 1) body
  | app t1 t2 => isWellFormed d t1 && isWellFormed d t2

/-!
## Substitution Properties
-/

/-- Substitution distributes over application -/
theorem subst_app (j : Nat) (s t1 t2 : Term) :
    subst j s (app t1 t2) = app (subst j s t1) (subst j s t2) := rfl

/-- Substitution goes under lambda with index shift -/
theorem subst_lam (j : Nat) (s body : Term) :
    subst j s (lam body) = lam (subst (j + 1) (shift 1 0 s) body) := rfl

/-!
## Beta Reduction Properties
-/

/-- Reduction with 0 fuel returns the original term -/
theorem reduce_zero_fuel (t : Term) : reduce 0 t = t := rfl

/-!
## Church Encoding Correctness Theorems
-/

/-- Church zero equals the explicit definition -/
theorem churchNum_zero_eq : churchNum 0 = churchZero := rfl

/-- Church one equals the explicit definition -/
theorem churchNum_one_eq : churchNum 1 = churchOne := rfl

/-- Church two equals the explicit definition -/
theorem churchNum_two_eq : churchNum 2 = churchTwo := rfl

/-- Church booleans are distinct -/
theorem churchTrue_neq_churchFalse : churchTrue ≠ churchFalse := by
  intro h
  simp only [churchTrue, churchFalse] at h
  injection h with h'
  injection h' with h''
  cases h''

/-!
## Additional Structural Lemmas
-/

/-- Variables are in normal form -/
theorem var_normalForm (n : Nat) : isNormalForm (var n) = true := rfl

/-- Count variable occurrences in variable -/
theorem countVarOccurrences_var (n : Nat) : countVarOccurrences (var n) = 1 := rfl

/-- Count variable occurrences in lambda -/
theorem countVarOccurrences_lam (body : Term) :
    countVarOccurrences (lam body) = countVarOccurrences body := rfl

/-- Count variable occurrences in application -/
theorem countVarOccurrences_app (t1 t2 : Term) :
    countVarOccurrences (app t1 t2) =
    countVarOccurrences t1 + countVarOccurrences t2 := rfl

end LambdaCalc
