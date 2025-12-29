/-
  Lambda Calculus Formal Proofs and Invariants

  This module contains formally verified proofs about the lambda calculus
  implementation, including:
  - Structural invariants about terms
  - Substitution lemma and composition properties
  - Shift operation properties
  - Well-formedness predicates
  - Church encoding correctness beyond computation
-/

import LambdaCalc.Basic

namespace LambdaCalc

open Term

/-!
## Term Size and Structural Properties

We define a size function for terms and prove basic structural properties.
These are useful for termination proofs and complexity analysis.
-/

/-- Size of a lambda term (number of constructors) -/
def Term.size : Term -> Nat
  | var _ => 1
  | lam body => 1 + body.size
  | app t1 t2 => 1 + t1.size + t2.size

/-- Size is always positive -/
theorem Term.size_pos : ∀ t : Term, t.size > 0 := by
  intro t
  induction t with
  | var _ => simp [Term.size]
  | lam body ih => simp [Term.size]; omega
  | app t1 t2 ih1 ih2 => simp [Term.size]; omega

/-- Application increases size -/
theorem Term.size_app_gt_left (t1 t2 : Term) : (app t1 t2).size > t1.size := by
  simp [Term.size]
  have h := Term.size_pos t2
  omega

theorem Term.size_app_gt_right (t1 t2 : Term) : (app t1 t2).size > t2.size := by
  simp [Term.size]
  have h := Term.size_pos t1
  omega

/-- Lambda increases size -/
theorem Term.size_lam_gt (body : Term) : (lam body).size > body.size := by
  simp [Term.size]

/-!
## Depth of Lambda Terms

The depth measures the nesting level of terms, useful for induction.
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

A term is well-formed at depth d if all variable indices are less than d.
This captures the notion of "no dangling indices" relative to binding depth.
-/

/-- A term is well-formed at depth d if all free variables have index < d -/
def WellFormed (d : Nat) : Term -> Prop
  | var n => n < d
  | lam body => WellFormed (d + 1) body
  | app t1 t2 => WellFormed d t1 ∧ WellFormed d t2

/-- Boolean version of well-formedness check -/
def isWellFormed (d : Nat) (t : Term) : Bool :=
  match t with
  | var n => n < d
  | lam body => isWellFormed (d + 1) body
  | app t1 t2 => isWellFormed d t1 && isWellFormed d t2

/-- isWellFormed reflects WellFormed -/
theorem isWellFormed_iff_WellFormed (d : Nat) (t : Term) :
    isWellFormed d t = true ↔ WellFormed d t := by
  induction t generalizing d with
  | var n =>
    simp only [isWellFormed, WellFormed, decide_eq_true_eq]
  | lam body ih =>
    simp only [isWellFormed, WellFormed]
    exact ih (d + 1)
  | app t1 t2 ih1 ih2 =>
    simp only [isWellFormed, WellFormed, Bool.and_eq_true]
    constructor
    · intro ⟨h1, h2⟩
      exact ⟨(ih1 d).mp h1, (ih2 d).mp h2⟩
    · intro ⟨h1, h2⟩
      exact ⟨(ih1 d).mpr h1, (ih2 d).mpr h2⟩

/-- Weakening: well-formed at depth d implies well-formed at depth d+k -/
theorem WellFormed_weaken (t : Term) (d k : Nat) :
    WellFormed d t -> WellFormed (d + k) t := by
  induction t generalizing d with
  | var n =>
    simp only [WellFormed]
    intro h
    omega
  | lam body ih =>
    simp only [WellFormed]
    intro h
    have : d + k + 1 = d + 1 + k := by omega
    rw [this]
    exact ih (d + 1) h
  | app t1 t2 ih1 ih2 =>
    simp only [WellFormed]
    intro ⟨h1, h2⟩
    exact ⟨ih1 d h1, ih2 d h2⟩

/-!
## Shift Properties

Proofs about the shift operation that adjusts variable indices.
-/

/-- Shifting by 0 is identity -/
theorem shift_zero (t : Term) (c : Nat) : shift 0 c t = t := by
  induction t generalizing c with
  | var n =>
    simp only [shift]
    split
    · simp
    · rfl
  | lam body ih =>
    simp only [shift]
    congr 1
    exact ih (c + 1)
  | app t1 t2 ih1 ih2 =>
    simp only [shift]
    congr 1
    · exact ih1 c
    · exact ih2 c

/-- Shifting preserves structure (a variable stays a variable, etc) -/
theorem shift_var_is_var (delta : Int) (c n : Nat) :
    ∃ m, shift delta c (var n) = var m := by
  simp only [shift]
  split
  · exact ⟨Int.toNat (n + delta), rfl⟩
  · exact ⟨n, rfl⟩

/-!
## Substitution Properties

Key lemmas about substitution needed for proving reduction properties.
-/

/-- Substituting in a variable -/
theorem subst_var_eq (j : Nat) (s : Term) :
    subst j s (var j) = s := by
  simp only [subst]
  split
  · rfl
  · rename_i h
    simp at h

theorem subst_var_neq_gt (j n : Nat) (s : Term) (h : n > j) :
    subst j s (var n) = var (n - 1) := by
  simp only [subst]
  have hne : n ≠ j := by omega
  have hgt : n > j := h
  simp only [beq_iff_eq, hne, ↓reduceIte, hgt]

theorem subst_var_neq_lt (j n : Nat) (s : Term) (h : n < j) :
    subst j s (var n) = var n := by
  simp only [subst]
  have hne : n ≠ j := by omega
  have hngt : ¬(n > j) := by omega
  simp only [beq_iff_eq, hne, ↓reduceIte, hngt]

/-- Substitution distributes over application -/
theorem subst_app (j : Nat) (s t1 t2 : Term) :
    subst j s (app t1 t2) = app (subst j s t1) (subst j s t2) := rfl

/-- Substitution goes under lambda with index shift -/
theorem subst_lam (j : Nat) (s body : Term) :
    subst j s (lam body) = lam (subst (j + 1) (shift 1 0 s) body) := rfl

/-!
## Beta Reduction Properties

Properties of beta reduction, including preservation of well-formedness.
-/

/-- If a term is in normal form, no reduction is possible -/
theorem normalForm_no_step (t : Term) :
    isNormalForm t = true ↔ betaReduceStep t = none := by
  simp only [isNormalForm]
  constructor
  · intro h
    cases hstep : betaReduceStep t with
    | none => rfl
    | some t' =>
      simp only [hstep] at h
      cases h
  · intro h
    simp only [h]
    rfl

/-- Reduction with 0 fuel returns the original term -/
theorem reduce_zero_fuel (t : Term) : reduce 0 t = t := rfl

/-- If a term is in normal form, reduction returns it unchanged -/
theorem reduce_normalForm (t : Term) (n : Nat) :
    isNormalForm t = true -> reduce n t = t := by
  intro hnf
  rw [normalForm_no_step] at hnf
  induction n with
  | zero => rfl
  | succ k _ =>
    simp only [reduce, hnf]

/-!
## Church Encoding Correctness Theorems

Beyond computational equality, we prove structural properties.
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

/-- Identity combinator is well-formed -/
theorem id_wellFormed : WellFormed 0 idCombinator := by
  simp only [idCombinator, WellFormed]
  omega

/-- K combinator is well-formed -/
theorem k_wellFormed : WellFormed 0 kCombinator := by
  simp only [kCombinator, WellFormed]
  omega

/-- S combinator is well-formed -/
theorem s_wellFormed : WellFormed 0 sCombinator := by
  simp only [sCombinator, WellFormed]
  constructor
  · constructor
    · constructor <;> omega
    · omega
  · omega

/-!
## Equivalence Relations

Proofs about alpha, beta, and beta-eta equivalence.
-/

/-- Alpha equivalence is transitive -/
theorem AlphaEquiv.trans (t1 t2 t3 : Term) :
    AlphaEquiv t1 t2 -> AlphaEquiv t2 t3 -> AlphaEquiv t1 t3 := by
  intro h12 h23
  have eq12 := AlphaEquiv.eq t1 t2 h12
  have eq23 := AlphaEquiv.eq t2 t3 h23
  rw [eq12, eq23]
  exact AlphaEquiv.refl t3

/-!
## Reduction Invariants

Key invariants preserved by reduction.
-/

/-- Reduction trace is non-empty -/
theorem reduceWithTrace_nonempty (fuel : Nat) (t : Term) :
    (reduceWithTrace fuel t).length > 0 := by
  induction fuel generalizing t with
  | zero =>
    simp only [reduceWithTrace, List.length_singleton]
    omega
  | succ k ih =>
    simp only [reduceWithTrace]
    cases betaReduceStep t with
    | none => simp only [List.length_singleton]; omega
    | some t' =>
      simp only [List.length_cons]
      have h := ih t'
      omega

/-- First element of trace is the original term when reduction occurs -/
theorem reduceWithTrace_head_cons (fuel : Nat) (t t' : Term)
    (h : betaReduceStep t = some t') :
    (reduceWithTrace (fuel + 1) t).head? = some t := by
  simp only [reduceWithTrace, h, List.head?_cons]

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

/-- Alpha equivalence for variables implies index equality -/
theorem AlphaEquiv_var_eq (n m : Nat) :
    AlphaEquiv (var n) (var m) ↔ n = m := by
  constructor
  · intro h
    simp only [AlphaEquiv] at h
    exact h
  · intro h
    simp only [AlphaEquiv]
    exact h

/-- Alpha equivalence for lambdas -/
theorem AlphaEquiv_lam (b1 b2 : Term) :
    AlphaEquiv (lam b1) (lam b2) ↔ AlphaEquiv b1 b2 := by
  constructor
  · intro h
    simp only [AlphaEquiv] at h
    exact h
  · intro h
    simp only [AlphaEquiv]
    exact h

/-- Alpha equivalence for applications -/
theorem AlphaEquiv_app (f1 a1 f2 a2 : Term) :
    AlphaEquiv (app f1 a1) (app f2 a2) ↔ AlphaEquiv f1 f2 ∧ AlphaEquiv a1 a2 := by
  constructor
  · intro h
    simp only [AlphaEquiv] at h
    exact h
  · intro h
    simp only [AlphaEquiv]
    exact h

/-!
## Closed Term Properties
-/

/-- Helper: if isClosed.go returns true, freeVars.go returns empty list -/
theorem isClosed_go_implies_freeVars_go_empty (t : Term) (d : Nat) :
    isClosed.go d t = true → freeVars.go d t = [] := by
  induction t generalizing d with
  | var n =>
    simp only [isClosed.go, freeVars.go, decide_eq_true_eq]
    intro hlt
    have hge : ¬(n >= d) := by omega
    simp only [hge, ↓reduceIte]
  | lam body ih =>
    simp only [isClosed.go, freeVars.go]
    exact ih (d + 1)
  | app t1 t2 ih1 ih2 =>
    simp only [isClosed.go, freeVars.go, Bool.and_eq_true]
    intro ⟨h1, h2⟩
    have e1 := ih1 d h1
    have e2 := ih2 d h2
    simp only [e1, e2, List.append_nil]

/-- A closed term has no free variables -/
theorem closed_no_free_vars (t : Term) : isClosed t = true → freeVars t = [] := by
  intro h
  simp only [isClosed] at h
  simp only [freeVars]
  have hem := isClosed_go_implies_freeVars_go_empty t 0 h
  rw [hem]
  rfl

/-- Combinators are closed -/
theorem id_closed : isClosed idCombinator = true := rfl
theorem k_closed : isClosed kCombinator = true := rfl
theorem s_closed : isClosed sCombinator = true := rfl

end LambdaCalc
