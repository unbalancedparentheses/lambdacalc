/-
  Lambda Calculus Implementation in Lean 4

  This module provides:
  - A data type for lambda terms (variables, abstractions, applications)
  - Substitution function
  - Beta reduction (single step and multi-step)
  - Eta reduction
  - Alpha equivalence (trivial for de Bruijn terms)
  - Church encodings (booleans, numerals, pairs, arithmetic)
  - Recursive functions via Y combinator
  - Pretty printing for lambda terms
-/

namespace LambdaCalc

/-- Lambda terms using de Bruijn indices for variables -/
inductive Term where
  | var : Nat -> Term           -- Variable (de Bruijn index)
  | lam : Term -> Term          -- Lambda abstraction
  | app : Term -> Term -> Term  -- Application
  deriving Repr, BEq, Inhabited, DecidableEq

open Term

/-- Pretty print a lambda term with de Bruijn indices -/
def Term.toString : Term -> String
  | var n => s!"x{n}"
  | lam body => s!"(λ. {body.toString})"
  | app t1 t2 => s!"({t1.toString} {t2.toString})"

instance : ToString Term where
  toString := Term.toString

/-
  Variable Analysis Functions
-/

/-- Check if variable with index n appears free in term -/
def hasFreeVar (n : Nat) : Term -> Bool
  | var m => m == n
  | lam body => hasFreeVar (n + 1) body
  | app t1 t2 => hasFreeVar n t1 || hasFreeVar n t2

/-- Count the number of variable occurrences in a term -/
def countVarOccurrences : Term -> Nat
  | var _ => 1
  | lam body => countVarOccurrences body
  | app t1 t2 => countVarOccurrences t1 + countVarOccurrences t2

/-- Check if a term is closed (has no free variables) -/
def isClosed (t : Term) : Bool :=
  go 0 t
where
  go (depth : Nat) : Term -> Bool
    | var n => n < depth
    | lam body => go (depth + 1) body
    | app t1 t2 => go depth t1 && go depth t2

/-- Get the set of free variable indices in a term -/
def freeVars (t : Term) : List Nat :=
  go 0 t |>.eraseDups
where
  go (depth : Nat) : Term -> List Nat
    | var n => if n >= depth then [n - depth] else []
    | lam body => go (depth + 1) body
    | app t1 t2 => go depth t1 ++ go depth t2

/-
  Alpha Equivalence

  For de Bruijn indexed terms, alpha equivalence is exactly structural equality.
  Two terms are alpha-equivalent iff they have the same de Bruijn representation.
-/

/-- Alpha equivalence for de Bruijn indexed terms is structural equality -/
def alphaEquiv (t1 t2 : Term) : Bool := t1 == t2

/-- Alpha equivalence as a proposition -/
def AlphaEquiv : Term -> Term -> Prop
  | var n, var m => n = m
  | lam b1, lam b2 => AlphaEquiv b1 b2
  | app f1 a1, app f2 a2 => AlphaEquiv f1 f2 ∧ AlphaEquiv a1 a2
  | _, _ => False

/-- AlphaEquiv is reflexive -/
theorem AlphaEquiv.refl : ∀ t, AlphaEquiv t t
  | var _ => rfl
  | lam body => AlphaEquiv.refl body
  | app t1 t2 => ⟨AlphaEquiv.refl t1, AlphaEquiv.refl t2⟩

/-- AlphaEquiv is symmetric -/
theorem AlphaEquiv.symm (t1 t2 : Term) (h : AlphaEquiv t1 t2) : AlphaEquiv t2 t1 := by
  induction t1 generalizing t2 with
  | var n =>
    cases t2 with
    | var m =>
      simp only [AlphaEquiv] at h ⊢
      exact Eq.symm h
    | lam _ => exact False.elim h
    | app _ _ => exact False.elim h
  | lam b1 ih =>
    cases t2 with
    | var _ => exact False.elim h
    | lam b2 => exact ih b2 h
    | app _ _ => exact False.elim h
  | app f1 a1 ihf iha =>
    cases t2 with
    | var _ => exact False.elim h
    | lam _ => exact False.elim h
    | app f2 a2 => exact ⟨ihf f2 h.1, iha a2 h.2⟩

/-- AlphaEquiv implies structural equality for de Bruijn terms -/
theorem AlphaEquiv.eq : ∀ t1 t2, AlphaEquiv t1 t2 -> t1 = t2
  | var n, var m, h => by
    simp only [AlphaEquiv] at h
    rw [h]
  | lam b1, lam b2, h => by simp [AlphaEquiv.eq b1 b2 h]
  | app f1 a1, app f2 a2, ⟨hf, ha⟩ => by
    simp [AlphaEquiv.eq f1 f2 hf, AlphaEquiv.eq a1 a2 ha]

/-
  Shifting and Substitution
-/

/-- Shift all free variables (with index >= cutoff) by delta.

    PRECONDITION: For any variable `n >= cutoff`, we must have `n + delta >= 0`.
    If this precondition is violated, the behavior is undefined (Int.toNat maps
    negative values to 0, which may produce incorrect terms).

    This is safe when:
    - delta >= 0 (always safe)
    - delta < 0 and all free variables have index >= |delta| relative to cutoff
-/
def shift (delta : Int) (cutoff : Nat) : Term -> Term
  | var n =>
    if n >= cutoff then
      let newIdx := n + delta
      -- Debug assertion: uncomment to catch precondition violations during development
      -- if newIdx < 0 then dbg_trace "WARNING: shift produced negative index!"
      var (Int.toNat newIdx)
    else
      var n  -- bound variable unchanged
  | lam body => lam (shift delta (cutoff + 1) body)
  | app t1 t2 => app (shift delta cutoff t1) (shift delta cutoff t2)

/-- Substitute term s for variable index j in term t -/
def subst (j : Nat) (s : Term) : Term -> Term
  | var n =>
    if n == j then s
    else if n > j then var (n - 1)  -- adjust index for removed binder
    else var n
  | lam body =>
    -- When going under a binder:
    -- 1. Increment the target index
    -- 2. Shift free variables in s up by 1
    lam (subst (j + 1) (shift 1 0 s) body)
  | app t1 t2 => app (subst j s t1) (subst j s t2)

/-
  Beta Reduction
-/

/-- Perform a single beta reduction step if possible (leftmost-outermost) -/
def betaReduceStep : Term -> Option Term
  | app (lam body) arg =>
    -- Beta reduction: (λ. body) arg -> body[0 := arg]
    some (subst 0 arg body)
  | app t1 t2 =>
    -- Try reducing left side first (leftmost-outermost)
    match betaReduceStep t1 with
    | some t1' => some (app t1' t2)
    | none =>
      -- Try reducing right side
      match betaReduceStep t2 with
      | some t2' => some (app t1 t2')
      | none => none
  | lam body =>
    -- Reduce under lambda
    match betaReduceStep body with
    | some body' => some (lam body')
    | none => none
  | var _ => none

/-- Check if a term is in beta normal form (no beta redex) -/
def isNormalForm (t : Term) : Bool :=
  betaReduceStep t == none

/-- Reduce a term to beta normal form with a fuel limit -/
def reduce (fuel : Nat) (t : Term) : Term :=
  match fuel with
  | 0 => t
  | fuel' + 1 =>
    match betaReduceStep t with
    | some t' => reduce fuel' t'
    | none => t

/-- Reduce and return the trace of all intermediate terms -/
def reduceWithTrace (fuel : Nat) (t : Term) : List Term :=
  match fuel with
  | 0 => [t]
  | fuel' + 1 =>
    match betaReduceStep t with
    | some t' => t :: reduceWithTrace fuel' t'
    | none => [t]

/-
  Eta Reduction

  Eta reduction: λx. (M x) -> M  when x does not appear free in M
  In de Bruijn notation: λ. (M 0) -> shift(-1, 0, M)  when 0 not free in M
-/

/-- Single step eta reduction -/
def etaReduceStep : Term -> Option Term
  | lam (app body (var 0)) =>
    -- Check if var 0 is NOT free in body (required for eta reduction)
    if not (hasFreeVar 0 body) then
      some (shift (-1) 0 body)  -- Remove the outer binder, adjust indices
    else
      none
  | lam body =>
    match etaReduceStep body with
    | some body' => some (lam body')
    | none => none
  | app t1 t2 =>
    match etaReduceStep t1 with
    | some t1' => some (app t1' t2)
    | none =>
      match etaReduceStep t2 with
      | some t2' => some (app t1 t2')
      | none => none
  | var _ => none

/-- Check if a term is in eta normal form -/
def isEtaNormalForm (t : Term) : Bool :=
  etaReduceStep t == none

/-- Perform eta reduction to normal form with fuel limit -/
def etaReduce (fuel : Nat) (t : Term) : Term :=
  match fuel with
  | 0 => t
  | fuel' + 1 =>
    match etaReduceStep t with
    | some t' => etaReduce fuel' t'
    | none => t

/-- Combined beta-eta reduction step (beta first, then eta) -/
def betaEtaReduceStep (t : Term) : Option Term :=
  match betaReduceStep t with
  | some t' => some t'
  | none => etaReduceStep t

/-- Reduce to beta-eta normal form -/
def betaEtaReduce (fuel : Nat) (t : Term) : Term :=
  match fuel with
  | 0 => t
  | fuel' + 1 =>
    match betaEtaReduceStep t with
    | some t' => betaEtaReduce fuel' t'
    | none => t

/-- Check if a term is in beta-eta normal form -/
def isBetaEtaNormalForm (t : Term) : Bool :=
  betaEtaReduceStep t == none

/-
  Call-by-Value Reduction

  In call-by-value, we only reduce (λx. body) arg when arg is a value.
  Values are: variables and lambda abstractions (not applications).
-/

/-- Check if a term is a value (for call-by-value semantics) -/
def isValue : Term -> Bool
  | var _ => true
  | lam _ => true
  | app _ _ => false

/-- Single step call-by-value reduction -/
def cbvReduceStep : Term -> Option Term
  | app (lam body) arg =>
    if isValue arg then
      some (subst 0 arg body)  -- Only reduce if arg is a value
    else
      match cbvReduceStep arg with
      | some arg' => some (app (lam body) arg')
      | none => none
  | app t1 t2 =>
    match cbvReduceStep t1 with
    | some t1' => some (app t1' t2)
    | none =>
      match cbvReduceStep t2 with
      | some t2' => some (app t1 t2')
      | none => none
  | lam _ => none  -- Don't reduce under lambdas in CBV
  | var _ => none

/-- Reduce to value using call-by-value with fuel limit -/
def cbvReduce (fuel : Nat) (t : Term) : Term :=
  match fuel with
  | 0 => t
  | fuel' + 1 =>
    match cbvReduceStep t with
    | some t' => cbvReduce fuel' t'
    | none => t

/-- Eta reduce and return trace -/
def etaReduceWithTrace (fuel : Nat) (t : Term) : List Term :=
  match fuel with
  | 0 => [t]
  | fuel' + 1 =>
    match etaReduceStep t with
    | some t' => t :: etaReduceWithTrace fuel' t'
    | none => [t]

/-
  Named Lambda Terms

  For convenience, we also provide a named representation that can be
  converted to de Bruijn terms.
-/

/-- Lambda terms with named variables -/
inductive NamedTerm where
  | var : String -> NamedTerm
  | lam : String -> NamedTerm -> NamedTerm
  | app : NamedTerm -> NamedTerm -> NamedTerm
  deriving Repr, BEq

open NamedTerm

/-- Find the index of an element in a list -/
def List.findIndex? [BEq a] (x : a) : List a -> Option Nat
  | [] => none
  | y :: ys => if x == y then some 0 else (findIndex? x ys).map (· + 1)

/-- Pretty print a named lambda term -/
def NamedTerm.toString : NamedTerm -> String
  | NamedTerm.var x => x
  | NamedTerm.lam x body => s!"(\\{x}. {body.toString})"
  | NamedTerm.app t1 t2 => s!"({t1.toString} {t2.toString})"

instance : ToString NamedTerm where
  toString := NamedTerm.toString

/-- Convert a named term to a de Bruijn term -/
def toDeBruijn (ctx : List String) : NamedTerm -> Term
  | NamedTerm.var x =>
    match List.findIndex? x ctx with
    | some i => Term.var i
    | none => Term.var 999  -- Free variable (use high index)
  | NamedTerm.lam x body =>
    Term.lam (toDeBruijn (x :: ctx) body)
  | NamedTerm.app t1 t2 =>
    Term.app (toDeBruijn ctx t1) (toDeBruijn ctx t2)

/-- Convert named term to de Bruijn with empty context -/
def compile (t : NamedTerm) : Term := toDeBruijn [] t

/-
  Church Encodings - Booleans
-/

-- Church booleans
def churchTrue : Term := lam (lam (var 1))   -- λx. λy. x
def churchFalse : Term := lam (lam (var 0))  -- λx. λy. y

-- Church if-then-else: λb. λt. λe. b t e
def churchIf : Term :=
  lam (lam (lam (app (app (var 2) (var 1)) (var 0))))

-- Church and: λa. λb. a b false
def churchAnd : Term :=
  lam (lam (app (app (var 1) (var 0)) churchFalse))

-- Church or: λa. λb. a true b
def churchOr : Term :=
  lam (lam (app (app (var 1) churchTrue) (var 0)))

-- Church not: λb. b false true
def churchNot : Term :=
  lam (app (app (var 0) churchFalse) churchTrue)

/-
  Church Encodings - Numerals and Arithmetic
-/

-- Church numerals
def churchZero : Term := lam (lam (var 0))   -- λf. λx. x
def churchOne : Term := lam (lam (app (var 1) (var 0)))  -- λf. λx. f x
def churchTwo : Term := lam (lam (app (var 1) (app (var 1) (var 0))))  -- λf. λx. f (f x)
def churchThree : Term := lam (lam (app (var 1) (app (var 1) (app (var 1) (var 0)))))
def churchFour : Term := lam (lam (app (var 1) (app (var 1) (app (var 1) (app (var 1) (var 0))))))
def churchFive : Term := lam (lam (app (var 1) (app (var 1) (app (var 1) (app (var 1) (app (var 1) (var 0)))))))

/-- Build a Church numeral from a natural number -/
def churchNum (n : Nat) : Term :=
  lam (lam (applyN n (var 1) (var 0)))
where
  applyN : Nat -> Term -> Term -> Term
    | 0, _, x => x
    | n + 1, f, x => app f (applyN n f x)

-- Church successor: λn. λf. λx. f (n f x)
def churchSucc : Term :=
  lam (lam (lam (app (var 1) (app (app (var 2) (var 1)) (var 0)))))

-- Church addition: λm. λn. λf. λx. m f (n f x)
def churchAdd : Term :=
  lam (lam (lam (lam (app (app (var 3) (var 1)) (app (app (var 2) (var 1)) (var 0))))))

-- Church multiplication: λm. λn. λf. m (n f)
def churchMult : Term :=
  lam (lam (lam (app (var 2) (app (var 1) (var 0)))))

-- Church exponentiation: λm. λn. n m
-- Computes m^n (n copies of m composed)
def churchExp : Term :=
  lam (lam (app (var 0) (var 1)))

-- Church isZero: λn. n (λx. false) true
-- Returns true if n is zero, false otherwise
def churchIsZero : Term :=
  lam (app (app (var 0) (lam churchFalse)) churchTrue)

/-
  Church Predecessor and Subtraction

  These are the classic tricky encodings using pairs.
  pred n = π₂(n (λp. (succ (π₁ p), π₁ p)) (0, 0))
-/

-- Church pair: λa. λb. λf. f a b
def churchPair : Term :=
  lam (lam (lam (app (app (var 0) (var 2)) (var 1))))

-- Church first: λp. p (λa. λb. a)
def churchFst : Term :=
  lam (app (var 0) churchTrue)

-- Church second: λp. p (λa. λb. b)
def churchSnd : Term :=
  lam (app (var 0) churchFalse)

-- Helper for predecessor: λp. pair (succ (fst p)) (fst p)
-- This creates (n+1, n) from (n, n-1)
def predHelper : Term :=
  lam (app (app churchPair
    (app churchSucc (app churchFst (var 0))))
    (app churchFst (var 0)))

-- Church predecessor: λn. snd (n predHelper (pair 0 0))
-- pred(0) = 0, pred(n+1) = n
def churchPred : Term :=
  lam (app churchSnd
    (app (app (var 0) predHelper)
      (app (app churchPair churchZero) churchZero)))

-- Church subtraction: λm. λn. n pred m
-- sub m n = m - n (saturating at 0)
def churchSub : Term :=
  lam (lam (app (app (var 0) churchPred) (var 1)))

-- Church less-than-or-equal: λm. λn. isZero (sub m n)
def churchLeq : Term :=
  lam (lam (app churchIsZero (app (app churchSub (var 1)) (var 0))))

-- Church equal: λm. λn. and (leq m n) (leq n m)
def churchEq : Term :=
  lam (lam (app (app churchAnd
    (app (app churchLeq (var 1)) (var 0)))
    (app (app churchLeq (var 0)) (var 1))))

-- Church greater-than: λm. λn. not (leq m n)
def churchGt : Term :=
  lam (lam (app churchNot (app (app churchLeq (var 1)) (var 0))))

-- Church min: λm. λn. if (leq m n) then m else n
def churchMin : Term :=
  lam (lam (app (app (app churchIf
    (app (app churchLeq (var 1)) (var 0)))
    (var 1))
    (var 0)))

-- Church max: λm. λn. if (leq m n) then n else m
def churchMax : Term :=
  lam (lam (app (app (app churchIf
    (app (app churchLeq (var 1)) (var 0)))
    (var 0))
    (var 1)))

/-
  Combinators
-/

-- Identity combinator: λx. x
def idCombinator : Term := lam (var 0)

-- K combinator: λx. λy. x
def kCombinator : Term := lam (lam (var 1))

-- S combinator: λx. λy. λz. x z (y z)
def sCombinator : Term :=
  lam (lam (lam (app (app (var 2) (var 0)) (app (var 1) (var 0)))))

-- Omega combinator (self-application): λx. x x
def omega : Term := lam (app (var 0) (var 0))

-- Big Omega (diverges): (λx. x x) (λx. x x)
def bigOmega : Term := app omega omega

-- B combinator (composition): λf. λg. λx. f (g x)
def bCombinator : Term :=
  lam (lam (lam (app (var 2) (app (var 1) (var 0)))))

-- C combinator (flip): λf. λx. λy. f y x
def cCombinator : Term :=
  lam (lam (lam (app (app (var 2) (var 0)) (var 1))))

-- W combinator (duplicate): λf. λx. f x x
def wCombinator : Term :=
  lam (lam (app (app (var 1) (var 0)) (var 0)))

/-
  Fixed-Point Combinators for Recursion
-/

-- Y combinator (call-by-name fixed-point): λf. (λx. f (x x)) (λx. f (x x))
-- Y f = f (Y f)
def yCombinator : Term :=
  lam (app
    (lam (app (var 1) (app (var 0) (var 0))))
    (lam (app (var 1) (app (var 0) (var 0)))))

-- Z combinator (call-by-value fixed-point): λf. (λx. f (λv. x x v)) (λx. f (λv. x x v))
-- Also known as the "applicative order" Y combinator
-- Delays the self-application to work with strict evaluation
def zCombinator : Term :=
  lam (app
    (lam (app (var 1) (lam (app (app (var 1) (var 1)) (var 0)))))
    (lam (app (var 1) (lam (app (app (var 1) (var 1)) (var 0))))))

-- Theta combinator (Turing's fixed-point): (λx. λf. f (x x f)) (λx. λf. f (x x f))
def thetaCombinator : Term :=
  let theta := lam (lam (app (var 0) (app (app (var 1) (var 1)) (var 0))))
  app theta theta

/-
  Recursive Function Examples Using Y Combinator

  These demonstrate how to define recursive functions in pure lambda calculus.
  The pattern is: Y (λself. λargs. body-using-self)
-/

/-- Factorial function body: λself. λn. if (isZero n) then 1 else n * self(n-1)
    When applied to Y, gives factorial -/
def factBody : Term :=
  lam (lam (  -- λself. λn.
    app (app (app churchIf
      (app churchIsZero (var 0)))        -- if isZero n
      churchOne)                          -- then 1
      (app (app churchMult (var 0))       -- else n *
        (app (var 1)                      -- self
          (app churchPred (var 0))))))    -- (pred n)

/-- Factorial using Y combinator -/
def churchFactorial : Term := app yCombinator factBody

/-- Sum function: sum(n) = 0 + 1 + 2 + ... + n
    Body: λself. λn. if (isZero n) then 0 else n + self(n-1) -/
def sumBody : Term :=
  lam (lam (  -- λself. λn.
    app (app (app churchIf
      (app churchIsZero (var 0)))        -- if isZero n
      churchZero)                         -- then 0
      (app (app churchAdd (var 0))        -- else n +
        (app (var 1)                      -- self
          (app churchPred (var 0))))))    -- (pred n)

/-- Sum of 0 to n using Y combinator -/
def churchSum : Term := app yCombinator sumBody

/-- Fibonacci body: λself. λn. if n <= 1 then n else self(n-1) + self(n-2) -/
def fibBody : Term :=
  lam (lam (  -- λself. λn.
    app (app (app churchIf
      (app (app churchLeq (var 0)) churchOne))  -- if n <= 1
      (var 0))                                   -- then n
      (app (app churchAdd                        -- else
        (app (var 1) (app churchPred (var 0))))  -- self(n-1) +
        (app (var 1) (app churchPred (app churchPred (var 0))))))) -- self(n-2)

/-- Fibonacci using Y combinator -/
def churchFib : Term := app yCombinator fibBody

/-- Power function body: λself. λb. λe. if (isZero e) then 1 else b * self b (e-1)
    Computes b^e -/
def powerBody : Term :=
  lam (lam (lam (  -- λself. λb. λe.
    app (app (app churchIf
      (app churchIsZero (var 0)))        -- if isZero e
      churchOne)                          -- then 1
      (app (app churchMult (var 1))       -- else b *
        (app (app (var 2) (var 1))        -- self b
          (app churchPred (var 0)))))))   -- (pred e)

/-- Power function using Y combinator -/
def churchPower : Term := app yCombinator powerBody

/-
  List Encodings (Scott encoding)

  Scott-encoded lists:
  nil  = λn. λc. n
  cons = λh. λt. λn. λc. c h t
-/

-- Scott-encoded nil
def scottNil : Term := lam (lam (var 1))

-- Scott-encoded cons: λh. λt. λn. λc. c h t
def scottCons : Term :=
  lam (lam (lam (lam (app (app (var 0) (var 3)) (var 2)))))

-- isNil: λl. l true (λh. λt. false)
def scottIsNil : Term :=
  lam (app (app (var 0) churchTrue) (lam (lam churchFalse)))

-- head: λl. l error (λh. λt. h)  (we use 0 as error/default)
def scottHead : Term :=
  lam (app (app (var 0) churchZero) (lam (lam (var 1))))

-- tail: λl. l nil (λh. λt. t)
def scottTail : Term :=
  lam (app (app (var 0) scottNil) (lam (lam (var 0))))

-- length: Y (λf. λl. l 0 (λh. λt. succ (f t)))
def scottLength : Term :=
  app yCombinator
    (lam (lam (app (app (var 0) churchZero)
      (lam (lam (app churchSucc (app (var 3) (var 0))))))))

-- append: Y (λf. λl1. λl2. l1 l2 (λh. λt. cons h (f t l2)))
def scottAppend : Term :=
  app yCombinator
    (lam (lam (lam (app (app (var 1) (var 0))
      (lam (lam (app (app scottCons (var 1))
        (app (app (var 4) (var 0)) (var 2)))))))))

-- map: Y (λf. λg. λl. l nil (λh. λt. cons (g h) (f g t)))
def scottMap : Term :=
  app yCombinator
    (lam (lam (lam (app (app (var 0) scottNil)
      (lam (lam (app (app scottCons (app (var 3) (var 1)))
        (app (app (var 4) (var 3)) (var 0)))))))))

-- foldr: Y (λf. λg. λz. λl. l z (λh. λt. g h (f g z t)))
def scottFoldr : Term :=
  app yCombinator
    (lam (lam (lam (lam (app (app (var 0) (var 1))
      (lam (lam (app (app (var 4) (var 1))
        (app (app (app (var 5) (var 4)) (var 3)) (var 0))))))))))

-- reverse: Y (λf. λacc. λl. l acc (λh. λt. f (cons h acc) t))
def scottReverse : Term :=
  app yCombinator
    (lam (lam (lam (app (app (var 0) (var 1))
      (lam (lam (app (app (var 4) (app (app scottCons (var 1)) (var 3))) (var 0))))))))

-- sum: foldr add 0 l
def scottSum : Term :=
  lam (app (app (app scottFoldr churchAdd) churchZero) (var 0))

-- product: foldr mul 1 l
def scottProduct : Term :=
  lam (app (app (app scottFoldr churchMult) churchOne) (var 0))

-- nth: get element at index n (0-based)
-- Y (λf. λn. λl. l 0 (λh. λt. (zero? n) h (f (pred n) t)))
def scottNth : Term :=
  app yCombinator
    (lam (lam (lam (app (app (var 0) churchZero)
      (lam (lam (app (app (app churchIsZero (var 3)) (var 1))
        (app (app (var 4) (app churchPred (var 3))) (var 0)))))))))

/-
  SKI Combinator Translation

  Convert lambda terms to SKI combinator terms using bracket abstraction.
  This is the classic translation from lambda calculus to combinatory logic.

  Rules:
  - [x] x = I
  - [x] N = K N  (when x not free in N)
  - [x] (M N) = S ([x] M) ([x] N)
-/

/-- Check if variable n is free in term (for SKI translation) -/
def freeInSKI (n : Nat) : Term -> Bool
  | Term.var m => m == n
  | Term.lam body => freeInSKI (n + 1) body
  | Term.app t1 t2 => freeInSKI n t1 || freeInSKI n t2

/-- Adjust variable indices after removing a binder (for SKI translation) -/
def adjustVarsSKI (depth : Nat) : Term -> Term
  | Term.var n => if n > depth then var (n - 1) else var n
  | Term.lam body => lam (adjustVarsSKI (depth + 1) body)
  | Term.app t1 t2 => app (adjustVarsSKI depth t1) (adjustVarsSKI depth t2)

/-- Eliminate a single variable binding, producing an SKI term -/
partial def eliminateSKI (depth : Nat) : Term -> Term
  | Term.var n =>
    if n == depth then idCombinator
    else if n > depth then app kCombinator (var (n - 1))
    else app kCombinator (var n)
  | Term.lam body =>
    -- First eliminate inner lambda, then the outer variable
    let inner := eliminateSKI (depth + 1) body
    eliminateSKI depth (lam inner)
  | Term.app t1 t2 =>
    if !freeInSKI depth (app t1 t2) then
      app kCombinator (app (adjustVarsSKI depth t1) (adjustVarsSKI depth t2))
    else
      app (app sCombinator (eliminateSKI depth t1)) (eliminateSKI depth t2)

/-- Bracket abstraction: eliminate the outermost lambda using SKI combinators -/
def bracketAbstract : Term -> Term
  | Term.lam body => eliminateSKI 0 body
  | t => t

/-- Convert a lambda term to SKI combinators -/
partial def toSKI : Term -> Term
  | Term.var n => var n
  | Term.lam body => bracketAbstract (lam (toSKI body))
  | Term.app t1 t2 => app (toSKI t1) (toSKI t2)

/-
  Utility functions for testing
-/

/-- Convert a Church numeral to a natural number (by reducing and counting) -/
def churchToNat (t : Term) : Option Nat :=
  let reduced := reduce 1000 t
  countApps reduced
where
  countApps : Term -> Option Nat
    | Term.lam (Term.lam inner) => countInner 0 inner
    | _ => none
  countInner (acc : Nat) : Term -> Option Nat
    | Term.var 0 => some acc
    | Term.app (Term.var 1) rest => countInner (acc + 1) rest
    | _ => none

/-- Build a list of Church numerals -/
def churchList (ns : List Nat) : Term :=
  ns.foldr (fun n acc => app (app scottCons (churchNum n)) acc) scottNil

end LambdaCalc
