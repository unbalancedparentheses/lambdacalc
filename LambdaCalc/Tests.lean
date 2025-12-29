/-
  Lambda Calculus Tests and Theorems

  This module contains formal verification of properties about the
  lambda calculus implementation using Lean 4's theorem proving.
-/

import LambdaCalc.Basic

namespace LambdaCalc

open Term

/-!
## Basic Evaluation Tests
-/

-- Test identity combinator
#eval idCombinator  -- Expected: (λ. x0)

-- Test that (λx. x) y reduces to y
#eval reduce 10 (app idCombinator (var 5))  -- Expected: x5

/-!
## Church Numerals Tests
-/

#eval churchZero   -- λf. λx. x
#eval churchOne    -- λf. λx. f x
#eval churchTwo    -- λf. λx. f (f x)
#eval churchThree  -- λf. λx. f (f (f x))
#eval churchFour   -- λf. λx. f (f (f (f x)))
#eval churchFive   -- λf. λx. f (f (f (f (f x))))

-- Verify churchNum generates correct numerals
theorem churchNum_three_eq : churchNum 3 = churchThree := rfl
theorem churchNum_four_eq : churchNum 4 = churchFour := rfl
theorem churchNum_five_eq : churchNum 5 = churchFive := rfl

/-!
## Successor Tests
-/

#eval reduce 100 (app churchSucc churchZero)   -- Should equal churchOne
#eval reduce 100 (app churchSucc churchOne)    -- Should equal churchTwo
#eval reduce 100 (app churchSucc churchTwo)    -- Should equal churchThree

theorem succ_zero_is_one : reduce 100 (app churchSucc churchZero) = churchOne := rfl
theorem succ_one_is_two : reduce 100 (app churchSucc churchOne) = churchTwo := rfl
theorem succ_two_is_three : reduce 100 (app churchSucc churchTwo) = churchThree := rfl
theorem succ_three_is_four : reduce 100 (app churchSucc churchThree) = churchFour := rfl

/-!
## Addition Tests
-/

#eval reduce 100 (app (app churchAdd churchOne) churchOne)    -- 1 + 1 = 2
#eval reduce 100 (app (app churchAdd churchTwo) churchOne)    -- 2 + 1 = 3
#eval reduce 100 (app (app churchAdd churchTwo) churchTwo)    -- 2 + 2 = 4

theorem one_plus_one : reduce 100 (app (app churchAdd churchOne) churchOne) = churchTwo := rfl
theorem one_plus_zero : reduce 100 (app (app churchAdd churchOne) churchZero) = churchOne := rfl
theorem zero_plus_one : reduce 100 (app (app churchAdd churchZero) churchOne) = churchOne := rfl
theorem two_plus_one : reduce 100 (app (app churchAdd churchTwo) churchOne) = churchThree := rfl
theorem two_plus_two : reduce 100 (app (app churchAdd churchTwo) churchTwo) = churchFour := rfl
theorem one_plus_two : reduce 100 (app (app churchAdd churchOne) churchTwo) = churchThree := rfl
theorem zero_plus_zero : reduce 100 (app (app churchAdd churchZero) churchZero) = churchZero := rfl

/-!
## Multiplication Tests
-/

#eval reduce 100 (app (app churchMult churchTwo) churchTwo)    -- 2 * 2 = 4
#eval reduce 100 (app (app churchMult churchTwo) churchThree)  -- 2 * 3 = 6

theorem two_times_one : reduce 100 (app (app churchMult churchTwo) churchOne) = churchTwo := rfl
theorem one_times_two : reduce 100 (app (app churchMult churchOne) churchTwo) = churchTwo := rfl
theorem two_times_two : reduce 100 (app (app churchMult churchTwo) churchTwo) = churchFour := rfl
theorem three_times_one : reduce 100 (app (app churchMult churchThree) churchOne) = churchThree := rfl
theorem one_times_three : reduce 100 (app (app churchMult churchOne) churchThree) = churchThree := rfl
theorem zero_times_any : reduce 100 (app (app churchMult churchZero) churchFive) = churchZero := rfl
theorem any_times_zero : reduce 100 (app (app churchMult churchFive) churchZero) = churchZero := rfl

/-!
## Exponentiation Tests
-/

#eval reduce 100 (app (app churchExp churchTwo) churchTwo)    -- 2^2 = 4
#eval reduce 100 (app (app churchExp churchTwo) churchThree)  -- 2^3 = 8

-- Note: n^0 returns λx.x (identity), which is eta-equivalent to churchOne but not structurally equal
-- So we test the actual result
theorem two_exp_zero : reduce 100 (app (app churchExp churchTwo) churchZero) = lam (var 0) := rfl
theorem two_exp_one : reduce 100 (app (app churchExp churchTwo) churchOne) = churchTwo := rfl
theorem two_exp_two : reduce 100 (app (app churchExp churchTwo) churchTwo) = churchFour := rfl
theorem three_exp_one : reduce 100 (app (app churchExp churchThree) churchOne) = churchThree := rfl
theorem one_exp_any : reduce 100 (app (app churchExp churchOne) churchFive) = churchOne := rfl

/-!
## isZero Tests
-/

#eval reduce 100 (app churchIsZero churchZero)  -- Should be true
#eval reduce 100 (app churchIsZero churchOne)   -- Should be false
#eval reduce 100 (app churchIsZero churchTwo)   -- Should be false

theorem isZero_zero : reduce 100 (app churchIsZero churchZero) = churchTrue := rfl
theorem isZero_one : reduce 100 (app churchIsZero churchOne) = churchFalse := rfl
theorem isZero_two : reduce 100 (app churchIsZero churchTwo) = churchFalse := rfl
theorem isZero_three : reduce 100 (app churchIsZero churchThree) = churchFalse := rfl

/-!
## Boolean Operation Tests
-/

-- AND tests
theorem and_true_true : reduce 100 (app (app churchAnd churchTrue) churchTrue) = churchTrue := rfl
theorem and_true_false : reduce 100 (app (app churchAnd churchTrue) churchFalse) = churchFalse := rfl
theorem and_false_true : reduce 100 (app (app churchAnd churchFalse) churchTrue) = churchFalse := rfl
theorem and_false_false : reduce 100 (app (app churchAnd churchFalse) churchFalse) = churchFalse := rfl

-- OR tests
theorem or_true_true : reduce 100 (app (app churchOr churchTrue) churchTrue) = churchTrue := rfl
theorem or_true_false : reduce 100 (app (app churchOr churchTrue) churchFalse) = churchTrue := rfl
theorem or_false_true : reduce 100 (app (app churchOr churchFalse) churchTrue) = churchTrue := rfl
theorem or_false_false : reduce 100 (app (app churchOr churchFalse) churchFalse) = churchFalse := rfl

-- NOT tests
theorem not_true : reduce 100 (app churchNot churchTrue) = churchFalse := rfl
theorem not_false : reduce 100 (app churchNot churchFalse) = churchTrue := rfl

-- Double negation
theorem not_not_true : reduce 100 (app churchNot (app churchNot churchTrue)) = churchTrue := rfl
theorem not_not_false : reduce 100 (app churchNot (app churchNot churchFalse)) = churchFalse := rfl

/-!
## If-Then-Else Tests
-/

theorem if_true_then_a_else_b :
    reduce 100 (app (app (app churchIf churchTrue) (var 1)) (var 2)) = var 1 := rfl

theorem if_false_then_a_else_b :
    reduce 100 (app (app (app churchIf churchFalse) (var 1)) (var 2)) = var 2 := rfl

/-!
## Pair Tests
-/

-- Create a pair and extract elements
#eval reduce 100 (app churchFst (app (app churchPair (var 1)) (var 2)))  -- Should be var 1
#eval reduce 100 (app churchSnd (app (app churchPair (var 1)) (var 2)))  -- Should be var 2

theorem pair_fst : reduce 100 (app churchFst (app (app churchPair (var 1)) (var 2))) = var 1 := rfl
theorem pair_snd : reduce 100 (app churchSnd (app (app churchPair (var 1)) (var 2))) = var 2 := rfl

-- Pairs with Church numerals
theorem pair_num_fst :
    reduce 100 (app churchFst (app (app churchPair churchOne) churchTwo)) = churchOne := rfl
theorem pair_num_snd :
    reduce 100 (app churchSnd (app (app churchPair churchOne) churchTwo)) = churchTwo := rfl

/-!
## Predecessor Tests
-/

#eval reduce 500 (app churchPred churchOne)    -- Should be 0
#eval reduce 500 (app churchPred churchTwo)    -- Should be 1
#eval reduce 500 (app churchPred churchThree)  -- Should be 2

theorem pred_zero : reduce 500 (app churchPred churchZero) = churchZero := rfl
theorem pred_one : reduce 500 (app churchPred churchOne) = churchZero := rfl
theorem pred_two : reduce 500 (app churchPred churchTwo) = churchOne := rfl
theorem pred_three : reduce 500 (app churchPred churchThree) = churchTwo := rfl

/-!
## Subtraction Tests
-/

#eval reduce 1000 (app (app churchSub churchTwo) churchOne)   -- 2 - 1 = 1
#eval reduce 1000 (app (app churchSub churchThree) churchOne) -- 3 - 1 = 2

theorem sub_one_zero : reduce 1000 (app (app churchSub churchOne) churchZero) = churchOne := rfl
theorem sub_two_one : reduce 1000 (app (app churchSub churchTwo) churchOne) = churchOne := rfl
theorem sub_three_one : reduce 1000 (app (app churchSub churchThree) churchOne) = churchTwo := rfl
theorem sub_three_two : reduce 1000 (app (app churchSub churchThree) churchTwo) = churchOne := rfl
-- Saturating subtraction: 1 - 2 = 0
theorem sub_one_two : reduce 1000 (app (app churchSub churchOne) churchTwo) = churchZero := rfl
theorem sub_zero_one : reduce 1000 (app (app churchSub churchZero) churchOne) = churchZero := rfl

/-!
## Comparison Tests
-/

-- Less than or equal
theorem leq_zero_zero : reduce 1000 (app (app churchLeq churchZero) churchZero) = churchTrue := rfl
theorem leq_zero_one : reduce 1000 (app (app churchLeq churchZero) churchOne) = churchTrue := rfl
theorem leq_one_one : reduce 1000 (app (app churchLeq churchOne) churchOne) = churchTrue := rfl
theorem leq_one_two : reduce 1000 (app (app churchLeq churchOne) churchTwo) = churchTrue := rfl
theorem leq_two_one : reduce 1000 (app (app churchLeq churchTwo) churchOne) = churchFalse := rfl
theorem leq_three_one : reduce 1000 (app (app churchLeq churchThree) churchOne) = churchFalse := rfl

-- Equality
theorem eq_zero_zero : reduce 1500 (app (app churchEq churchZero) churchZero) = churchTrue := rfl
theorem eq_one_one : reduce 1500 (app (app churchEq churchOne) churchOne) = churchTrue := rfl
theorem eq_zero_one : reduce 1500 (app (app churchEq churchZero) churchOne) = churchFalse := rfl
theorem eq_one_zero : reduce 1500 (app (app churchEq churchOne) churchZero) = churchFalse := rfl
theorem eq_two_two : reduce 1500 (app (app churchEq churchTwo) churchTwo) = churchTrue := rfl

-- Greater than
theorem gt_one_zero : reduce 1000 (app (app churchGt churchOne) churchZero) = churchTrue := rfl
theorem gt_two_one : reduce 1000 (app (app churchGt churchTwo) churchOne) = churchTrue := rfl
theorem gt_zero_zero : reduce 1000 (app (app churchGt churchZero) churchZero) = churchFalse := rfl
theorem gt_one_one : reduce 1000 (app (app churchGt churchOne) churchOne) = churchFalse := rfl
theorem gt_zero_one : reduce 1000 (app (app churchGt churchZero) churchOne) = churchFalse := rfl

/-!
## Combinator Tests
-/

-- Identity is in normal form
theorem id_is_normal : isNormalForm idCombinator = true := rfl
theorem k_is_normal : isNormalForm kCombinator = true := rfl
theorem s_is_normal : isNormalForm sCombinator = true := rfl

-- Reduction of identity applied to variable produces the variable
theorem id_reduces_to_arg : reduce 10 (app idCombinator (var n)) = var n := rfl

-- K combinator applied to two arguments returns first
theorem k_reduces : reduce 10 (app (app kCombinator (var 1)) (var 2)) = var 1 := rfl

-- S K K = I (combinator identity)
theorem skk_is_identity :
    reduce 100 (app (app (app sCombinator kCombinator) kCombinator) (var 99)) = var 99 := rfl

-- B combinator (composition): B f g x = f (g x)
theorem b_combinator_composition :
    reduce 100 (app (app (app bCombinator (var 10)) (var 20)) (var 30)) =
    app (var 10) (app (var 20) (var 30)) := rfl

-- C combinator (flip): C f x y = f y x
theorem c_combinator_flip :
    reduce 100 (app (app (app cCombinator (var 10)) (var 20)) (var 30)) =
    app (app (var 10) (var 30)) (var 20) := rfl

-- W combinator (duplicate): W f x = f x x
theorem w_combinator_duplicate :
    reduce 100 (app (app wCombinator (var 10)) (var 20)) =
    app (app (var 10) (var 20)) (var 20) := rfl

/-!
## Named Term Compilation Tests
-/

theorem compile_id :
    compile (NamedTerm.lam "x" (NamedTerm.var "x")) = idCombinator := rfl

theorem compile_k :
    compile (NamedTerm.lam "x" (NamedTerm.lam "y" (NamedTerm.var "x"))) = kCombinator := rfl

theorem compile_s :
    compile (NamedTerm.lam "x" (NamedTerm.lam "y" (NamedTerm.lam "z"
      (NamedTerm.app (NamedTerm.app (NamedTerm.var "x") (NamedTerm.var "z"))
                     (NamedTerm.app (NamedTerm.var "y") (NamedTerm.var "z")))))) = sCombinator := rfl

/-!
## Closed Term Tests
-/

theorem id_is_closed : isClosed idCombinator = true := rfl
theorem k_is_closed : isClosed kCombinator = true := rfl
theorem s_is_closed : isClosed sCombinator = true := rfl
theorem churchTrue_is_closed : isClosed churchTrue = true := rfl
theorem churchFalse_is_closed : isClosed churchFalse = true := rfl
theorem churchZero_is_closed : isClosed churchZero = true := rfl
theorem churchOne_is_closed : isClosed churchOne = true := rfl

-- Open terms
theorem var_is_open : isClosed (var 0) = false := rfl
theorem open_app_is_open : isClosed (app (var 0) (var 1)) = false := rfl

/-!
## Free Variable Tests
-/

theorem var_has_free_var : hasFreeVar 0 (var 0) = true := rfl
theorem var_no_free_var : hasFreeVar 1 (var 0) = false := rfl
theorem lam_binds_var : hasFreeVar 0 (lam (var 0)) = false := rfl
theorem lam_free_var_shifts : hasFreeVar 0 (lam (var 1)) = true := rfl

-- Free variables list
theorem var_free_vars : freeVars (var 0) = [0] := rfl
theorem id_free_vars : freeVars idCombinator = [] := rfl

/-!
## Shifting Tests
-/

example : shift 1 0 (var 0) = var 1 := rfl
example : shift 1 1 (var 0) = var 0 := rfl  -- below cutoff
example : shift 1 0 (lam (var 0)) = lam (var 0) := rfl  -- bound to inner lambda
example : shift 2 0 (var 0) = var 2 := rfl
example : shift 1 0 (var 5) = var 6 := rfl

/-!
## Substitution Tests
-/

example : subst 0 (var 5) (var 0) = var 5 := rfl
example : subst 0 (var 5) (var 1) = var 0 := rfl  -- x1 becomes x0 after removing binder
example : subst 1 (var 5) (var 0) = var 0 := rfl  -- x0 unchanged when substituting for x1
example : subst 1 (var 5) (var 1) = var 5 := rfl  -- x1 replaced by x5

/-!
## Scott-Encoded List Tests
-/

-- isNil tests
theorem isNil_nil : reduce 100 (app scottIsNil scottNil) = churchTrue := rfl
theorem isNil_cons : reduce 100 (app scottIsNil (app (app scottCons churchOne) scottNil)) = churchFalse := rfl

-- head tests
theorem head_singleton :
    reduce 100 (app scottHead (app (app scottCons churchOne) scottNil)) = churchOne := rfl
theorem head_list :
    reduce 100 (app scottHead (app (app scottCons churchTwo) (app (app scottCons churchOne) scottNil))) = churchTwo := rfl

-- tail tests
theorem tail_singleton :
    reduce 100 (app scottTail (app (app scottCons churchOne) scottNil)) = scottNil := rfl

/-!
## Eta Reduction Tests
-/

-- λx. f x should eta-reduce to f (when x not free in f)
-- In de Bruijn: lam (app (var 1) (var 0)) -> var 0
theorem eta_basic : etaReduce 10 (lam (app (var 1) (var 0))) = var 0 := rfl

-- No eta reduction when the variable is used elsewhere
theorem no_eta_when_var_used : etaReduce 10 (lam (app (var 0) (var 0))) = lam (app (var 0) (var 0)) := rfl

-- isEtaNormalForm tests
theorem id_not_eta_normal : isEtaNormalForm (lam (app (var 1) (var 0))) = false := rfl
theorem omega_is_eta_normal : isEtaNormalForm omega = true := rfl

/-!
## Reduction Trace Tests
-/

#eval reduceWithTrace 10 (app (app kCombinator (var 1)) (var 2))

-- Verify trace length is reasonable
theorem trace_k_reduction :
    (reduceWithTrace 10 (app (app kCombinator (var 1)) (var 2))).length = 3 := rfl

/-!
## Alpha Equivalence Tests
-/

theorem alpha_refl_var : alphaEquiv (var 0) (var 0) = true := rfl
theorem alpha_refl_lam : alphaEquiv idCombinator idCombinator = true := rfl
theorem alpha_diff_var : alphaEquiv (var 0) (var 1) = false := rfl
theorem alpha_diff_term : alphaEquiv idCombinator kCombinator = false := rfl

/-!
## Normal Form Tests
-/

-- Church numerals are in normal form
theorem zero_is_normal : isNormalForm churchZero = true := rfl
theorem one_is_normal : isNormalForm churchOne = true := rfl
theorem two_is_normal : isNormalForm churchTwo = true := rfl

-- Church booleans are in normal form
theorem true_is_normal : isNormalForm churchTrue = true := rfl
theorem false_is_normal : isNormalForm churchFalse = true := rfl

-- Redexes are not in normal form
theorem redex_not_normal : isNormalForm (app idCombinator (var 0)) = false := rfl
theorem nested_redex_not_normal : isNormalForm (app (app kCombinator (var 0)) (var 1)) = false := rfl

/-!
## Beta-Eta Reduction Tests
-/

-- Beta-eta reduces both beta redexes and eta redexes
theorem beta_eta_reduces_beta :
    betaEtaReduce 100 (app idCombinator (var 5)) = var 5 := rfl

theorem beta_eta_reduces_eta :
    betaEtaReduce 100 (lam (app (var 1) (var 0))) = var 0 := rfl

/-!
## Variable Occurrence Count Tests
-/

theorem count_var : countVarOccurrences (var 0) = 1 := rfl
theorem count_lam : countVarOccurrences (lam (var 0)) = 1 := rfl
theorem count_app : countVarOccurrences (app (var 0) (var 1)) = 2 := rfl
theorem count_omega : countVarOccurrences omega = 2 := rfl
theorem count_k : countVarOccurrences kCombinator = 1 := rfl
theorem count_s : countVarOccurrences sCombinator = 4 := rfl

/-!
## churchToNat Utility Tests
-/

#eval churchToNat churchZero   -- Should be some 0
#eval churchToNat churchOne    -- Should be some 1
#eval churchToNat churchTwo    -- Should be some 2
#eval churchToNat churchThree  -- Should be some 3
#eval churchToNat churchFour   -- Should be some 4
#eval churchToNat churchFive   -- Should be some 5

theorem toNat_zero : churchToNat churchZero = some 0 := rfl
theorem toNat_one : churchToNat churchOne = some 1 := rfl
theorem toNat_two : churchToNat churchTwo = some 2 := rfl
theorem toNat_three : churchToNat churchThree = some 3 := rfl
theorem toNat_four : churchToNat churchFour = some 4 := rfl
theorem toNat_five : churchToNat churchFive = some 5 := rfl

-- Test with computed values
theorem toNat_succ_zero : churchToNat (reduce 100 (app churchSucc churchZero)) = some 1 := rfl
theorem toNat_one_plus_one : churchToNat (reduce 100 (app (app churchAdd churchOne) churchOne)) = some 2 := rfl
theorem toNat_two_times_two : churchToNat (reduce 100 (app (app churchMult churchTwo) churchTwo)) = some 4 := rfl

end LambdaCalc
