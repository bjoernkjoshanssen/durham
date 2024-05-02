/-
Copyright (c) 2023 Quinn Culver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quinn Culver
-/

import Mathlib
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

variable {i : ℝ}

structure CashFlow :=
  time : ℝ
  amount : ℝ
  t_nonneg : 0 ≤ time

inductive CashFlowSequence where
| empty : CashFlowSequence
| cons : CashFlow → CashFlowSequence → CashFlowSequence

variable (cfs : CashFlowSequence)

noncomputable def presentValue  (i: ℝ) (cfs : CashFlowSequence) : ℝ :=
match cfs with
| CashFlowSequence.empty => 0
| CashFlowSequence.cons cf cfs => cf.amount / (1+i) ^ cf.time + presentValue i cfs

/-simple cash flow sequence for testing-/
def simpleCashFlowSequence : CashFlowSequence :=
      CashFlowSequence.cons {time := 1, amount := 100, t_nonneg := by norm_num}
      CashFlowSequence.empty

#norm_num [presentValue] (presentValue (0.1) simpleCashFlowSequence )

def cashflowExample22 : CashFlowSequence :=
  CashFlowSequence.cons { time := 1, amount := 1000, t_nonneg := by norm_num }
    (CashFlowSequence.cons { time := 2, amount := 1000, t_nonneg := by norm_num }
      (CashFlowSequence.cons { time := 3, amount := 1000, t_nonneg := by norm_num }
        (CashFlowSequence.cons { time := 4, amount := 1000, t_nonneg := by norm_num }
          (CashFlowSequence.cons { time := 5, amount := 1000, t_nonneg := by norm_num }
            (CashFlowSequence.cons { time := 6, amount := 1000, t_nonneg := by norm_num }
              (CashFlowSequence.cons { time := 7, amount := 1000, t_nonneg := by norm_num }
                (CashFlowSequence.cons { time := 8, amount := 1000, t_nonneg := by norm_num }
                  (CashFlowSequence.cons { time := 9, amount := 1000, t_nonneg := by norm_num }
                    (CashFlowSequence.cons { time := 10, amount := 1000, t_nonneg := by norm_num }
                      CashFlowSequence.empty)))))))))

#norm_num [presentValue] (presentValue 0.07 cashflowExample22) -- returns 1381644796127950460700000 / 196715135728956532249 ≈ 7023.5815, as in equation (2.2)

noncomputable def presentValueDerivative  (i: ℝ) (cfs : CashFlowSequence) : ℝ :=
match cfs with
| CashFlowSequence.empty => 0
| CashFlowSequence.cons cf cfs => cf.amount*(-cf.time) / (1+i) ^ (cf.time+1) + presentValue i cfs

lemma deriv_presentValue (i : ℝ)cfs : deriv (λ (r : ℝ) => presentValue r cfs) i = (λ (r : ℝ) => (presentValueDerivative r cfs)) i := sorry


/-
noncomputable def presentValue (cf : cashFlowSequence) (i : ℝ) : ℝ :=
  cf.foldr (λ (c : Cashflow) (pv : ℝ) => pv + (c.amount) / ((1 + i) ^ (c.time))) 0

noncomputable def presentValueDerivative (cf : cashFlowSequence) (i : ℝ) : ℝ :=
  cf.foldr (λ (c : Cashflow) (pv : ℝ) => pv + (c.amount)*(-c.time) / ((1 + i) ^ (c.time+1))) 0

lemma presantValueDifferentiable (i:ℝ) (cf : cashFlowSequence) : HasStrictDerivAt (presentValue cf ) (presentValueDerivative cf i) i := HasSum

theorem deriv_presantValue (i: ℝ) (cf : cashFlowSequence) : deriv (presentValue cf) i = (presentValueDerivative cf) i := sorry
-/
/- lemma deriv_presantValue (i: ℝ) (cf : cashFlowSequence) : deriv (presentValue cf i) (presentValueDerivative cf i) := sorry -/







/- def cashflowExample : cashFlowSequence :=
  (List.range 10).map (λ k => { time := k+1, amount := 1000, t_nonneg := by })
 -/
/- The following taken from https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/View.20list.20elements -/
section
open Lean Elab Meta Tactic
partial def reduce_list (e : Expr) : MetaM Expr := do
  let e' ← whnf e
  if e'.isAppOfArity ``List.nil 1 then
    return e'
  else if e'.isAppOfArity ``List.cons 3 then
    let tail ← reduce_list e'.appArg!
    return Expr.app e'.appFn! tail
  else
    return e
elab "reduce_list" : conv => withMainContext do
  Conv.changeLhs (← reduce_list (← Conv.getLhs))

macro "#list_norm_num " t:term : command =>
  `(command| #conv (reduce_list; norm_num [CoeT.coe, CoeHTCT.coe]) => $t)
end

/- #list_norm_num cashflowExample -/

/- The next two calculations match the articles' (2.2) & (2.3) hence verifying that our definition work as intendend. -/

#norm_num [presentValue, List.foldr, CoeT.coe, CoeHTCT.coe] (presentValue cashflowExample 0.07) -- returns 1381644796127950460700000 / 196715135728956532249 ≈ 7023.5815

#norm_num [presentValue, List.foldr, CoeT.coe, CoeHTCT.coe] (presentValue cashflowExample 0.065)
/- 1381828868362807308274600000 / 192218876443582475037849 ≈ 7188.8302 -/


noncomputable def MacaulayDuration (cf : cashFlowSequence) (i : ℝ) : ℝ :=
  (cf.foldr (λ (c : Cashflow) (sum : ℝ) => sum + c.time * c.amount / ((1 + i) ^ c.time)) 0) / presentValue cf i

noncomputable def modifiedDuration (cf : cashFlowSequence) (i : ℝ) : ℝ := (MacaulayDuration cf i) / (1+i)

lemma modifiedDurationAltDefn : modifiedDuration = (λ (cfs : cashFlowSequence) (i : ℝ) => (-presentValueDerivative  i cfs)/(presentValue i cfs)) := sorry

/- Two more calculations verifying our definitions are correct -/
#norm_num [MacaulayDuration, List.foldr, presentValue, CoeT.coe, CoeHTCT.coe] (MacaulayDuration cashflowExample 0.07) /- 68337133122415284707 / 13816447961279504607 ≈ 4.9460710 -/

#norm_num [modifiedDuration, MacaulayDuration, List.foldr, presentValue, CoeT.coe, CoeHTCT.coe] (modifiedDuration cashflowExample 0.07) /- 6833713312241528470700 / 1478359931856906992949 ≈ 4.6224963 -/

/- theorem abs_log_sub_add_sum_range_le {x : ℝ} (h : |x| < 1) (n : ℕ) :
    |(∑ i in range n, x ^ (i + 1) / (i + 1)) + log (1 - x)| ≤ |x| ^ (n + 1) / (1 - |x|) := -/

/- theorem firstOrderModifiedApprox -/
/-- **Taylor's theorem** with the Lagrange form of the remainder.

We assume that `f` is `n+1`-times continuously differentiable in the closed set `Icc x₀ x` and
`n+1`-times differentiable on the open set `Ioo x₀ x`. Then there exists an `x' ∈ Ioo x₀ x` such
that $$f(x) - (P_n f)(x₀, x) = \frac{f^{(n+1)}(x') (x - x₀)^{n+1}}{(n+1)!},$$
where $P_n f$ denotes the Taylor polynomial of degree $n$ and $f^{(n+1)}$ is the $n+1$-th iterated
derivative. -/
/-- **Taylor's theorem** with the Cauchy form of the remainder.

We assume that `f` is `n+1`-times continuously differentiable on the closed set `Icc x₀ x` and
`n+1`-times differentiable on the open set `Ioo x₀ x`. Then there exists an `x' ∈ Ioo x₀ x` such
that $$f(x) - (P_n f)(x₀, x) = \frac{f^{(n+1)}(x') (x - x')^n (x-x₀)}{n!},$$
where $P_n f$ denotes the Taylor polynomial of degree $n$ and $f^{(n+1)}$ is the $n+1$-th iterated
derivative. -/

/-!
# Main theorem

This file defines the Taylor polynomial of a real function `f : ℝ → E`,
where `E` is a normed vector space over `ℝ` and proves Taylor's theorem,
which states that if `f` is sufficiently smooth, then
`f` can be approximated by the Taylor polynomial up to an explicit error term.

## Main definitions



## Main         statements



## TODO



## Tags

Macaulay duration, modified duration,

TODO:
* add sections?
* assume P(i) ≠ 0
* add namespaces?
-/
