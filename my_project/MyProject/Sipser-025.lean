import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic

set_option tactic.hygienic false


example (a b c : ℕ) (h : 0 < a) (h₁: a*b=a*c ) : b = c
:= Nat.mul_left_cancel h h₁

example (a b c : ℝ) (h : a ≠ 0) (h₁: a*b=a*c ) : b = c
:= mul_left_cancel₀ h h₁


theorem Sipser_025
  {P_ : ℕ → ℂ}
  (P M Y : ℂ)
  (h: P_ 0 = P)
  (hM: M - 1 ≠ 0)
  (ha : ∀ t:ℕ, P_ (Nat.succ t) = (P_ t) * M - Y)
  (t:ℕ)
  :
  P_ t = P * M^t - Y * (M^t - 1)/(M-1)
  := by {
    induction t; simp; exact h
    let g := ha n; rw [g,n_ih,Nat.succ_eq_add_one]
    apply mul_left_cancel₀ hM; field_simp; left; ring
  }
