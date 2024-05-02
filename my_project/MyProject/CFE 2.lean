import Mathlib.Data.Real.Basic
-- import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- import Mathlib.Data.Nat.Parity
-- import Mathlib.Data.Rat.Order
import Mathlib.Data.Nat.Basic
-- import Mathlib.Data.Rat.Basic

set_option tactic.hygienic false


-- def CFE (x : List ℕ) : ℚ  := match x with
-- | List.nil => 0
-- | a :: x   => (a:ℚ) + 1/(CFE x)

-- #eval CFE List.nil
-- #eval CFE [2,3,4,5]
-- #eval CFE [2,3,0,0]
-- #eval CFE [2,1,2,1,1,4,1,1,6,1,1,8]
-- #eval ((1:ℚ)+1/5)^5

-- axiom μ : (Set (Set ℕ)) → ℝ

-- axiom strings (n:ℕ) (σ : Set (Fin n)) : μ ({ A | ∀ k : Fin n,  k.1 ∈ A ↔ k ∈ σ}) = 2^(-n)

-- theorem half0 : μ ({ A | 0 ∈ A}) = 2^(-(1:ℕ)) :=
--   have h0: μ {A | ∀ (k : Fin 1), k.1 ∈ A ↔ k ∈ {0}} = 2^(-(1:ℕ)) := strings 1 {0}
--   have h1: {A | ∀ (k : Fin 1), k.1 ∈ A ↔ k ∈ ({0}: Set (Fin 1))} = {A : Set ℕ | 0 ∈ A} :=
--     Set.ext (
--       λ A ↦ by {
--         constructor
--         intro h
--         exact (h 0).mpr rfl
--         intros h k
--         constructor
--         intro
--         have : k = 0 := Fin.eq_zero k
--         exact this
--         intro
--         simp
--         exact h
--       }
--     )
--   calc
--   _ = μ {A | ∀ (k : Fin 1), k.1 ∈ A ↔ k ∈ ({0}:Set (Fin 1))} := by {rw[← h1];}
--   _ = 2^(-(1:ℕ)) := h0


theorem id_pow (k:ℕ) : k ≤ 2^k := by {
  induction k
  exact zero_le_one
  calc
  Nat.succ n  = n + 1 := rfl
  _ ≤ 2^n + 1 := add_le_add_right n_ih _
  _ ≤ 2^n + 2^n := add_le_add_left (Nat.one_le_two_pow _) _
  _ = 2^n * 2 := by ring
  _ = 2^Nat.succ n := rfl
}

-- theorem id_pow' (k:ℕ) : k+1 ≤ 2^(k+1) := id_pow (k+1)

-- theorem pow_dom (k:ℕ) (hk: 0 < k) : ∃ n:ℕ, 1/2^n ≤ 1/k := by {exists k;exact Nat.div_le_div_left (id_pow _) hk}


-- example (r : ℝ) (n : ℕ)
--   (h: r ≤ 1/2^n)
--   (h1 : (1:ℝ)/2^n ≤ 1/(n+1)):
--   r ≤ 1/(n+1) :=
--   le_trans h h1

-- example (a b : ℕ) (h : a ≤ b) : (a:ℝ) ≤ b
-- := by exact Nat.cast_le.mpr h

-- example (a b : ℝ) (h : a ≤ b) (hb : 0 < b) (ha : 0 < a) : 1/b ≤ 1/a :=
-- by {
--   exact (one_div_le_one_div hb ha).mpr h
-- }

theorem Aexample (a b : ℕ) (h : a ≤ b) (hb : 0<b) (ha : 0<a) :
  (1:ℝ)/b ≤ 1/a := by {
    have haR : (0:ℝ) < a := Nat.cast_pos.mpr ha
    have hbR : (0:ℝ) < b := Nat.cast_pos.mpr hb
    have hR : (a:ℝ) ≤ b := Nat.cast_le.mpr h
    exact (one_div_le_one_div hbR haR).mpr hR
  }

theorem Cool {r:ℝ} (h: ∀ n : ℕ, r ≤ (1:ℝ)/2^(n)): ∀ n : ℕ, r ≤ (1:ℝ)/(n+1) := by {

  intro n
  have ht: (0) < (2^(n+1)) := Nat.pow_two_pos (n + 1)
  have hn : 0 < (n)+1 := Nat.succ_pos n
  have hi : n+1 ≤ 2^(n+1) := id_pow (n+1)
  have he : (1:ℝ)/(2^(n+1)) ≤ (1:ℝ)/(n+1) := by {
    norm_cast
    exact Aexample (n+1) (2^(n+1)) hi ht hn
  }
  exact le_trans (h (n+1)) he
}

theorem arch_right' (r:ℝ) (h: 0 < r) : ∃ n : ℕ, 1/(n+1) < r := exists_nat_one_div_lt h

theorem arch_right {r:ℝ} (h: ∀ n : ℕ, r ≤ 1/(n+1)) : r ≤ 0 := by {
  by_contra hh
  have : 0 < r := by exact not_le.mp hh
  have : ∃ n : ℕ, 1/(n+1) < r := arch_right' r this
  cases this
  have hr : r ≤ 1/(w+1) := h w
  have : 1/((w:ℝ)+1) < 1/(w+1) := (calc
  1/(w+1) < r := h_1
  _ ≤ 1/(w+1) := hr)
  exact LT.lt.false this
}

theorem geom_arch_right {r:ℝ} (h: ∀ n : ℕ, r ≤ 1/2^(n)) : r ≤ 0 := by {
  have : ∀ n : ℕ, r ≤ (1:ℝ)/(n+1) := Cool h
  exact arch_right this
}

theorem geometric_archimedean {r:ℝ} (h0: 0≤r ) (h: ∀ n : ℕ, r ≤ 1/2^(n)) : r = 0 := by {
  have : r ≤0 := geom_arch_right h
  exact le_antisymm this h0
}
