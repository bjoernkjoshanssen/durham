import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Data.Vector.Basic

theorem orderly_injective_helper {β:Type} (x : ℕ → β)
  (a b : β) (hab: a ≠ b)
  (h₀ : x 0 = a)
  (j:ℕ) (hj : ∃ i, i < j ∧ x i.succ = b)
  (h₂: ∀ i, i < j → x i = a ∨ x i = b)
  [DecidablePred fun n => n < j ∧ x (Nat.succ n) = b]
  :
  (∃ i, i < j ∧ x i = a ∧ x i.succ = b) := by
  exists (Nat.find hj);let Q := Nat.find_spec hj
  constructor;exact Q.1;constructor;let R := h₂ (Nat.find hj) Q.1
  cases R;rename_i p;exact p;rename_i p;exfalso
  have : (Nat.find hj) ≠ 0 := by
    intro hc;rw [← hc] at h₀;have : a = b := Eq.trans h₀.symm p
    exact hab this
  obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero this
  have : Nat.find hj ≤ i := Nat.find_le (by
    constructor
    calc
      i < i.succ := Nat.lt.base i
      _ = Nat.find hj := hi.symm
      _ < j := Q.1
    rw [← hi];exact p
  )
  have : Nat.succ i ≤ i := Eq.trans_le (id hi.symm) this
  contrapose this;exact Nat.not_succ_le_self i;exact Q.2


theorem fin_fin {k:ℕ} {i:ℕ} {j:Fin k.succ} (h: i < j.1):
i < k := by
    calc
      _ < j.1 := h
      _ ≤ k := Fin.is_le j

theorem fin_fi {k:ℕ} {i:ℕ} {j:Fin k.succ} (h: i < j.1):
i < k.succ := by
    calc
      _ < j.1 := h
      _ ≤ k.succ := Fin.is_le'

theorem orderly_injective_helper₁ {β:Type} (k:ℕ) (x : (Fin k.succ) → β)
  (a b : β) (hab: a ≠ b)
  (h₀ : x 0 = a)
  (j:Fin k.succ) (hj : ∃ i, i.1 < j.1 ∧ x (Fin.succ i) = b)
  (h₂: ∀ i, i.1 < j.1 → x i = a ∨ x i = b)
  [DecidablePred fun n => ∃ (h : n < j.1), x (Fin.succ ⟨n, fin_fin h⟩) = b]
  :
    (∃ i : Fin k, i.1 < j.1 ∧ x (Fin.castSucc i) = a ∧ x (Fin.succ i) = b) := by
  have hthis: ∃ n:ℕ, ∃ h : n < j.1, x (Fin.succ ⟨n,fin_fin h⟩) = b := by
    obtain ⟨i,hi⟩ := hj
    exists i.1
    exists hi.1
    exact hi.2
  have h : Nat.find hthis < j.1 := by
        obtain ⟨h,_⟩ := Nat.find_spec hthis
        exact h
  exists ⟨Nat.find hthis,fin_fin h⟩
  obtain ⟨h,_⟩ := Nat.find_spec hthis
  constructor
  exact h
  constructor
  cases h₂ ⟨Nat.find hthis,fin_fi h
  ⟩ h
  rename_i p;exact p;rename_i p;exfalso
  have hthis₀: (⟨(Nat.find hthis),fin_fi h⟩ : Fin k.succ) ≠ 0 := by
    intro hc;
    rw [← hc] at h₀;
    have : a = b := Eq.trans h₀.symm p
    exact hab this
  have : Nat.find hthis ≠ 0 := by
    intro hc
    exact hthis₀ (Fin.ext hc)
  obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero this
  have : Nat.find hthis ≤ i := Nat.find_le (by
    constructor
    simp
    simp_rw [← Nat.succ_eq_add_one,← hi]
    exact p
    calc
      i < i.succ          := Nat.lt.base i
      _ = Nat.find hthis  := hi.symm
      _ < j               := (Nat.find_spec hthis).1
  )
  have : Nat.succ i ≤ i := Eq.trans_le (id hi.symm) this
  contrapose this;exact Nat.not_succ_le_self i;exact (Nat.find_spec hthis).2

theorem orderly_injective_helper₂ (k:ℕ) (x : (Fin k.succ) → Fin 4)
  (h₀ : x 0 = 0)
  (j:Fin k.succ) (hj : ∃ i, i.1 < j.1 ∧ x (Fin.succ i) = 1)
  (h₂: ∀ i, i.1 < j.1 → x i = 0 ∨ x i = 1)
  :
  (∃ i : Fin k, i.1 < j.1 ∧ x (Fin.castSucc i) = 0 ∧ x (Fin.succ i) = 1)
  :=
  orderly_injective_helper₁ _ _ _ _ (Fin.zero_ne_one) h₀ _ hj h₂

theorem orderly_injective_helper₃ (k:ℕ) (moves : Vector (Fin 4) k.succ)
  (h₀ : moves.get 0 = 0)
  (j:Fin k.succ) (hj : ∃ i, i.1 < j.1 ∧ moves.get (Fin.succ i) = 1)
  (h₂: ∀ i, i.1 < j.1 → moves.get i = 0 ∨ moves.get i = 1)
  :
  (∃ i : Fin k, i.1 < j.1 ∧ moves.get (Fin.castSucc i) = 0 ∧ moves.get (Fin.succ i) = 1)
  :=
  orderly_injective_helper₁ _ _ _ _ (Fin.zero_ne_one) h₀ _ hj h₂
-- somehow this works even though moves is now a vector

-- now we want to point out that if moves.get (Fin.castSucc i) = 0 ∧ moves.get (Fin.succ i) = 1
-- then λ i ↦ (pathᵥ rect moves).get i is not injective because equals at i and i+2
