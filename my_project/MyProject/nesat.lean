import Mathlib.Tactic
set_option tactic.hygienic false

def cnf_clause (p q r : Prop) := p ∨ q ∨ r
def dnf_clause (p q r : Prop) := p ∧ q ∧ r
def nesat_clause (p q r : Prop) := cnf_clause p q r ∧ ¬ dnf_clause p q r

theorem nesat_reduction:
∃ b : Prop, ∀ y₁ y₂ y₃ : Prop, ∃ z : Prop,
       cnf_clause   y₁ y₂ y₃ ↔ nesat_clause   y₁ y₂ z ∧ nesat_clause (¬z) y₃ b
:= by
  exists False; unfold nesat_clause cnf_clause dnf_clause
  intro y₁ y₂ y₃; by_cases y₁ ∨ y₂
  . exists False;tauto
  . exists y₃;tauto

def some_true₃ (p : Fin 3 → Prop) := p 0 ∨ p 1 ∨ p 2
def all_true₃ (p : Fin 3 → Prop) := p 0 ∧ p 1 ∧ p 2
def not_all_eq (p : Fin 3 → Prop) := some_true₃ p ∧ ¬ all_true₃ p

theorem nesat₃reduction_pair_theorem:
∃ b : Prop, ∀ y : Fin 3 → Prop, ∃ z : Prop,
  some_true₃ y ↔ not_all_eq ![y 0, y 1, z] ∧ not_all_eq ![¬z, y 2, b]
:= by
  obtain ⟨b,hb⟩ := nesat_reduction
  exists b;intro y;obtain ⟨z,hz⟩ := hb (y 0) (y 1) (y 2);exists z

def nesat₃reduction_pair (y : Fin 3 → Prop) [Decidable (y 0 ∨ y 1)]
: (Fin 3 → Prop) × (Fin 3 → Prop) :=
  by let z := ite (y 0 ∨ y 1) False (y 2);exact (![y 0, y 1, z],![¬ z, y 2, False])

theorem reduce_3SAT_to_NESAT_prop : ∀ n : ℕ, ∀ φ : Fin n → (Fin 3 → Prop),
(∀ i, Decidable (φ i 0 ∨ φ i 1)) → ∃ ψ : Fin n → (Fin 3 → Prop) × (Fin 3 → Prop),
  (∀ i, some_true₃ (φ i)) ↔ ∀ i, (not_all_eq (ψ i).1 ∧ not_all_eq (ψ i).2)
  := by
    intro n φ _; exists (λ i ↦ nesat₃reduction_pair (φ i))
    unfold nesat₃reduction_pair not_all_eq some_true₃ all_true₃
    constructor
    . intro hφ i;let _ := hφ i;simp;tauto
    . intro hψ i;let hψi := hψ i;simp at hψi;tauto

-- Now it looks like a proper DecisionProblem reduction: (March 24, 2024)

open Classical

def sat3instance : Type := Σ n, (Fin n → (Fin 3 → Prop))

def reduction_3SAT_to_NESAT (φ : sat3instance) : sat3instance := ⟨2*φ.1, (λ i ↦ ite (Even i.1)
       (nesat₃reduction_pair (φ.2 ⟨i.1/2, Nat.div_lt_of_lt_mul i.2⟩)).1
       (nesat₃reduction_pair (φ.2 ⟨i.1/2, Nat.div_lt_of_lt_mul i.2⟩)).2
    )⟩

theorem reduce_3SAT_to_NESAT' (φ : sat3instance) -- [∀ i j, Decidable (φ.2 i j)]
: ∃ ψ : sat3instance,
  (∀ i, some_true₃ (φ.2 i)) ↔ ∀ i, (not_all_eq (ψ.2 i))
  := by
    exists (reduction_3SAT_to_NESAT φ)
    constructor
    . intro hφ i
      let hφi := hφ ⟨i.1/2, Nat.div_lt_of_lt_mul i.2⟩
      unfold some_true₃ at hφi
      unfold reduction_3SAT_to_NESAT not_all_eq some_true₃ nesat₃reduction_pair all_true₃
      . by_cases h : Even i.1
        . simp;rw [if_pos h];simp;tauto
        . simp;rw [if_neg h];simp;tauto
    . intro hψ i
      have p₀ : 2 * i.1     < 2 * φ.1 := (mul_lt_mul_iff_of_pos_left Nat.two_pos).mpr i.2
      have p₁ : 2 * i.1 + 1 < 2 * φ.1 := by let Q := i.2;linarith
      have : ¬ Even (2* i.1 + 1)    := Nat.odd_iff_not_even.mp (odd_two_mul_add_one i.1)
      let hψi₀ := hψ ⟨2*i.1,p₀⟩
      let hψi₁ := hψ ⟨2*i.1+1,p₁⟩
      unfold some_true₃
      unfold reduction_3SAT_to_NESAT not_all_eq some_true₃ nesat₃reduction_pair all_true₃ at hψi₀ hψi₁
      simp at hψi₀ hψi₁
      rw [if_neg this] at hψi₁
      simp at hψi₁
      let Q := hψi₀.1
      cases Q
      . tauto
      . cases h
        . tauto
        . simp at h_1
          tauto



-- Boolean development
def cnfclause (p q r : Bool) := p || q || r
def dnfclause (p q r : Bool) := p && q && r
def nesatclause (p q r : Bool) := cnfclause p q r && ! (dnfclause p q r)

theorem nesatreduction:
∃ b : Bool, ∀ y₁ y₂ y₃ : Bool, ∃ z : Bool,
       cnfclause   y₁ y₂ y₃ = (nesatclause  y₁ y₂ z && nesatclause (!z) y₃ b)
:= by exists False

def cnf₃_clause (p : Fin 3 → Bool) := p 0 || p 1 || p 2
def dnf₃_clause (p : Fin 3 → Bool) := p 0 && p 1 && p 2
def nesat₃_clause (p : Fin 3 → Bool) := cnf₃_clause p && ! dnf₃_clause p

def nesat₃_reduction (y : Fin 3 → Bool)
: (Fin 3 → Bool) × (Fin 3 → Bool) :=
  by let z := ite (y 0 || y 1) false (y 2);exact (![y 0, y 1, z],![! z, y 2, false])

theorem material₀ (p q : Bool) : (p → q = true) ↔ (!p || q) = true := by
  constructor
  intro h
  simp at h
  simp
  by_cases hh : (p = true)
  tauto
  simp at hh
  tauto

  intro h₀ h₁
  simp at h₀
  cases h₀
  . exfalso
    exact Bool.true_eq_false_eq_False (Bool.and_or_inj_right h h₁.symm)
  . exact h

theorem material₁ (p q : Bool) : (¬ p → q = true) ↔ (p || q) = true := by
  constructor
  intro h
  simp at h
  simp
  by_cases hh : (p = true)
  tauto
  simp at hh
  tauto

  intro h₀ h₁
  simp at h₀
  cases h₀
  . exfalso
    exact h₁ h
  . exact h

theorem material₂ (p q : Bool) : (¬ (p=true) → q = true) ↔ (p || q) = true := by
  constructor
  intro h
  simp at h
  simp
  by_cases hh : (p = true)
  tauto
  simp at hh
  tauto

  intro h₀ h₁
  simp at h₀
  cases h₀
  . exfalso
    exact h₁ h
  . exact h

theorem material₃ (p q r : Bool) : (¬ (p=true ∨ q = true) → r = true) ↔ (p || q || r) = true := by
  constructor
  intro h
  simp at h
  simp
  by_cases hh : (p = true)
  tauto
  simp at hh
  tauto

  intro h₀ h₁
  simp at h₀
  cases h₀
  . exfalso
    exact h₁ h
  . exact h

theorem material₄ (p q r : Bool) : (¬ (p=true ∨ q = true) → r = false) ↔ (p || q || !r) = true := by
  constructor
  intro h
  simp at h
  simp
  by_cases hh : (p = true)
  tauto
  simp at hh
  tauto

  intro h₀ h₁
  simp at h₀
  cases h₀
  . exfalso
    exact h₁ h
  . exact h


theorem reduce_3SAT_to_NESAT : ∀ n : ℕ, ∀ φ : Fin n → (Fin 3 → Bool),
 ∃ ψ : Fin n → (Fin 3 → Bool) × (Fin 3 → Bool),
  (∀ i, cnf₃_clause (φ i) = true) ↔ ∀ i, ((nesat₃_clause (ψ i).1 && nesat₃_clause (ψ i).2) = true)
  := by
    intro n φ; exists (λ i ↦ nesat₃_reduction (φ i))
    unfold nesat₃_reduction nesat₃_clause cnf₃_clause dnf₃_clause
    simp -- unfortunately introduces a "→"
    constructor
    . intro hφ i;let h := hφ i;
      constructor
      constructor
      tauto
      cases h
      tauto
      by_cases h : ((φ i 0 = false ∨ φ i 1 = false))
      . tauto
      right
      intro hh
      exfalso
      by_cases h₀: (φ i 0 = true)
      . tauto
      . . by_cases h₁: (φ i 1 = true)
          tauto
          simp at h₀ h₁
          tauto
      . tauto
    . intro hψ i;let hψi := hψ i;simp at hψi;tauto



-- theorem reduce_3SAT_to_NESAT' : ∀ n : ℕ, ∀ φ : Fin n → (Fin 3 → Bool),
--  ∃ ψ : Fin (2*n) → (Fin 3 → Bool),
--   (∀ i, cnf₃_clause (φ i) = true) ↔ ∀ i, (nesat₃_clause (ψ i) = true)
--   := by
--     intro n φ
--     exists (λ i ↦ by
--       by_cases  (Even i)
--       exact (nesat₃_reduction (φ ⟨i.1/2, Nat.div_lt_of_lt_mul i.2⟩)).1
--       exact (nesat₃_reduction (φ ⟨i.1/2, Nat.div_lt_of_lt_mul i.2⟩)).2
--     )
--     constructor
--     intro hφ i
--     unfold nesat₃_clause cnf₃_clause nesat₃_reduction dnf₃_clause
--     simp
--     by_cases h : (Even i)
--     rw [dif_pos h]
--     simp
--     let hφi := hφ ⟨i.1/2, Nat.div_lt_of_lt_mul i.2⟩
--     unfold cnf₃_clause at hφi
--     simp at hφi

--     constructor
--     tauto
--     rw [material₄]
--     cases hφi
--     cases h_1
--     simp
--     by_cases ht : φ ⟨i.1/2, Nat.div_lt_of_lt_mul i.2⟩ 1 = true
--     -- rw [dif_pos h_2]
--     -- rw [dif_pos ht]
--     sorry
--     sorry
--     sorry

--     sorry
--     sorry
