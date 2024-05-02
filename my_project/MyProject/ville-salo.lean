import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.MetricSpace.Baire
import Mathlib.Init.Order.Defs
import Mathlib.Topology.Clopen
import Init.Prelude

/-
In this file we prove every statement (by Ville Salo) in the following paragraph
from https://mathoverflow.net/questions/364808/homeomorphisms-and-mod-finite/364844#364844
The numbers below are the things to prove and define.

[1] Define `f : C → C` by the formula ` f(x) = x_0 ⬝ (x ⊕ σ(x)) `
    where `⬝` is word concatenation,
    `⊕ : C × C → C` is coordinatewise `xor`, and
    `σ(x)_i = x_{i+1}` is the shift.
[2] Clearly this map is continuous
[3] and preserves `=^*`.
[4] It is a bijection because you can deduce the preimage one coordinate at a time,
which amounts to summing the prefix,
[5] `f^{-1}(x)_i = \bigoplus_{j \leq i} x_i$.`
[6] By compactness `f` is a homeomorphism.
[7] However, `f(0^\omega) = 0^\omega` and
[8] `f(1^\omega) = 10^\omega`, so
[9] `f` does not respect `=^*`.

And here is where to find the proofs in this file.
[1]: `def ville_salo`
[2]: `theorem continuous_ville_salo`
[3]: `theorem ville_salo_E₉`
[4]: `theorem ville_salo_injective`, `ville_salo_surjective`
[5]: `def iteratedXor`, `theorem ville_salo_iteratedXor_id`
[6]: `def ville_salo_homeo` (although I did not use compactness)
[7]: `theorem ville_salo_false`
[8]: `theorem ville_salo_1false`
[9]: `theorem not_iteratedXor_E₉`
-/

set_option tactic.hygienic false
set_option maxHeartbeats 10000000

/-- Definition 13 in `A tractable case`. Apr 11, 2024.-/
def searrow {α : Type} (σ : Σ n : ℕ, Fin n → α) (X : ℕ → α) : ℕ → α := by
  intro n
  by_cases h : (n < σ.1)
  exact σ.2 ⟨n,h⟩
  exact X n

/- Definition 3.2 in `Randomness extraction and asymptotic Hamming distance`.-/
def frown {α : Type} (σ : Σ n : ℕ, Fin n → α) (X : ℕ → α) : ℕ → α := by
  intro n
  by_cases h : (n < σ.1)
  exact σ.2 ⟨n,h⟩
  exact X (n - σ.1)

infix:50 " ↘ " => searrow
infix:50 " ⌢ " => frown

def cantor := ℕ → Bool
instance : TopologicalSpace cantor := by
  unfold cantor
  exact inferInstance

/-- From
  https://mathoverflow.net/questions/364808/homeomorphisms-and-mod-finite/364844#364844
-/
def ville_salo : cantor → cantor := λ x ↦
  ⟨1,λ n ↦ x n.1⟩ ⌢ (λ n ↦ xor (x n) (x n.succ))

def iterated_xor (X : ℕ → Bool) : ℕ → Bool := by
  intro n
  induction n
  exact X 0
  exact xor n_ih (X n_1.succ)

def iteratedXor (X : ℕ → Bool) : ℕ → Bool := by
  intro n
  match n with
  | 0 => exact X 0
  | Nat.succ k => exact xor (X k.succ) (iteratedXor X k)

-- #eval iterated_xor (λ _ ↦ true) 0
-- #eval iterated_xor (λ _ ↦ true) 1
-- #eval iterated_xor (λ _ ↦ true) 2
-- #eval iterated_xor (λ _ ↦ true) 3
-- #eval iteratedXor (λ _ ↦ true) 0
-- #eval iteratedXor (λ _ ↦ true) 1
-- #eval iteratedXor (λ _ ↦ true) 2
-- #eval iteratedXor (λ _ ↦ true) 3


theorem ville_salo_iteratedXor_id :
  ville_salo ∘ iteratedXor = id := by
  apply funext
  intro Y
  apply funext
  intro n
  induction n
  . rfl
  . unfold ville_salo frown
    simp
    unfold ville_salo frown at n_ih
    simp at n_ih
    by_cases h : n_1 = 0
    . subst h
      simp at n_ih
      unfold iteratedXor
      rw [n_ih]
      cases Y 0
      repeat (cases Y 1;simp;simp)
    . suffices (iteratedXor Y (Nat.succ n_1)) = xor (Y (Nat.succ n_1)) (iteratedXor Y n_1) by
        rw [this]
        cases (iteratedXor Y (n_1))
        repeat simp
      rfl

theorem ville_salo_iterated_xor_id :
  ville_salo ∘ iterated_xor = id := by
  apply funext
  intro Y
  apply funext
  intro n
  induction n
  . rfl
  . unfold ville_salo frown
    simp
    unfold ville_salo frown at n_ih
    simp at n_ih
    by_cases h : (n_1 = 0)
    subst h
    unfold iterated_xor
    simp
    cases Y 0
    repeat simp
    rw [if_neg h] at n_ih
    have : iterated_xor Y (Nat.succ n_1)
    = xor (iterated_xor Y (n_1)) (Y n_1.succ) := rfl
    rw [this]
    cases (iterated_xor Y n_1)
    repeat simp

theorem ville_salo_surjective :
  Function.Surjective ville_salo := by
  intro Y
  exists (iterated_xor Y)
  exact congrFun ville_salo_iterated_xor_id Y

theorem ville_salo_injective :
  Function.Injective ville_salo := by
    intro x y hxy
    apply funext
    intro n
    unfold ville_salo at hxy
    induction n
    simp at hxy
    let Q := congrFun hxy 0
    unfold frown at Q
    simp at Q
    exact Q
    simp at hxy
    let Q := congrFun hxy n_1.succ
    unfold frown at Q
    simp at Q
    rw [n_ih] at Q
    have : ∀ a b₁ b₂ : Bool,
      xor a b₁ = xor a b₂ → b₁ = b₂ := by
        intro a b₁ b₂ h
        have : a = true ∨ a = false := Bool.eq_false_or_eq_true a
        cases this
        . subst h_1
          simp at h
          exact Bool.not_inj h
        . subst h_1
          simp at h
          exact h
    exact this (y n_1) _ _ Q


def shift {α : Type}
 (X : ℕ → α) (n:ℕ) := X (n.succ)


def right_shift
 (X : ℕ → Bool) (n:ℕ) := (ite (n=0)) false (X (n.pred))

theorem continuous_shift : Continuous (@shift (Bool)) := by
  unfold shift
  exact Pi.continuous_precomp' fun j ↦ Nat.succ j

theorem continuous_right_shift : Continuous (right_shift) := by
  unfold right_shift
  refine continuous_pi ?h
  intro i
  by_cases h : (i=0)
  . subst h
    simp
    exact continuous_const
  exact {
    isOpen_preimage := by
      intro O hO
      show IsOpen ((fun a ↦ if i = 0 then false else a (Nat.pred i)) ⁻¹' O)
      have : (fun a : ℕ → Bool ↦ if i = 0 then false else a (Nat.pred i))
        = (fun a ↦ a (Nat.pred i)) := by
          apply funext
          intro A
          rw [if_neg h]
      rw [this]
      refine Continuous.isOpen_preimage ?_ O hO
      exact continuous_apply (Nat.pred i)
  }


theorem characterize_ville_salo :
  ville_salo = λ A ↦ (λ n ↦ xor (A n) (right_shift A n)) := by
    unfold ville_salo right_shift xor frown
    simp
    apply funext
    intro A
    apply funext
    intro n
    induction n
    . simp
    . simp
      exact Bool.xor_comm (A n_1) (A (Nat.succ n_1))


theorem xor_continuous_ville_salo₀₀ :
      ∀ p q : (ℕ → Bool) → Bool, Continuous p → Continuous q →
      Continuous (λ A ↦ xor (p A) (q A)) := by
      intro p q hp hq
      let Q := @Continuous.comp₂ Bool Bool Bool (ℕ → Bool) _ _ _ _
        (λ pair ↦ xor pair.1 pair.2) (by
          have : Continuous (λ b c : Bool ↦ xor b c) := by exact continuous_bot
          simp at this
          have : (fun x : Bool × Bool => if (fun pair : Bool × Bool => ¬pair.1 = pair.2) x then true else false)
           = (fun pair : Bool × Bool => xor pair.1 pair.2) := by
            apply funext;intro pair;cases pair;cases fst
            repeat (cases snd;repeat simp)
          simp at this
          rw [← this]
          apply continuous_of_discreteTopology
        )
        p hp q hq
      exact Q

theorem xor_continuous_ville_salo₀ (f g : (ℕ → Bool) → (Bool)) (hf : Continuous f)
  (hg : Continuous g) : Continuous (
    λ A ↦ (λ _ ↦ xor (f A) (g A))
    : (ℕ → Bool) → (ℕ → Bool)
  ) := by
    refine continuous_pi ?h
    intro
    exact xor_continuous_ville_salo₀₀ (λ A ↦ f A) (λ A ↦ g A) hf hg

theorem xor_continuous_ville_salo (f g : (ℕ → Bool) → (ℕ → Bool)) (hf : Continuous f)
  (hg : Continuous g) : Continuous (
    λ A ↦ (λ n ↦ xor (f A n) (g A n))
    : (ℕ → Bool) → (ℕ → Bool)
  ) := by
    refine continuous_pi ?h
    intro i
    have h_: Continuous fun a : ℕ → Bool ↦ a i := continuous_apply i
    have h_f: Continuous fun a ↦ f a i := Continuous.comp h_ hf
    have h_g: Continuous fun a ↦ g a i := Continuous.comp h_ hg
    exact xor_continuous_ville_salo₀₀ (λ A ↦ f A i) (λ A ↦ g A i) h_f h_g

/-- This follows from general theory as in https://math.stackexchange.com/questions/3042668/continuous-bijection-between-compact-and-hausdorff-spaces-is-a-homeomorphism
  but we can try a direct proof-/
theorem continuous_iteratedXor : Continuous iteratedXor := by
  refine continuous_pi ?h
  intro i
  induction i

  unfold iteratedXor
  exact continuous_apply 0
  unfold iteratedXor

  let Q := xor_continuous_ville_salo₀₀
    (λ A ↦ A n.succ) (λ A ↦ iteratedXor A n)
    (continuous_apply (Nat.succ n)) n_ih
  simp at Q
  exact Q

theorem continuous_ville_salo :
  Continuous ville_salo := by
    rw [characterize_ville_salo]
    apply xor_continuous_ville_salo
    exact Pi.continuous_precomp' fun j => j
    exact continuous_right_shift

def ville_salo_homeo : Homeomorph (ℕ → Bool) (ℕ → Bool) := {
  toFun := ville_salo
  invFun := iteratedXor
  continuous_toFun := continuous_ville_salo
  right_inv := by
    unfold Function.RightInverse
    intro A
    exact congrFun ville_salo_iteratedXor_id A
  left_inv := by
      intro A
      suffices ville_salo (iteratedXor (ville_salo A)) = ville_salo A by
        exact ville_salo_injective this
      let Q := congrFun ville_salo_iteratedXor_id (ville_salo A)
      simp at Q
      exact Q
  continuous_invFun :=  continuous_iteratedXor
}

theorem ville_salo_false : ville_salo (λ _ ↦ false) = λ _ ↦ false := by
  apply funext
  intro n
  unfold ville_salo frown
  simp

theorem ville_salo_false' : iteratedXor (λ _ ↦ false) = λ _ ↦ false := by
  suffices ville_salo (iteratedXor (λ _ ↦ false)) = ville_salo (λ _ ↦ false) by
    exact ville_salo_injective this
  let Q := congrFun ville_salo_iteratedXor_id (λ _ ↦ false)
  simp at Q
  rw [Q]
  exact ville_salo_false.symm

theorem ville_salo_1false : ville_salo (λ _ ↦ true) =  (⟨1,λ _ ↦ true⟩ ⌢ (λ _ ↦ false))
 := by
  apply funext
  intro n
  unfold ville_salo frown
  simp

theorem ville_salo_1false' : iteratedXor (⟨1,λ _ ↦ true⟩ ⌢ (λ _ ↦ false)) = (λ _ ↦ true) := by
  suffices ville_salo (iteratedXor (⟨1,λ _ ↦ true⟩ ⌢ (λ _ ↦ false))) = ville_salo (λ _ ↦ true) by
    exact ville_salo_injective this
  let Q := congrFun ville_salo_iteratedXor_id (⟨1,λ _ ↦ true⟩ ⌢ (λ _ ↦ false))
  simp at Q
  rw [Q]
  exact ville_salo_1false.symm

def invariant {α : Type} (E : α → α → Prop) (F : α → α) : Prop :=
∀ A B : α, E A B → E (F A) (F B)

infix:50 " invariant_under " => invariant

def E₀ {α:Type} (A B : ℕ → α) : Prop := ∃ a, ∀ n, a ≤ n → A n = B n

def E₀invariant {α:Type} (F : (ℕ → α) → (ℕ → α)) : Prop :=
(E₀ invariant_under F)

theorem not_iteratedXor_E₉ : ¬ E₀invariant iteratedXor := by
  unfold E₀invariant
  intro hc
  have : E₀ (λ _ ↦ false) (⟨1,λ _ ↦ true⟩ ⌢ (λ _ ↦ false)) := by
    unfold frown E₀
    exists 1
    intro n
    simp
    intro h
    have : ¬ n = 0 := by exact Nat.pos_iff_ne_zero.mp h
    rw [if_neg this]
  have : E₀ (iteratedXor (λ _ ↦ false)) (iteratedXor (⟨1,λ _ ↦ true⟩ ⌢ (λ _ ↦ false))) := by
    let Q := hc _ _ this
    exact Q
  rw [ville_salo_false'] at this
  rw [ville_salo_1false'] at this
  obtain ⟨a,ha⟩ := this
  let Q := ha a (le_refl _)
  simp at Q


theorem ville_salo_E₉ : E₀invariant ville_salo := by
  intro A B h
  unfold E₀ at *
  obtain ⟨a,ha⟩ := h
  exists a.succ
  intro n hn
  unfold ville_salo frown
  simp
  cases n
  . simp
    simp at hn
  . simp
    have : a ≤ n_1 := Nat.lt_succ.mp hn
    let Q := ha n_1 this
    let R := ha n_1.succ (Nat.le_step this)
    rw [Q,R]
