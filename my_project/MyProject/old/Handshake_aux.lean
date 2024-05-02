import Mathlib.Tactic
open Finset


theorem disjoint_asymm {α:Type} [Fintype α]
[DecidableEq α]
(P Q :α → α → Prop)
[DecidablePred fun a : α × α => P a.1 a.2 ∧ Q a.1 a.2]
[DecidablePred fun a : α × α => P a.1 a.2 ∧ Q a.2 a.1]
[DecidablePred fun a : α × α => P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.2 a.1)]
[DecidablePred fun a : α × α => P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.1 a.2)]
(hQ : IsAsymm _ Q) :
card (filter (λ a : α × α ↦ P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.2 a.1)) univ)
= card (filter (λ a : α × α ↦ P a.1 a.2 ∧ Q a.1 a.2) univ)
+ card (filter (λ a : α × α ↦ P a.1 a.2 ∧ Q a.2 a.1) univ) := by
  have :
    (filter (λ a : α × α ↦ P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.2 a.1)) univ)
    =
    (filter (λ a : α × α ↦ P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.2 a.1)) univ)
    ∪
    (filter (λ a : α × α ↦ P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.2 a.1)) univ)
    := by
      apply ext
      simp
  rw [this]
  have : Disjoint
      (filter (λ a : α × α ↦ P a.1 a.2 ∧ (Q a.2 a.1)) univ)
      (filter (λ a : α × α ↦ P a.1 a.2 ∧ (Q a.1 a.2)) univ)
    := by
      intro A h₁ h₂ a ha
      let H₁ := h₁ ha
      let H₂ := h₂ ha
      simp at H₁ H₂
      exfalso
      exact hQ.asymm _ _ H₁.2 H₂.2
  simp
  rw [Nat.add_comm, ← card_union_eq this]
  congr;apply ext;simp;intro a b;tauto

theorem disjoint_symm_asymm {α:Type} [Fintype α]
[DecidableEq α]
(P Q :α → α → Prop)
[DecidablePred fun a : α × α => P a.1 a.2 ∧ Q a.1 a.2]
[DecidablePred fun a : α × α => P a.1 a.2 ∧ Q a.2 a.1]
[DecidablePred fun a : α × α => P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.2 a.1)]
[DecidablePred fun a : α × α => P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.1 a.2)]
[DecidablePred fun a : α × α => P a.2 a.1 ∧ Q a.2 a.1]
(hP : Symmetric P)
(hQ : IsAsymm _ Q) :
card (filter (λ a : α × α ↦ P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.2 a.1)) univ)
= card (filter (λ a : α × α ↦ P a.1 a.2 ∧ Q a.1 a.2) univ)
+ card (filter (λ a : α × α ↦ P a.2 a.1 ∧ Q a.2 a.1) univ) := by
  rw [disjoint_asymm P Q hQ]
  simp
  congr
  apply funext
  intro x
  simp
  intro
  constructor
  intro h
  exact hP h
  intro h
  exact hP h

theorem twice_symm_asymm {α:Type} [Fintype α]
[DecidableEq α]
(P Q :α → α → Prop)
[DecidablePred fun a : α × α => P a.1 a.2 ∧ Q a.1 a.2]
[DecidablePred fun a : α × α => P a.1 a.2 ∧ Q a.2 a.1]
[DecidablePred fun a : α × α => P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.2 a.1)]
[DecidablePred fun a : α × α => P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.1 a.2)]
[DecidablePred fun a : α × α => P a.2 a.1 ∧ Q a.2 a.1]
(hP : Symmetric P)
(hQ : IsAsymm _ Q) :
card (filter (λ a : α × α ↦ P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.2 a.1)) univ)
= 2 * card (filter (λ a : α × α ↦ P a.1 a.2 ∧ Q a.1 a.2) univ) := by
  rw [disjoint_symm_asymm P Q hP hQ]
  -- simp
  let s := (filter (λ a : α × α ↦ P a.1 a.2 ∧ Q a.1 a.2) univ)
  let t := (filter (λ a : α × α ↦ P a.2 a.1 ∧ Q a.2 a.1) univ)
  let f : (a : α × α) → (a ∈ s) → α × α := λ (x,y) _ ↦ (y,x)
  have
  h₁ : ∀ (a : α×α) (ha : a ∈ s), f a ha ∈ t := by
    intro a ha
    simp
    simp at ha
    tauto
  have  h₂ : ∀ (a b : α×α) (ha : a ∈ s) (hb : b ∈ s), f a ha = f b hb → a = b := by
    intro a b ha hb hf
    simp at hf
    apply Prod.ext
    tauto;tauto
  have h₃ : ∀ b ∈ t, ∃ (a : α×α) (ha : a ∈ s), f a ha = b := by
    intro b hb
    simp
    simp at hb
    exists b.2
    exists b.1
  let R := card_congr f h₁ h₂ h₃
  rw [R]
  simp
  ring



instance separated_asymm {l:ℕ} : IsAsymm _ (λ i j : Fin l ↦ i.1.succ < j.1) := {
  asymm := by
    intro a b h hc
    have : a.1.succ < a.1 := calc
      _ < b.1      := h
      _ < b.1.succ := Nat.lt.base b.1
      _ < _        := hc
    contrapose this
    exact Nat.not_succ_lt_self
}

theorem twice_fold {l:ℕ} (P: Fin l → Fin l → Prop)
[DecidablePred fun a : (Fin l) × (Fin l)  => P a.1 a.2]
[DecidablePred fun a : (Fin l) × (Fin l)  => P a.1 a.2 ∧ (fun i j => Nat.succ ↑i < ↑j) a.1 a.2]
[DecidablePred fun a : (Fin l) × (Fin l) => P a.1 a.2 ∧ ((fun i j => Nat.succ ↑i < ↑j) a.1 a.2 ∨ (fun i j => Nat.succ ↑i < ↑j) a.2 a.1)]
[DecidablePred fun a : (Fin l) × (Fin l) => P a.1 a.2 ∧ (λ i j : Fin l ↦ i.1.succ < j.1) a.2 a.1]
[DecidablePred fun a : (Fin l) × (Fin l) => P a.1 a.2 ∧ ((λ i j : Fin l ↦ i.1.succ < j.1) a.1 a.2 ∨ (λ i j : Fin l ↦ i.1.succ < j.1) a.1 a.2)]
[DecidablePred fun a : (Fin l) × (Fin l) => P a.2 a.1 ∧ ((λ i j : Fin l ↦ i.1.succ < j.1)) a.2 a.1]
(hP: Symmetric P):
card (
  filter (
    λ a : (Fin l) × (Fin l) ↦ P a.1 a.2 ∧ (
         a.1.1.succ < a.2.1
      ∨ a.2.1.succ < a.1.1)
  )
  univ
)
= 2 * card (filter (λ a : (Fin l) × (Fin l) ↦ P a.1 a.2 ∧ a.1.1.succ < a.2.1) univ) := by

  exact twice_symm_asymm P (λ i j : Fin l ↦ i.1.succ < j.1) hP separated_asymm
