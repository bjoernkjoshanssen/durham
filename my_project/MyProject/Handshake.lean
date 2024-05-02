import MyProject.HydrophobicPolarModel
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
      simp only [mem_filter, mem_univ, true_and] at H₁ H₂
      exfalso
      exact hQ.asymm _ _ H₁.2 H₂.2
  simp only [union_idempotent]
  rw [Nat.add_comm, ← card_union_eq this]
  congr;apply ext; simp only [mem_filter, mem_univ, true_and, mem_union, Prod.forall];intro a b;tauto

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
  simp only [add_right_inj]
  congr
  apply funext
  intro x
  simp only [eq_iff_iff, and_congr_left_iff]
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
    simp only [mem_filter, mem_univ, true_and]
    simp only [mem_filter, mem_univ, true_and] at ha
    tauto
  have  h₂ : ∀ (a b : α×α) (ha : a ∈ s) (hb : b ∈ s), f a ha = f b hb → a = b := by
    intro a b ha hb hf
    simp only [Prod.mk.injEq] at hf
    apply Prod.ext
    tauto;tauto
  have h₃ : ∀ b ∈ t, ∃ (a : α×α) (ha : a ∈ s), f a ha = b := by
    intro b hb
    simp only [mem_filter, mem_univ, true_and, exists_prop, Prod.exists]
    simp only [mem_filter, mem_univ, true_and] at hb
    exists b.2
    exists b.1
  let R := card_congr f h₁ h₂ h₃
  rw [R]
  simp only [filter_congr_decidable]
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

open Finset
theorem twice_fold_pts₀  {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
 {l : ℕ} (fold : Vector α l.succ) (phobic : Vector Bool l.succ)
(hP: Symmetric (λ i j : Fin l.succ ↦ phobic.get i && phobic.get j && nearby go (fold.get i) (fold.get j))):
card (
  filter (
    λ a : (Fin l.succ) × (Fin l.succ) ↦
    phobic.get a.1 && phobic.get a.2 && nearby go (fold.get a.1) (fold.get a.2) && (
         a.1.1.succ < a.2.1
      ∨ a.2.1.succ < a.1.1
    )
  )
  univ
)
= 2 * card (filter (λ a : (Fin l.succ) × (Fin l.succ) ↦
  (phobic.get a.1 && phobic.get a.2 && nearby go (fold.get a.1) (fold.get a.2))  ∧ a.1.1.succ < a.2.1) univ)
  := by
  let Q := twice_fold (λ i j : Fin l.succ ↦ phobic.get i && phobic.get j && nearby go (fold.get i) (fold.get j)) hP
  simp only [Bool.decide_or, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  simp only [Bool.and_eq_true] at Q
  exact Q

theorem symmetric_nearby_helper₀
 {α: Type} [DecidableEq α] {β:Type} [Fintype β]
(go: β → α → α)
{l:ℕ} (ph : Vector Bool l.succ)
(fold : Vector α l.succ)
(hP: Symmetric (λ x y ↦ nearby go x y)):
Symmetric (λ i j : Fin l.succ ↦ ph.get i && ph.get j && nearby go (fold.get i) (fold.get j))
:= by
  intro x y h;
  simp only [Bool.and_eq_true];simp only [Bool.and_eq_true] at h;
  constructor;
  . tauto;
  . rw [hP];
    simp only;
    tauto

theorem twice_fold_pts₁ {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
  {l : ℕ} (fold : Vector α l.succ) (phobic : Vector Bool l.succ)
  (hP₀: Symmetric (λ x y ↦ nearby go x y))
  :
  card (filter (
      λ a : (Fin l.succ) × (Fin l.succ) ↦
      phobic.get a.1 && phobic.get a.2 && nearby go (fold.get a.1) (fold.get a.2) && (
          a.1.1.succ < a.2.1
        ∨ a.2.1.succ < a.1.1
      )
  ) univ) = 2 * points_tot go phobic fold
  := by
    have hP: Symmetric (λ i j : Fin l.succ ↦ phobic.get i && phobic.get j && nearby go (fold.get i) (fold.get j)) :=
      symmetric_nearby_helper₀ go phobic fold hP₀
    rw [twice_fold_pts₀ go fold phobic hP];
    simp only [Bool.and_eq_true, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false];
    unfold points_tot pt_loc;congr;simp only [Bool.and_eq_true,
      decide_eq_true_eq]
    apply funext;intro ik; simp only [eq_iff_iff];constructor;norm_num;intro h₁ h₂ h₃ h₄;tauto;tauto
  -- 3/14/2024, 3/25/2024

def handshake_map_3_to_2  {α:Type} {b:ℕ}
  -- map (i,j) to ((i,a),j) and then drop the j. iaj = ((i,a),j)
  (go : Fin b → α → α) [DecidableEq α]
  {l : ℕ} (fold : Vector α l.succ)
  (phobic : Vector Bool l.succ) :
  filter (
    λ iaj : ((Fin l.succ) × (Fin b)) × (Fin l.succ) ↦
      phobic.get iaj.1.1 && phobic.get iaj.2
      && (fold.get iaj.2) = go iaj.1.2 (fold.get iaj.1.1)
      && (iaj.1.1.1.succ < iaj.2.1 ∨ iaj.2.1.succ < iaj.1.1.1)
  ) univ
  →  filter (
    λ ia : ((Fin l.succ) × (Fin b)) ↦ -- ia = (i,a)
    ∃ j : Fin l.succ, phobic.get ia.1 && phobic.get j
      && (fold.get j) = go ia.2 (fold.get ia.1)
      && (ia.1.1.succ < j.1 ∨ j.1.succ < ia.1.1)
  ) univ
:= λ iaj ↦ ⟨iaj.1.1,by
  simp only [Bool.decide_or, Bool.and_eq_true,
  decide_eq_true_eq, Bool.or_eq_true, mem_filter, mem_univ, true_and];
  exists iaj.1.2;let Q := iaj.2;simp only [Bool.decide_or,
  Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, mem_filter, mem_univ, true_and] at Q ;tauto
⟩

def handshake_map_2_to_3  {α:Type} {b:ℕ}
  -- map (i,j) to ((i,a),j) and then drop the j.
  (go : Fin b → α → α) [DecidableEq α]
  {l : ℕ} (fold : Vector α l.succ)
  (phobic : Vector Bool l.succ)
  :
    filter (
    λ ij : (Fin l.succ) × (Fin l.succ) ↦
    phobic.get ij.1 && phobic.get ij.2 && nearby go (fold.get ij.1) (fold.get ij.2)
      && (ij.1.1.succ < ij.2.1 ∨ ij.2.1.succ < ij.1.1)
  ) univ →
  filter (
    λ iaj : ((Fin l.succ) × (Fin b)) × (Fin l.succ) ↦ -- ia = (i,a)
      phobic.get iaj.1.1 && phobic.get iaj.2
      && ((fold.get iaj.2) = go iaj.1.2 (fold.get iaj.1.1))
      && (iaj.1.1.1.succ < iaj.2.1 ∨ iaj.2.1.succ < iaj.1.1.1)
  ) univ
:= λ ij ↦ by
  simp only [Bool.decide_or, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    mem_filter, mem_univ, true_and] at ij
  let Q := ij.2.1.2
  unfold nearby at Q
  simp only [decide_eq_true_eq] at Q
  let a' := Fin.find (λ a ↦ fold.get ij.1.2 = go a (fold.get ij.1.1))
  have ha': Option.isSome a' := Fin.isSome_find_iff.mpr Q
  let a := a'.get ha'
  let i := ij.1.1
  let j := ij.1.2
  exact ⟨(⟨i,a⟩,j),by
    simp only [Bool.decide_or, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      mem_filter, mem_univ, true_and]
    constructor;constructor;
    exact ij.2.1.1
    unfold nearby
    simp only
    exact Fin.find_spec
          (λ a : Fin b ↦ fold.get ij.1.2 = go a (fold.get ij.1.1))
          (Option.get_mem ha')
    exact ij.2.2
  ⟩

theorem handshake_2_to_3_injective
  {α:Type} {b:ℕ}
  -- let's just map (i,j) to (i,j,a) and then drop the j.
  (go : Fin b → α → α) [DecidableEq α]
  {l : ℕ} (fold : Vector α l.succ)
  (phobic : Vector Bool l.succ):
  Function.Injective (handshake_map_2_to_3 go fold phobic) := by
    intro ⟨i₁,j₁⟩ ⟨i₂,j₂⟩ h
    unfold handshake_map_2_to_3 at h
    simp only [eq_mp_eq_cast, Bool.decide_or, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, filter_val, Multiset.mem_filter, mem_val, mem_univ, true_and, set_coe_cast,
      Subtype.mk.injEq, Prod.mk.injEq] at h
    have : i₁ = i₂ := by apply Prod.ext; tauto;tauto
    exact SetCoe.ext this

theorem handshake_3_to_2_injective
  {α:Type} {b:ℕ}
  -- let's just map (i,j) to (i,j,a) and then drop the j.
  (go : Fin b → α → α) [DecidableEq α]
  {l : ℕ} (fold : Vector α l.succ)
  (hfold : Function.Injective (λ i ↦ fold.get i))
  (phobic : Vector Bool l.succ):
  Function.Injective (handshake_map_3_to_2 go fold phobic) := by
  intro iajp₁ iajp₂ h
  unfold handshake_map_3_to_2 at h
  simp only [Subtype.mk.injEq] at h
  let p₁ := iajp₁.2;simp only [Bool.decide_or, Bool.and_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, mem_filter, mem_univ, true_and] at p₁
  let p₂ := iajp₂.2;simp only [Bool.decide_or, Bool.and_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, mem_filter, mem_univ, true_and] at p₂
  let j₁ := iajp₁.1.2
  let j₂ := iajp₂.1.2
  apply SetCoe.ext; apply Prod.ext
  tauto; apply hfold
  show fold.get j₁ = fold.get j₂
  rw [p₁.1.2, p₂.1.2, h]

def handshake_map_2_to_2  {α:Type} {b:ℕ}
  -- map (i,j) to ((i,a),j) and then drop the j.
  (go : Fin b → α → α) [DecidableEq α]
  {l : ℕ} (fold : Vector α l.succ)
  (phobic : Vector Bool l.succ)
  :
    filter (
    λ ij : (Fin l.succ) × (Fin l.succ) ↦
    phobic.get ij.1 && phobic.get ij.2 && nearby go (fold.get ij.1) (fold.get ij.2)
      && (ij.1.1.succ < ij.2.1 ∨ ij.2.1.succ < ij.1.1)
  ) univ
  →  filter (
    λ ia : ((Fin l.succ) × (Fin b)) ↦ -- ia = (i,a)
    ∃ j : Fin l.succ, phobic.get ia.1 && phobic.get j
      && (fold.get j) = go ia.2 (fold.get ia.1)
      && (ia.1.1.succ < j.1 ∨ j.1.succ < ia.1.1)
  ) univ
:= λ ij ↦ handshake_map_3_to_2 go fold phobic (handshake_map_2_to_3 go fold phobic ij)

theorem handshake_map_2_to_2_injective  {α:Type} {b:ℕ}
  -- map (i,j) to (i,a) injectively. 3/16/2024
  (go : Fin b → α → α) [DecidableEq α]
  {l : ℕ} (fold : Vector α l.succ)
  (phobic : Vector Bool l.succ)
  (hfold : Function.Injective (λ i ↦ fold.get i))
  : Function.Injective (handshake_map_2_to_2 go fold phobic) := by
    intro ij₁ ij₂ h
    unfold handshake_map_2_to_2 at h

    apply handshake_3_to_2_injective at h
    apply handshake_2_to_3_injective at h
    exact h
    exact hfold

theorem handshake_card₀
  {α:Type} {b:ℕ}
  -- map (i,j) to ((i,a),j) and then drop the j.
  (go : Fin b → α → α) [DecidableEq α]
  {l : ℕ} (fold : Vector α l.succ)
  (phobic : Vector Bool l.succ)
  (hfold : Function.Injective (λ i ↦ fold.get i))
  : card (
    filter (
    λ ij : (Fin l.succ) × (Fin l.succ) ↦
    phobic.get ij.1 && phobic.get ij.2 && nearby go (fold.get ij.1) (fold.get ij.2)
      && (ij.1.1.succ < ij.2.1 ∨ ij.2.1.succ < ij.1.1)
  ) univ)
  ≤ card ( filter (
    λ ia : ((Fin l.succ) × (Fin b)) ↦ -- ia = (i,a)
    ∃ j : Fin l.succ, phobic.get ia.1 && phobic.get j
      && (fold.get j) = go ia.2 (fold.get ia.1)
      && (ia.1.1.succ < j.1 ∨ j.1.succ < ia.1.1)
  ) univ)
:= by
  let α' := filter (
    λ ij : (Fin l.succ) × (Fin l.succ) ↦
    phobic.get ij.1 && phobic.get ij.2 && nearby go (fold.get ij.1) (fold.get ij.2)
      && (ij.1.1.succ < ij.2.1 ∨ ij.2.1.succ < ij.1.1)
  ) univ
  let β' := filter (
    λ ia : ((Fin l.succ) × (Fin b)) ↦ -- ia = (i,a)
    ∃ j : Fin l.succ, phobic.get ia.1 && phobic.get j
      && (fold.get j) = go ia.2 (fold.get ia.1)
      && (ia.1.1.succ < j.1 ∨ j.1.succ < ia.1.1)
  ) univ
  let f : α' → β'
    :=  λ a ↦ (handshake_map_2_to_2 go fold phobic a)
  let s : Finset α' := univ
  let t : Finset β' := univ

  have hf : ∀ a ∈ s, f a ∈ t := by
    intro a;intro;simp
  have f_inj : ∀ a₁ ∈ s, ∀ a₂ ∈ s, f a₁ = f a₂ → a₁ = a₂ := by
    intro a₁
    intro
    intro a₂
    intro
    intro hf
    apply handshake_map_2_to_2_injective
    exact hfold
    exact hf
  have : s.card ≤ t.card := Finset.card_le_card_of_inj_on f hf f_inj
  simp only [univ_eq_attach, card_attach, Bool.decide_or, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq] at this
  simp only [Bool.decide_or, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    ge_iff_le]
  tauto

theorem handshake_card₁
  {α:Type} {b:ℕ}
  -- map (i,j) to ((i,a),j) and then drop the j.
  (go : Fin b → α → α) [DecidableEq α]
  {l : ℕ} (fold : Vector α l.succ)
  (phobic : Vector Bool l.succ)
  (hfold : Function.Injective (λ i ↦ fold.get i))
  (hP₀: Symmetric (λ x y ↦ nearby go x y))

  : points_tot go phobic fold ≤ l.succ * b / 2
:= by
  apply Nat.le_div_two_iff_mul_two_le.mpr
  apply Int.toNat_le.mp
  suffices 2 * points_tot go phobic fold ≤ l.succ * b by
    rw [Nat.mul_comm] at this
    tauto
  let U := (Finset.univ : Finset (Fin l.succ × Fin b))
  calc
  _ = card (filter (λ a : (Fin l.succ) × (Fin l.succ) ↦
      phobic.get a.1 && phobic.get a.2  && nearby go (fold.get a.1) (fold.get a.2)
        && (a.1.1.succ < a.2.1 ∨ a.2.1.succ < a.1.1)
    ) univ)                         := (twice_fold_pts₁ go fold phobic hP₀).symm
  _ ≤ card ( filter (λ ia : (Fin l.succ) × (Fin b) ↦ ∃ j : Fin l.succ,
      phobic.get ia.1 && phobic.get j   && (fold.get j) = go ia.2 (fold.get ia.1)
        && (ia.1.1.succ < j.1 ∨ j.1.succ < ia.1.1)
    ) univ)                         := handshake_card₀ _ _ _ hfold
  _ ≤ card ( filter (λ _ ↦ True) U) := by
    apply Finset.card_le_card (by intros;simp)
  _ = card U                        := by apply card_eq_of_equiv; simp only [mem_univ,
    forall_true_left, Prod.forall, implies_true, forall_const, filter_true_of_mem];rfl
  _ = l.succ * b                    := by rw [Finset.card_univ];simp

-- #check (univ: Finset (Fin 2)) ×ˢ (univ: Finset (Fin 2))
-- #check (Fin 2) × (Fin 2)
-- #check (univ: Finset (Fin 2)) × (univ: Finset (Fin 2))
theorem cartesian_prod₀ {x y : ℕ} {P: Fin x → Prop} {Q: Fin y → Prop}
  [DecidablePred fun a => P a]
  [DecidablePred fun a => Q a]
  :  (filter (λ ab : Fin x                ×                 Fin y ↦ P ab.1 ∧ Q ab.2) univ)
  =  (filter (λ a : (Fin x)  ↦ P a) univ) ×ˢ (filter (λ b : Fin y  ↦ Q b) univ)
  := by refine ext ?_;intro ab;simp

theorem cartesian_prod₁ {x y : ℕ} {P: Fin x → Prop}
  [DecidablePred fun a => P a]
  :  (filter (λ ab : Fin x                ×                 Fin y ↦ P ab.1) univ)
  =  (filter (λ a : (Fin x)  ↦ P a) univ) ×ˢ (univ : Finset (Fin y))
  := by refine ext ?_;intro ab;simp

theorem card_product_set_type₀ {x y : ℕ} {P: Fin x → Prop} {Q: Fin y → Prop}
  [DecidablePred fun a => P a]
  [DecidablePred fun a => Q a]
  : card (filter (λ ab : (Fin x) × (Fin y) ↦ P ab.1 ∧ Q ab.2) univ)
  = card (filter (λ a : (Fin x)  ↦ P a) univ)
  * card (filter (λ b : (Fin y)  ↦ Q b) univ)
  := by rw [cartesian_prod₀,card_product]

theorem card_product_set_type₁ (x y : ℕ) (P: Fin x → Prop)
  [DecidablePred fun a => P a]
  : card (filter (λ ab : (Fin x) × (Fin y) ↦ P ab.1) univ)
  = card (filter (λ a : (Fin x)  ↦ P a) univ) * y
  := by rw [cartesian_prod₁,card_product];simp

-- need a "P ab.1 ∧ Q ab" version of card_product_set_type:
theorem card_product_set_type₂ (x y : ℕ) (P: Fin x → Prop)
  (Q: Fin x × Fin y → Prop)
  [DecidablePred fun a => P a]
  [DecidablePred fun a => Q a]
  : card (filter (λ ab : (Fin x) × (Fin y) ↦ P ab.1 ∧ Q ab) univ)
  ≤ card (filter (λ a : (Fin x)  ↦ P a) univ)
  * y
  := by calc
    _ ≤ card (filter (λ ab : (Fin x) × (Fin y) ↦ P ab.1) univ) := by
      apply card_le_card;intro ab h; simp only [mem_filter, mem_univ, true_and] at *;tauto
    _ = _ := card_product_set_type₁ _ _ _

/- To strengthen handshake_card₁
we can also bound in terms of mumtrue, using card_product_set_type'
-/
def numtrue {l:ℕ} : Vector Bool l → ℕ := λ v ↦
  card (filter (λ i ↦ v.get i = true) (univ : Finset (Fin l)))


-- theorem symmetric_nearby_helper
--  {α: Type} [OfNat α 0] [DecidableEq α] {b:ℕ}
-- {go: Fin b → α → α}
-- {l:ℕ} (ph : Vector Bool l.succ)
-- (moves: Vector (Fin b) l)
-- (hP: Symmetric (λ x y ↦ nearby go x y)):
-- Symmetric (λ i j : Fin l.succ ↦ ph.get i && ph.get j && nearby go ((pathᵥ go moves).get i) ((pathᵥ go moves).get j))
-- := symmetric_nearby_helper₀ _ _ _ hP

theorem symmetric_pts_earned_bound_dir' {α: Type} [OfNat α 0] [DecidableEq α] {b:ℕ}
{go: Fin b → α → α}
{l:ℕ} (ph : Vector Bool l.succ)
(moves: Vector (Fin b) l)
(path_inj  : (Function.Injective fun k => Vector.get (pathᵥ go moves) k))
(hP: Symmetric (λ x y ↦ nearby go x y)) -- don't need right_injective left_injective go
: points_tot go ph (pathᵥ go moves) ≤ l.succ * b / 2 := by
  exact handshake_card₁ go (pathᵥ go moves) ph path_inj hP

theorem pts_earned_bound {α: Type} [OfNat α 0] [DecidableEq α] {b:ℕ} -- Apr 2, 2024
{go: Fin b → α → α}
{l:ℕ} (ph : Vector Bool l.succ)
(moves: Vector (Fin b) l)
(path_inj : (Function.Injective fun k => Vector.get (pathᵥ go moves) k))
(hP: Symmetric (λ x y ↦ nearby go x y))

: pts_tot' go ph (pathᵥ go moves) ≤ min (l.succ * b / 2) (l * l.pred / 2)
:= by
  apply Nat.le_min.mpr
  constructor
  rw [← pts_tot'_eq_points_tot]
  exact symmetric_pts_earned_bound_dir' ph moves path_inj hP
  exact pts_earned_bound_loc'_improved go ph (pathᵥ go moves)


lemma min_div₀
{a b: ℕ} (hab : a ≤ b)
: min (b / 2) (a / 2) ≤ min b a / 2
:= by
    rw [Nat.min_eq_right (Nat.div_le_div_right hab)]
    apply Nat.div_le_div_right
    apply Nat.le_min.mpr
    simp only [le_refl, and_true]
    tauto

lemma min_div {a b: ℕ} :
  min (b / 2) (a / 2) ≤ min b a / 2 := by
  cases Nat.le_or_le b a with
  | inl h =>
    rw [min_comm (b/2) (a/2)]
    rw [min_comm b a]
    exact min_div₀ h
  | inr h => exact min_div₀ h

theorem pts_earned_bound_div2 {α: Type} [OfNat α 0] [DecidableEq α] {b:ℕ} -- Apr 2, 2024
{go: Fin b → α → α}
{l:ℕ} (ph : Vector Bool l.succ)
(moves: Vector (Fin b) l)
(path_inj : (Function.Injective fun k => Vector.get (pathᵥ go moves) k))
(hP: Symmetric (λ x y ↦ nearby go x y))

: pts_tot' go ph (pathᵥ go moves) ≤ (min (l.succ * b) (l * l.pred)) / 2
-- still, in principle we can replace b by b-2 except for at endpoints.
-- so 2 * (b-1) + (l.succ - 2) * (b-2) = l.succ * (b-2) + 2
:= calc
  _ ≤ min (l.succ * b / 2) (l * l.pred / 2) := pts_earned_bound ph moves path_inj hP
  _ ≤ _                                     := min_div


lemma agarwala_2_1
  {α:Type} {b:ℕ}
  -- Like Lemma 2.1 in Agarwala et al. 3/17/2024
  (go : Fin b → α → α) [DecidableEq α]
  {l : ℕ} (fold : Vector α l.succ)
  (phobic : Vector Bool l.succ)
  (hfold : Function.Injective (λ i ↦ fold.get i))
  (h_P: Symmetric (λ x y ↦ nearby go x y))
  : points_tot go phobic fold ≤ (numtrue phobic) * b / 2
:= by
  suffices 2 * points_tot go phobic fold ≤ (numtrue phobic) * b by
    refine Nat.le_div_two_iff_mul_two_le.mpr ?_
    suffices  (points_tot go phobic fold) * 2 ≤ ((numtrue phobic) * b) by
      exact Int.toNat_le.mp this
    rw [Nat.mul_comm] at this
    tauto
  calc
  2 * points_tot go phobic fold = card (filter (
    λ a : (Fin l.succ) × (Fin l.succ) ↦
    phobic.get a.1 && phobic.get a.2 && nearby go (fold.get a.1) (fold.get a.2)
      && (a.1.1.succ < a.2.1 ∨ a.2.1.succ < a.1.1)
    ) univ)                                         := (twice_fold_pts₁ go fold phobic h_P).symm
  _ ≤ card ( filter (
    λ ia : (Fin l.succ) × (Fin b) ↦ -- ia = (i,a)
    ∃ j : Fin l.succ, phobic.get ia.1 && phobic.get j && (fold.get j) = go ia.2 (fold.get ia.1)
      && (ia.1.1.succ < j.1 ∨ j.1.succ < ia.1.1)
    ) univ)                                         := handshake_card₀ _ _ _ hfold
  _ = card ( filter (
    λ ia : (Fin l.succ) × (Fin b) ↦ -- ia = (i,a)
    phobic.get ia.1 && (∃ j : Fin l.succ, phobic.get j && (fold.get j) = go ia.2 (fold.get ia.1)
      && (ia.1.1.succ < j.1 ∨ j.1.succ < ia.1.1))
    ) univ) := by
      congr;simp only [Bool.decide_or, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true];apply funext;intro ab;
      simp only [eq_iff_iff];constructor;intro h;constructor;tauto;obtain ⟨j,hj⟩ := h
      exists j;tauto;intro h;obtain ⟨j,hj⟩ := h.2;exists j;tauto
  _ ≤ _                         := by simp only [Bool.decide_or, Bool.and_eq_true,
    decide_eq_true_eq, Bool.or_eq_true]; exact card_product_set_type₂ l.succ b (λ i ↦ phobic.get i) _
