import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option tactic.hygienic false

/-
As a proof of concept we obtain the bound l*l/2 for the protein folding score function
using the handshaking lemma implementation in Mathlib.

This is a weaker result than found in other files except that we prove it for Berger-Leighton scoring.
-/


open Classical


def nearby {α β : Type} [DecidableEq α] [Fintype β] (go : β → α → α)
  (p q : α) : Bool := ∃ a : β, q = go a p

def pt_loc {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
  {l : ℕ} (fold : Fin l → α) (i j : Fin l) (phobic : Fin l → Bool) : Bool
  :=  phobic i && phobic j && i.1.succ < j.1 && nearby go (fold i) (fold j)

/-- Berger and Leighton (RECOMB 1998) allowed
points to be scored between amino acids following each other in the chain. -/
def pt_loc_BL {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
  {l : ℕ} (fold : Fin l → α) (i j : Fin l) (phobic : Fin l → Bool) : Bool
  :=  phobic i && phobic j && nearby go (fold i) (fold j)

theorem le_pt_loc_BL {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
  {l : ℕ} (fold : Fin l → α) (i j : Fin l) (phobic : Fin l → Bool) :
  pt_loc go fold i j phobic
  →
  pt_loc_BL  go fold i j phobic
  := by
  unfold pt_loc pt_loc_BL
  simp
  tauto


instance BergerLeightonGraph {b l:ℕ} (go : Fin b → α → α) (fold : Fin l → (α)) (ph : Fin l → Bool)
(hl : ∀ a, ¬ nearby go a a)
(hs : Symmetric (λ a b ↦ nearby go a b))
: SimpleGraph (Fin l) := {
  Adj := λ i k ↦ (pt_loc_BL go fold i k ph)
  symm := by
    unfold pt_loc_BL
    intro i k h
    simp
    simp at h
    constructor
    tauto
    exact hs h.2
  loopless := by
    intro i;simp;unfold pt_loc_BL;simp;
    right;exact Bool.eq_false_iff.mpr (hl (fold i))
}


instance ScoreGraph {b l:ℕ} (go : Fin b → α → α) (fold : Fin l → (α)) (ph : Fin l → Bool)
: SimpleGraph (Fin l) := {
  Adj := λ i k ↦ (pt_loc go fold i k ph) ∨ (pt_loc go fold k i ph)
  loopless := by
    intro i;simp;unfold pt_loc;simp;left;right;exact Nat.le_succ ↑i
}

def points_tot -- April 25, 2024
  {α:Type} {β : Type} [Fintype β] (go : β → α → α)
  [DecidableEq α] {l:ℕ} (ph : Fin l → Bool) (fold : Fin l → α)
  := Finset.card (
    Finset.filter
    (λ ik : (Fin l) × (Fin l) ↦ ((pt_loc go fold ik.1 ik.2 ph): Prop))
    (Finset.univ)
  )   -- think "ik = (i,k)"


def points_tot_BL -- April 27, 2024
  {α:Type} {β : Type} [Fintype β] (go : β → α → α)
  [DecidableEq α] {l:ℕ} (ph : Fin l → Bool) (fold : Fin l → α)
  := Finset.card (
    Finset.filter
    (λ ik : (Fin l) × (Fin l) ↦ ((pt_loc_BL go fold ik.1 ik.2 ph ∧ ik.1 < ik.2): Prop))
    (Finset.univ)
  )   -- think "ik = (i,k)"

--pt_loc is not symmetric but can be symmetrized
theorem le_points_tot_BL -- April 27, 2024
  {α:Type} {β : Type} [Fintype β] (go : β → α → α)
  [DecidableEq α] {l:ℕ} (ph : Fin l → Bool) (fold : Fin l → α) :
  points_tot go ph fold ≤
  points_tot_BL go ph fold := by
    apply Finset.card_le_card
    intro ik h
    simp at *
    constructor
    exact le_pt_loc_BL go fold ik.1 ik.2 ph h
    unfold pt_loc at h
    simp at h
    show ik.1.1 < ik.2.1
    calc
    ik.1.1 < ik.1.1.succ := by exact Nat.lt.base ↑ik.1
    _ < _ := by tauto


def edgeFun   {b l:ℕ} (go : Fin b → α → α) (fold : Fin l → (α)) (ph : Fin l → Bool) :
{ x // x ∈ Finset.filter (fun ik : Fin l × Fin l => pt_loc go fold ik.1 ik.2 ph = true) Finset.univ } →
{ x // x ∈ Finset.filter (fun x => x ∈ SimpleGraph.edgeSet (ScoreGraph go fold ph)) Finset.univ }
:= λ ik ↦ ⟨Sym2.mk ik,by
  let Q := ik.2
  simp at Q
  simp
  unfold ScoreGraph
  unfold SimpleGraph.edgeSet
  simp
  unfold SimpleGraph.edgeSetEmbedding
  simp
  left
  exact Q
⟩
def edgeFunBL   {b l:ℕ} (go : Fin b → α → α) (fold : Fin l → (α)) (ph : Fin l → Bool)
(hl : ∀ a, ¬ nearby go a a)
(hs : Symmetric (λ a b ↦ nearby go a b))
:
{ x // x ∈ Finset.filter (fun ik : Fin l × Fin l => pt_loc_BL go fold ik.1 ik.2 ph = true ∧ ik.1 < ik.2)
  Finset.univ } →
{ x // x ∈ Finset.filter (fun x => x ∈ SimpleGraph.edgeSet (BergerLeightonGraph go fold ph hl hs)) Finset.univ }
:= λ ik ↦ ⟨Sym2.mk ik,by
  let Q := ik.2
  simp at Q
  simp
  unfold BergerLeightonGraph
  unfold SimpleGraph.edgeSet
  simp
  unfold SimpleGraph.edgeSetEmbedding
  simp
  exact Q.1
⟩


theorem edgeFunBL_surjective    {b l:ℕ} (go : Fin b → α → α) (fold : Fin l → (α)) (ph : Fin l → Bool)
(hl : ∀ a, ¬ nearby go a a)
(hs : Symmetric (λ a b ↦ nearby go a b))
: Function.Surjective (edgeFunBL go fold ph hl hs) := by
  intro x
  let hx₁ := x.2
  simp at hx₁
  unfold BergerLeightonGraph at hx₁
  unfold edgeFunBL
  let i := (Quot.out x.1).1
  let k := (Quot.out x.1).2
  by_cases hik: (i.1 < k.1)
  . exists ⟨Quot.out x.1,by
      simp
      simp at hx₁
      unfold SimpleGraph.edgeSet at hx₁
      simp at hx₁
      unfold SimpleGraph.edgeSetEmbedding at hx₁
      simp at hx₁
      let Q := @Sym2.fromRel_proj_prop (Fin l)
        (fun i k => pt_loc_BL go fold i k ph = true)
        (by
          unfold Symmetric
          intro x y h
          unfold pt_loc_BL at *
          simp at *
          constructor
          tauto
          exact hs h.2
        ) (Quot.out x.1)
      have : x.1 = Sym2.mk (Quot.out x.1) := by exact (Quot.out_eq x.1).symm
      rw [← this] at Q
      rw [Q] at hx₁
      tauto
    ⟩
    simp
  . exists ⟨Prod.swap (Quot.out x.1),by
      simp
      simp at hx₁
      unfold SimpleGraph.edgeSet at hx₁
      simp at hx₁
      unfold SimpleGraph.edgeSetEmbedding at hx₁
      simp at hx₁
      let Q := @Sym2.fromRel_proj_prop (Fin l)
        (fun i k => pt_loc_BL go fold i k ph = true)
        (by
          unfold Symmetric
          intro x y h
          unfold pt_loc_BL at *
          simp at *
          constructor
          tauto
          exact hs h.2
        ) (Quot.out x.1)
      have : x.1 = Sym2.mk (Quot.out x.1) := by exact (Quot.out_eq x.1).symm
      rw [← this] at Q
      rw [Q] at hx₁
      unfold pt_loc_BL at *
      simp at *
      constructor
      tauto
      have : (Quot.out x.1).2 < (Quot.out x.1).1
        ∨ (Quot.out x.1).2 = (Quot.out x.1).1 := by exact lt_or_eq_of_le hik
      cases this
      exact h
      exfalso
      apply hl (fold (Quot.out x.1).1)
      rw [h] at hx₁
      tauto
    ⟩
    simp


theorem edgeFun_surjective    {b l:ℕ} (go : Fin b → α → α) (fold : Fin l → (α)) (ph : Fin l → Bool)
: Function.Surjective (edgeFun go fold ph) := by
  intro x
  let hx₁ := x.2
  simp at hx₁
  unfold ScoreGraph at hx₁
  unfold edgeFun
  let i := (Quot.out x.1).1
  let k := (Quot.out x.1).2
  by_cases hik: (i.1 < k.1)
  . exists ⟨Quot.out x.1,by
      simp
      simp at hx₁
      unfold SimpleGraph.edgeSet at hx₁
      simp at hx₁
      unfold SimpleGraph.edgeSetEmbedding at hx₁
      simp at hx₁
      let Q := @Sym2.fromRel_proj_prop (Fin l)
        (fun i k => pt_loc go fold i k ph = true ∨ pt_loc go fold k i ph = true)
        (by
          unfold Symmetric
          intro x y h
          tauto
        ) (Quot.out x.1)
      have : x.1 = Sym2.mk (Quot.out x.1) := by exact (Quot.out_eq x.1).symm
      rw [← this] at Q
      rw [Q] at hx₁
      cases hx₁
      . tauto
      . exfalso
        unfold pt_loc at h
        simp at h
        let R := h.1.2
        have : k.1.succ < i.1 := R
        have : k.1.succ < k.1 := LT.lt.trans this hik
        contrapose this
        exact Nat.not_succ_lt_self
    ⟩
    simp
  . exists ⟨Prod.swap (Quot.out x.1),by
      simp
      simp at hx₁
      unfold SimpleGraph.edgeSet at hx₁
      simp at hx₁
      unfold SimpleGraph.edgeSetEmbedding at hx₁
      simp at hx₁
      let Q := @Sym2.fromRel_proj_prop (Fin l)
        (fun i k => pt_loc go fold i k ph = true ∨ pt_loc go fold k i ph = true)
        (by
          unfold Symmetric
          intro x y h
          tauto
        ) (Quot.out x.1)
      have : x.1 = Sym2.mk (Quot.out x.1) := by exact (Quot.out_eq x.1).symm
      rw [← this] at Q
      rw [Q] at hx₁
      cases hx₁
      . exfalso
        unfold pt_loc at h
        simp at h
        let R := h.1.2
        have : i.1.succ < k.1 := R
        have : i.1.succ < i.1 := calc
          _ < k.1 := R
          _ ≤ _ := Nat.not_lt.mp hik
        contrapose this
        exact Nat.not_succ_lt_self
      . tauto
    ⟩
    simp

theorem edgeFunBL_injective    {b l:ℕ} (go : Fin b → α → α) (fold : Fin l → (α)) (ph : Fin l → Bool)
(hl : ∀ a, ¬ nearby go a a)
(hs : Symmetric (λ a b ↦ nearby go a b))
: Function.Injective (edgeFunBL go fold ph hl hs) := by
  intro ⟨x,Q₁⟩ ⟨y,Q₂⟩
  unfold edgeFunBL
  simp
  intro h
  cases h
  . exact h_1
  . exfalso
    unfold pt_loc_BL at *
    simp at *
    unfold Prod.swap at h_1
    have H₀: x.1 = y.2 := by rw [h_1]
    have H₁: x.2 = y.1 := by rw [h_1]
    have hx: x.2 < x.1 := by
      rw [← H₀,← H₁] at Q₂
      tauto
    have : x.1 < x.1 := by calc
      x.1 < x.2 := by tauto
      _ < x.1 := hx
    contrapose this
    exact Eq.not_gt rfl

theorem edgeFun_injective    {b l:ℕ} (go : Fin b → α → α) (fold : Fin l → (α)) (ph : Fin l → Bool)
: Function.Injective (edgeFun go fold ph) := by
  intro ⟨x,Q₁⟩ ⟨y,Q₂⟩
  unfold edgeFun
  simp
  intro h
  cases h
  . exact h_1
  . exfalso
    unfold pt_loc at *
    simp at *
    unfold Prod.swap at h_1
    have H₀: x.1.1 = y.2.1 := by rw [h_1]
    have H₁: x.2.1 = y.1.1 := by rw [h_1]
    let R₁ := Q₁.1.2; rw [H₀,H₁] at R₁
    have : y.1.1.succ < y.1.1 := calc
          y.1.1.succ < y.2.1      := Q₂.1.2
          _          < y.2.1.succ := Nat.lt.base ↑y.2
          _          < y.1.1      := R₁
    contrapose this
    exact Nat.not_succ_lt_self

theorem points_imcs  {b l:ℕ} (go : Fin b → α → α) (fold : Fin l → (α)) (ph : Fin l → Bool)
:  (SimpleGraph.edgeFinset (ScoreGraph go fold ph)).card = points_tot go ph fold
:= by
  simp
  unfold points_tot
  repeat rw [← Fintype.card_coe]
  have : Function.Bijective (edgeFun go fold ph) := by
    constructor
    exact edgeFun_injective go fold ph
    exact edgeFun_surjective go fold ph
  exact (Fintype.card_of_bijective this).symm

theorem points_icmsBL  {b l:ℕ} (go : Fin b → α → α) (fold : Fin l → (α)) (ph : Fin l → Bool)
(hl : ∀ a, ¬ nearby go a a)
(hs : Symmetric (λ a b ↦ nearby go a b))
:  (SimpleGraph.edgeFinset (BergerLeightonGraph go fold ph hl hs)).card = points_tot_BL go ph fold
:= by
  simp
  unfold points_tot_BL
  repeat rw [← Fintype.card_coe]
  have : Function.Bijective (edgeFunBL go fold ph hl hs) := by
    constructor
    exact edgeFunBL_injective go fold ph hl hs
    exact edgeFunBL_surjective go fold ph hl hs
  exact (Fintype.card_of_bijective this).symm

theorem fiber {b l:ℕ} (go : Fin b → α → α) (fold : Fin l → (α)) (ph : Fin l → Bool):
Fintype.card (SimpleGraph.Dart (ScoreGraph go fold ph ))
  = 2 * (SimpleGraph.edgeFinset (ScoreGraph go fold ph)).card
 := SimpleGraph.dart_card_eq_twice_card_edges _

theorem fiber_more  {b l:ℕ} (go : Fin b → α → α) (fold : Fin l → (α)) (ph : Fin l → Bool):
Fintype.card (SimpleGraph.Dart (ScoreGraph go fold ph ))
  ≤ l * l := by
    have h₀: Fintype.card (Fin l) = l := by exact Fintype.card_fin l
    have h₁: Fintype.card (Fin l × Fin l) =
      Fintype.card (Fin l) * Fintype.card (Fin l) := by exact Fintype.card_prod (Fin l) (Fin l)
    have h₂: Fintype.card (Fin l × Fin l) = l * l := by
      rw [h₁,h₀]
    rw [← h₂]
    unfold ScoreGraph
    let f : SimpleGraph.Dart (ScoreGraph go fold ph) → Fin l × Fin l :=
      λ dart ↦ (dart.fst,dart.snd)
    apply Fintype.card_le_of_injective f (by
      intro d₁ d₂ h
      simp at h
      exact SimpleGraph.Dart.ext d₁ d₂ h
    )

theorem bound_BL  {b l:ℕ} (go : Fin b → α → α) (fold : Fin l → (α)) (ph : Fin l → Bool)
(hl : ∀ a, ¬ nearby go a a)
(hs : Symmetric (λ a b ↦ nearby go a b))
: 2 * points_tot_BL go ph fold ≤ l * l := by
  let Q := points_icmsBL go fold ph hl hs
  rw [← Q]
  have h₀: Fintype.card (Fin l) = l := by exact Fintype.card_fin l
  have h₁: Fintype.card (Fin l × Fin l) =
    Fintype.card (Fin l) * Fintype.card (Fin l) := by exact Fintype.card_prod (Fin l) (Fin l)
  have h₂: Fintype.card (Fin l × Fin l) = l * l := by
    rw [h₁,h₀]
  rw [← h₂]
  rw [← SimpleGraph.dart_card_eq_twice_card_edges]
  let f : SimpleGraph.Dart (BergerLeightonGraph go fold ph hl hs) → Fin l × Fin l :=
    λ dart ↦ (dart.fst,dart.snd)

  apply Fintype.card_le_of_injective f (by
    intro d₁ d₂ h
    simp at h
    exact SimpleGraph.Dart.ext d₁ d₂ h
  )
