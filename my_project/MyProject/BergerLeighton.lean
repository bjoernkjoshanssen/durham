import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import MyProject.HydrophobicPolarModel

/-
As a proof of concept we obtain the bound l*l/2 for the protein folding score function
using the handshaking lemma implementation in Mathlib.

This is a weaker result than found in other files except that we prove it for Berger-Leighton scoring.
-/


open Classical



def pt_locF {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
  {l : ℕ} (fold : Fin l → α) (i j : Fin l) (phobic : Fin l → Bool) : Bool
  :=  phobic i && phobic j && i.1.succ < j.1 && nearby go (fold i) (fold j)

/-- Berger and Leighton (RECOMB 1998) allowed
points to be scored between amino acids following each other in the chain. -/
def pt_locF_BL {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
  {l : ℕ} (fold : Fin l → α) (i j : Fin l) (phobic : Fin l → Bool) : Bool
  :=  phobic i && phobic j && nearby go (fold i) (fold j)



instance BergerLeightonGraph {b l:ℕ} (go : Fin b → α → α) (fold : Fin l → (α)) (ph : Fin l → Bool)
(hl : ∀ a, ¬ nearby go a a)
(hs : Symmetric (λ a b ↦ nearby go a b))
: SimpleGraph (Fin l) := {
  Adj := λ i k ↦ (pt_locF_BL go fold i k ph)
  symm := by
    unfold pt_locF_BL
    intro i k h
    simp only [Bool.and_eq_true]
    simp only [Bool.and_eq_true] at h
    constructor
    tauto
    exact hs h.2
  loopless := by
    intro i;simp only [Bool.not_eq_true];unfold pt_locF_BL;simp only [Bool.and_self,
      Bool.and_eq_false_eq_eq_false_or_eq_false];
    right;exact Bool.eq_false_iff.mpr (hl (fold i))
}


instance ScoreGraph {b l:ℕ} (go : Fin b → α → α) (fold : Fin l → (α)) (ph : Fin l → Bool)
: SimpleGraph (Fin l) := {
  Adj := λ i k ↦ (pt_locF go fold i k ph) ∨ (pt_locF go fold k i ph)
  loopless := by
    intro i;simp only [or_self, Bool.not_eq_true];unfold pt_locF;simp only [Bool.and_self, Bool.and_eq_false_eq_eq_false_or_eq_false,
      decide_eq_false_iff_not, not_lt];left;right;exact Nat.le_succ ↑i
}

def points_totF -- April 25, 2024
  {α:Type} {β : Type} [Fintype β] (go : β → α → α)
  [DecidableEq α] {l:ℕ} (ph : Fin l → Bool) (fold : Fin l → α)
  := Finset.card (
    Finset.filter
    (λ ik : (Fin l) × (Fin l) ↦ ((pt_locF go fold ik.1 ik.2 ph): Prop))
    (Finset.univ)
  )   -- think "ik = (i,k)"


/-- Berger-Leighton score -/
def points_tot_BL -- April 27, 2024
  {α:Type} {β : Type} [Fintype β] (go : β → α → α)
  [DecidableEq α] {l:ℕ} (ph : Fin l → Bool) (fold : Fin l → α)
  := Finset.card (
    Finset.filter
    (λ ik : (Fin l) × (Fin l) ↦ ((pt_locF_BL go fold ik.1 ik.2 ph ∧ ik.1 < ik.2): Prop))
    (Finset.univ)
  )   -- think "ik = (i,k)"

/-- Berger-Leighton score is higher than Dill score. -/
theorem le_points_tot_BL -- April 27, 2024
  {α:Type} {β : Type} [Fintype β] (go : β → α → α)
  [DecidableEq α] {l:ℕ} (ph : Fin l → Bool) (fold : Fin l → α) :
  points_totF go ph fold ≤
  points_tot_BL go ph fold := by
    apply Finset.card_le_card
    intro ik h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
    constructor
    unfold pt_locF at h
    unfold pt_locF_BL
    simp only [Bool.and_eq_true]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    tauto
    unfold pt_locF at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    show ik.1.1 < ik.2.1
    calc
    ik.1.1 < ik.1.1.succ := by exact Nat.lt.base ↑ik.1
    _ < _ := by tauto


def edgeFun   {b l:ℕ} (go : Fin b → α → α) (fold : Fin l → (α)) (ph : Fin l → Bool) :
{ x // x ∈ Finset.filter (fun ik : Fin l × Fin l => pt_locF go fold ik.1 ik.2 ph = true) Finset.univ } →
{ x // x ∈ Finset.filter (fun x => x ∈ SimpleGraph.edgeSet (ScoreGraph go fold ph)) Finset.univ }
:= λ ik ↦ ⟨Sym2.mk ik,by
  let Q := ik.2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at Q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold ScoreGraph
  unfold SimpleGraph.edgeSet
  simp only [Set.le_eq_subset]
  unfold SimpleGraph.edgeSetEmbedding
  simp only [OrderEmbedding.coe_ofMapLEIff, Sym2.fromRel_proj_prop]
  left
  exact Q
⟩
def edgeFunBL {b l:ℕ} (go : Fin b → α → α) (fold : Fin l → (α)) (ph : Fin l → Bool)
(hl : ∀ a, ¬ nearby go a a)
(hs : Symmetric (λ a b ↦ nearby go a b))
:
{ x // x ∈ Finset.filter (fun ik : Fin l × Fin l => pt_locF_BL go fold ik.1 ik.2 ph = true ∧ ik.1 < ik.2)
  Finset.univ } →
{ x // x ∈ Finset.filter (fun x => x ∈ SimpleGraph.edgeSet (BergerLeightonGraph go fold ph hl hs)) Finset.univ }
:= λ ik ↦ ⟨Sym2.mk ik,by
  let Q := ik.2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at Q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold BergerLeightonGraph
  unfold SimpleGraph.edgeSet
  simp only [Set.le_eq_subset]
  unfold SimpleGraph.edgeSetEmbedding
  simp only [OrderEmbedding.coe_ofMapLEIff, Sym2.fromRel_proj_prop]
  exact Q.1
⟩

theorem edgeFunBL_surjective    {b l:ℕ} (go : Fin b → α → α) (fold : Fin l → (α)) (ph : Fin l → Bool)
(hl : ∀ a, ¬ nearby go a a)
(hs : Symmetric (λ a b ↦ nearby go a b))
: Function.Surjective (edgeFunBL go fold ph hl hs) := by
  intro x
  let hx₁ := x.2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₁
  unfold BergerLeightonGraph at hx₁
  unfold edgeFunBL
  let i := (Quot.out x.1).1
  let k := (Quot.out x.1).2
  by_cases hik: (i.1 < k.1)
  . exists ⟨Quot.out x.1,by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only at hx₁
      unfold SimpleGraph.edgeSet at hx₁
      simp only [Set.le_eq_subset] at hx₁
      unfold SimpleGraph.edgeSetEmbedding at hx₁
      simp only [OrderEmbedding.coe_ofMapLEIff] at hx₁
      let Q := @Sym2.fromRel_proj_prop (Fin l)
        (fun i k => pt_locF_BL go fold i k ph = true)
        (by
          unfold Symmetric
          intro x y h
          unfold pt_locF_BL at *
          simp only [Fin.val_fin_lt, Bool.and_eq_true] at *
          constructor
          tauto
          exact hs h.2
        ) (Quot.out x.1)
      have : x.1 = Sym2.mk (Quot.out x.1) := by exact (Quot.out_eq x.1).symm
      rw [← this] at Q
      rw [Q] at hx₁
      tauto
    ⟩
    simp only [Quot.out_eq, Subtype.coe_eta]
  . exists ⟨Prod.swap (Quot.out x.1),by
      simp only [Finset.mem_filter, Finset.mem_univ, Prod.fst_swap, Prod.snd_swap, true_and]
      simp only at hx₁
      unfold SimpleGraph.edgeSet at hx₁
      simp only [Set.le_eq_subset] at hx₁
      unfold SimpleGraph.edgeSetEmbedding at hx₁
      simp only [OrderEmbedding.coe_ofMapLEIff] at hx₁
      let Q := @Sym2.fromRel_proj_prop (Fin l)
        (fun i k => pt_locF_BL go fold i k ph = true)
        (by
          unfold Symmetric
          intro x y h
          unfold pt_locF_BL at *
          simp only [Fin.val_fin_lt, not_lt, Bool.and_eq_true] at *
          constructor
          tauto
          exact hs h.2
        ) (Quot.out x.1)
      have : x.1 = Sym2.mk (Quot.out x.1) := by exact (Quot.out_eq x.1).symm
      rw [← this] at Q
      rw [Q] at hx₁
      unfold pt_locF_BL at *
      simp only [Bool.and_eq_true, Fin.val_fin_lt, not_lt, Quot.out_eq] at *
      constructor
      tauto
      have : (Quot.out x.1).2 < (Quot.out x.1).1
        ∨ (Quot.out x.1).2 = (Quot.out x.1).1 := by exact lt_or_eq_of_le hik
      cases this with
      | inl h => exact h
      | inr h =>
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
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₁
  unfold ScoreGraph at hx₁
  unfold edgeFun
  let i := (Quot.out x.1).1
  let k := (Quot.out x.1).2
  by_cases hik: (i.1 < k.1)
  . exists ⟨Quot.out x.1,by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only at hx₁
      unfold SimpleGraph.edgeSet at hx₁
      simp only [Set.le_eq_subset] at hx₁
      unfold SimpleGraph.edgeSetEmbedding at hx₁
      simp only [OrderEmbedding.coe_ofMapLEIff] at hx₁
      let Q := @Sym2.fromRel_proj_prop (Fin l)
        (fun i k => pt_locF go fold i k ph = true ∨ pt_locF go fold k i ph = true)
        (by
          unfold Symmetric
          intro x y h
          tauto
        ) (Quot.out x.1)
      have : x.1 = Sym2.mk (Quot.out x.1) := by exact (Quot.out_eq x.1).symm
      rw [← this] at Q
      rw [Q] at hx₁
      cases hx₁ with
      | inl => tauto
      | inr h =>
        exfalso
        unfold pt_locF at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        let R := h.1.2
        have : k.1.succ < i.1 := R
        have : k.1.succ < k.1 := LT.lt.trans this hik
        contrapose this
        exact Nat.not_succ_lt_self
    ⟩
    simp only [Quot.out_eq, Subtype.coe_eta]
  . exists ⟨Prod.swap (Quot.out x.1),by
      simp only [Finset.mem_filter, Finset.mem_univ, Prod.fst_swap, Prod.snd_swap, true_and]
      simp only at hx₁
      unfold SimpleGraph.edgeSet at hx₁
      simp only [Set.le_eq_subset] at hx₁
      unfold SimpleGraph.edgeSetEmbedding at hx₁
      simp only [OrderEmbedding.coe_ofMapLEIff] at hx₁
      let Q := @Sym2.fromRel_proj_prop (Fin l)
        (fun i k => pt_locF go fold i k ph = true ∨ pt_locF go fold k i ph = true)
        (by
          unfold Symmetric
          intro x y h
          tauto
        ) (Quot.out x.1)
      have : x.1 = Sym2.mk (Quot.out x.1) := by exact (Quot.out_eq x.1).symm
      rw [← this] at Q
      rw [Q] at hx₁
      cases hx₁ with
      | inr => tauto
      | inl h =>
        exfalso
        unfold pt_locF at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        let R := h.1.2
        have : i.1.succ < i.1 := calc
          _ < k.1 := R
          _ ≤ _ := Nat.not_lt.mp hik
        contrapose this
        exact Nat.not_succ_lt_self
    ⟩
    simp

theorem edgeFunBL_injective    {b l:ℕ} (go : Fin b → α → α) (fold : Fin l → (α)) (ph : Fin l → Bool)
(hl : ∀ a, ¬ nearby go a a)
(hs : Symmetric (λ a b ↦ nearby go a b))
: Function.Injective (edgeFunBL go fold ph hl hs) := by
  intro ⟨x,Q₁⟩ ⟨y,Q₂⟩
  unfold edgeFunBL
  simp only [Subtype.mk.injEq, Sym2.eq, Sym2.rel_iff']
  intro h
  cases h with
  | inl h_1 => exact h_1
  | inr h_1 =>
    exfalso
    unfold pt_locF_BL at *
    simp only [Bool.not_eq_true, Bool.and_eq_true, Finset.mem_filter, Finset.mem_univ,
      true_and] at *
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
  simp only [Subtype.mk.injEq, Sym2.eq, Sym2.rel_iff']
  intro h
  cases h with
  | inl h_1 => exact h_1
  | inr h_1 =>
    exfalso
    unfold pt_locF at *
    simp only [Bool.and_eq_true, decide_eq_true_eq, Finset.mem_filter, Finset.mem_univ,
      true_and] at *
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

theorem points_tot_graph  {b l:ℕ} (go : Fin b → α → α) (fold : Fin l → (α)) (ph : Fin l → Bool)
:  (SimpleGraph.edgeFinset (ScoreGraph go fold ph)).card = points_totF go ph fold
:= by
  simp only [Set.toFinset_card, Fintype.card_ofFinset, Finset.filter_congr_decidable]
  unfold points_totF
  repeat rw [← Fintype.card_coe]
  have : Function.Bijective (edgeFun go fold ph) := by
    constructor
    exact edgeFun_injective go fold ph
    exact edgeFun_surjective go fold ph
  exact (Fintype.card_of_bijective this).symm

theorem points_tot_BL_graph  {b l:ℕ} (go : Fin b → α → α) (fold : Fin l → (α)) (ph : Fin l → Bool)
(hl : ∀ a, ¬ nearby go a a)
(hs : Symmetric (λ a b ↦ nearby go a b))
:  (SimpleGraph.edgeFinset (BergerLeightonGraph go fold ph hl hs)).card = points_tot_BL go ph fold
:= by
  simp only [Set.toFinset_card, Fintype.card_ofFinset, Finset.filter_congr_decidable]
  unfold points_tot_BL
  repeat rw [← Fintype.card_coe]
  have : Function.Bijective (edgeFunBL go fold ph hl hs) := by
    constructor
    exact edgeFunBL_injective go fold ph hl hs
    exact edgeFunBL_surjective go fold ph hl hs
  exact (Fintype.card_of_bijective this).symm

theorem bound_BL  {b l:ℕ} (go : Fin b → α → α) (fold : Fin l → (α)) (ph : Fin l → Bool)
(hl : ∀ a, ¬ nearby go a a)
(hs : Symmetric (λ a b ↦ nearby go a b))
: 2 * points_tot_BL go ph fold ≤ l * l := by
  rw [← points_tot_BL_graph go fold ph hl hs]
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
    simp only [Prod.mk.eta] at h
    exact SimpleGraph.Dart.ext d₁ d₂ h
  )
