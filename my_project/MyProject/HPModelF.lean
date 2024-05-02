import MyProject.HydrophobicPolarModel

open BigOperators

def pt_locF {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
 {l : ℕ} (fold : Fin l → α) (i j : Fin l) (phobic : Fin l → Bool) : Bool
:=  phobic i && phobic j && i.1.succ < j.1 && nearby go (fold i) (fold j)

def pts_at'F {α:Type} {β : Type} [Fintype β] (go : β → α → α)
  [DecidableEq α] {l:ℕ} (k : Fin l) (ph : Fin l → Bool) (fold : Fin l → α) : ℕ :=
  Finset.card (
    Finset.filter (λ i : Fin l ↦ (pt_locF go fold i k ph))
    Finset.univ
  )



def change_typeF  {α:Type} {β : Type} [Fintype β] (go : β → α → α)
[DecidableEq α] {l:ℕ} (k : Fin l) (ph : Fin l → Bool) (fold : Fin l → α):
Finset.filter (λ i : Fin l ↦ (pt_locF go fold i k ph)) Finset.univ
→
Finset.filter (λ i : Fin k ↦ (pt_locF go fold (Fin_trans i) k ph)) Finset.univ
  := by
    intro ip; let Q := ip.2; rw [Finset.mem_filter] at Q -- Finset.mem_filter was key here
    unfold pt_locF at Q;
    have : ip.1.1.succ < k := by
      simp only [Finset.mem_univ, Bool.and_eq_true, decide_eq_true_eq, true_and] at Q ;tauto
    exact ⟨⟨ip.1.1,Nat.lt_of_succ_lt this⟩,by
      rw [Finset.mem_filter]; simp only [Finset.mem_univ,
      true_and];tauto
    ⟩

theorem change_type_cardF  {α:Type} {β : Type} [Fintype β] (go : β → α → α)
  [DecidableEq α] {l:ℕ} (k : Fin l) (ph : Fin l → Bool) (fold : Fin l → α):
Fintype.card (Finset.filter (λ i : Fin l ↦ (pt_locF go fold i k ph)) Finset.univ)
=
Fintype.card (Finset.filter (λ i : Fin k ↦ (pt_locF go fold (Fin_trans i) k ph)) Finset.univ)
:= by
  suffices Function.Bijective (change_typeF go k ph fold) by
    apply Fintype.card_of_bijective; exact this
  constructor
  intro i₁ i₂ hi; unfold change_typeF at hi; simp only [Subtype.mk.injEq,
    Fin.mk.injEq] at hi
  exact SetCoe.ext (Fin.ext hi)
  intro i; let Q := i.2; rw [Finset.mem_filter] at Q
  exists ⟨
    (Fin_trans i),
    by rw [Finset.mem_filter]; constructor; simp only [Finset.mem_univ]; exact Q.2
  ⟩

theorem pt_loc_of_embedsF
 {α:Type} [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
 {l:ℕ}
  (fold : Fin l → α) (a b : Fin l) (phobic : Fin l → Bool)
  (htri: pt_locF go₀ fold a b phobic) :
         pt_locF go₁ fold a b phobic := by
  unfold pt_locF at *; simp only [Bool.and_eq_true, decide_eq_true_eq] at *; constructor; tauto; exact nearby_of_embeds h_embed htri.2

theorem pts_at_of_embeds'F {α:Type} [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
{l:ℕ} (k:Fin l) (ph : Fin l → Bool) (fold : Fin l → α):
pts_at'F go₀ k ph fold ≤
pts_at'F go₁ k ph fold := by
  unfold pts_at'F; apply Finset.card_le_card; intro a ha;
  simp only [Finset.mem_filter, Finset.mem_univ, true_and];
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  exact pt_loc_of_embedsF h_embed fold a k ph ha

def pts_tot'F {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
 {l:ℕ} (ph : Fin l → Bool)(fold : Fin l → α)
  := ∑ i : Fin l, pts_at'F go i ph fold

theorem pts_bound_of_embeds'F {α:Type} [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
{l:ℕ} (ph : Fin l → Bool) (fold : Fin l → α):
pts_tot'F go₀ ph fold ≤
pts_tot'F go₁ ph fold := by
  unfold pts_tot'F; apply Finset.sum_le_sum; intros; exact pts_at_of_embeds'F h_embed _ _ _

def pts_atF {α:Type} {β : Type} [Fintype β] (go : β → α → α)
[DecidableEq α] {l:ℕ} (k : Fin l) (ph : Fin l → Bool) (fold : Fin l → α) : ℕ :=
  Finset.card (
    Finset.filter (λ i : Fin k ↦ (pt_locF go fold (Fin_trans i) k ph))
    Finset.univ
  )

theorem pts_at_eq_pts_at'F  {α:Type} {β : Type} [Fintype β] (go : β → α → α)
[DecidableEq α] {l:ℕ} (k : Fin l) (ph : Fin l → Bool) (fold : Fin l → α):
pts_atF go k ph fold = pts_at'F go k ph fold := by
unfold pts_atF pts_at'F; (repeat rw [← Fintype.card_coe]);
exact (change_type_cardF go k ph fold).symm

lemma pts_at_bound'F {α:Type} [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α)
{l:ℕ} (ph : Fin l → Bool) (fold : Fin l → α) (i:Fin l):
pts_at'F go i ph fold ≤ i := by
  rw [← pts_at_eq_pts_at'F, ← Finset.card_fin i.1];
  apply Finset.card_le_card; apply Finset.filter_subset

theorem pts_earned_bound_loc'F {α:Type} [DecidableEq α] {β : Type} [Fintype β] (go : β → α → α)
{l:ℕ} (ph : Fin l.succ → Bool) (fold : Fin l.succ → α):
pts_tot'F go ph fold ≤ l.succ * l / 2 := by
  suffices pts_tot'F go ph fold ≤ ∑ j : Fin l.succ, j.1 by calc
    _ ≤ ∑ j : Fin l.succ, j.1 := this
    _ = _                     := Fin_sum_range _
  unfold pts_tot'F; apply Finset.sum_le_sum; intro i; intro; exact pts_at_bound'F go ph fold i


section Global_orderliness
/-- April 3, 2024: A better approach to orderliness?
We might define `def isPath {l:ℕ} (fold : Fin l.succ → ℤ×ℤ) := ∀ i : Fin l,  ∃ a, fold i.succ = rect a (fold (Fin.castSucc i))`
but the following is more constructive.-/
def isPathWitness
 {α:Type} [DecidableEq α] {β : Type} [Fintype β] (go : β → α → α)
 {l:ℕ} (fold : Fin l.succ → α) :=
  (i : Fin l) →
  { a : β // fold i.succ = go a (fold (Fin.castSucc i))}

def rotate_pts₁ {l: ℕ} (ph : Fin l.succ.succ → Bool)
                     (fold : Fin l.succ.succ → ℤ × ℤ)
                        (j : Fin l.succ.succ) :
    { i_1 // pt_locF rect fold                       i_1 j ph = true }
  → { i_1 // pt_locF rect (fun i => rotate (fold i)) i_1 j ph = true }
    := (λ x ↦ ⟨x.1,by
      let Q := x.2;
      unfold pt_locF at *; simp only [Bool.and_eq_true, decide_eq_true_eq];
      simp only [Bool.and_eq_true, decide_eq_true_eq] at Q
      rw [rotate_preserves_nearby Q.2];
      tauto
    ⟩)

def reflect_pts₁
{l: ℕ}
(ph: Fin l.succ.succ → Bool)
(fold: Fin l.succ.succ → ℤ × ℤ)
(j:Fin l.succ.succ) :
    { i_1 // pt_locF rect fold                       i_1 j ph = true }
  → { i_1 // pt_locF rect (fun i => reflect (fold i)) i_1 j ph = true }
    := (λ x ↦ ⟨x.1,by
      unfold pt_locF; simp only [Bool.and_eq_true, decide_eq_true_eq]
      let Q := x.2;unfold pt_locF at Q; simp only [Bool.and_eq_true,
        decide_eq_true_eq] at Q
      rw [reflect_preserves_nearby];tauto
      tauto
    ⟩)

theorem reflect_pts₁_bijective
{l: ℕ}
(ph: Fin l.succ.succ → Bool)
(fold: Fin l.succ.succ → ℤ × ℤ)
(i:Fin l.succ.succ)
 : Function.Bijective (reflect_pts₁ ph fold i) := by
      constructor
      intro x y hxy
      unfold reflect_pts₁ at hxy
      simp only [Subtype.mk.injEq] at hxy
      exact SetCoe.ext hxy

      intro x
      exists ⟨x.1,by
        let Q := x.2;unfold pt_locF at Q; simp only [Bool.and_eq_true,
          decide_eq_true_eq] at Q
        unfold pt_locF; simp only [Bool.and_eq_true, decide_eq_true_eq]
        have : nearby rect (fold x.1) (fold i) = true := by
          apply reflect_preserves_nearby_converse;exact Q.2
        tauto
      ⟩

theorem rotate_pts₁_bijective
{l: ℕ}
(ph: Fin l.succ.succ → Bool)
(fold: Fin l.succ.succ → ℤ × ℤ)
(i:Fin l.succ.succ)
 : Function.Bijective (rotate_pts₁ ph fold i) := by
      constructor
      intro x y hxy
      unfold rotate_pts₁ at hxy
      simp only [Subtype.mk.injEq] at hxy
      exact SetCoe.ext hxy

      intro x
      exists ⟨x.1,by
        let Q := x.2;unfold pt_locF at Q; simp only [Bool.and_eq_true,
          decide_eq_true_eq] at Q
        unfold pt_locF; simp only [Bool.and_eq_true, decide_eq_true_eq]
        have : nearby rect (fold x.1) (fold i) = true := by
          apply rotate_preserves_nearby_converse;exact Q.2
        tauto
      ⟩

def rotate_pts₂ {l: ℕ}
(ph: Fin l.succ.succ → Bool)
(fold: Fin l.succ.succ → ℤ × ℤ)
(j:Fin l.succ.succ) :
  { i_1 // pt_locF rect fold                                i_1 j ph = true }
→ { i_1 // pt_locF rect (fun i => rotate (rotate (fold i))) i_1 j ph = true }
    := (λ x ↦ ⟨x.1,by
      unfold pt_locF; simp only [Bool.and_eq_true, decide_eq_true_eq]
      let Q := x.2;unfold pt_locF at Q; simp only [Bool.and_eq_true,
        decide_eq_true_eq] at Q
      repeat rw [rotate_preserves_nearby];tauto
    ⟩)

theorem rotate_pts₂_bijective
{l: ℕ}
(ph: Fin l.succ.succ → Bool)
(fold: Fin l.succ.succ → ℤ × ℤ)
(i:Fin l.succ.succ)
: Function.Bijective (rotate_pts₂ ph fold i) := by
      constructor
      intro x y hxy
      unfold rotate_pts₂ at hxy
      simp only [Subtype.mk.injEq] at hxy
      exact SetCoe.ext hxy

      intro x
      exists ⟨x.1,by
        let Q := x.2;unfold pt_locF at Q; simp only [Bool.and_eq_true,
          decide_eq_true_eq] at Q
        unfold pt_locF; simp only [Bool.and_eq_true, decide_eq_true_eq]
        have : nearby rect (fold x.1) (fold i) = true := by
          apply rotate_preserves_nearby_converse
          apply rotate_preserves_nearby_converse
          exact Q.2
        tauto
      ⟩

def rotate_pts₃
 {l: ℕ}
(ph: Fin l.succ.succ → Bool)
(fold: Fin l.succ.succ → ℤ × ℤ)
(j:Fin l.succ.succ) :

          { i_1 // pt_locF rect fold                       i_1 j ph = true }
        → { i_1 // pt_locF rect (fun i => rotate (rotate (rotate (fold i)))) i_1 j ph = true }
    := (λ x ↦ ⟨x.1,by
      unfold pt_locF; simp only [Bool.and_eq_true, decide_eq_true_eq]
      let Q := x.2;unfold pt_locF at Q; simp only [Bool.and_eq_true,
        decide_eq_true_eq] at Q
      rw [rotate_preserves_nearby];tauto
      repeat rw [rotate_preserves_nearby]
      tauto
    ⟩)

theorem rotate_pts₃_bijective
{l: ℕ}
(ph: Fin l.succ.succ → Bool)
(fold: Fin l.succ.succ → ℤ × ℤ)
(i:Fin l.succ.succ)
 : Function.Bijective (rotate_pts₃ ph fold i) := by
      constructor
      intro x y hxy
      unfold rotate_pts₃ at hxy
      simp only [Subtype.mk.injEq] at hxy
      exact SetCoe.ext hxy

      intro x
      exists ⟨x.1,by
        let Q := x.2;unfold pt_locF at Q; simp only [Bool.and_eq_true,
          decide_eq_true_eq] at Q
        unfold pt_locF; simp only [Bool.and_eq_true, decide_eq_true_eq]
        have : nearby rect (fold x.1) (fold i) = true := by
          apply rotate_preserves_nearby_converse;
          apply rotate_preserves_nearby_converse;
          apply rotate_preserves_nearby_converse;
          exact Q.2
        tauto
      ⟩

theorem reflect_pts_at'F
{l: ℕ}
(ph: Fin l.succ.succ → Bool)
(fold: Fin l.succ.succ → ℤ × ℤ)
       : ∀ i,
        pts_at'F rect i ph fold =
        pts_at'F rect i ph (fun i => reflect (fold i)) := by
          intro i;unfold pts_at'F;repeat rw [← Fintype.card_coe]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; apply Fintype.card_of_bijective (reflect_pts₁_bijective _ _ _)


theorem rotate_pts_at'F -- can use this to give a new proof of rotate_pts'_atᵥ ?
{l: ℕ}
(ph: Fin l.succ.succ → Bool)
(fold: Fin l.succ.succ → ℤ × ℤ)
       : ∀ i,
        pts_at'F rect i ph fold =
        pts_at'F rect i ph (fun i => rotate (fold i)) := by
          intro i;unfold pts_at'F;repeat rw [← Fintype.card_coe]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; apply Fintype.card_of_bijective (rotate_pts₁_bijective _ _ _)

theorem rotate₂_pts_at'F
{l: ℕ}
(ph: Fin l.succ.succ → Bool)
(fold: Fin l.succ.succ → ℤ × ℤ)
       : ∀ i,
        pts_at'F rect i ph fold =
        pts_at'F rect i ph (fun i => rotate (rotate (fold i))) := by
          intro i;unfold pts_at'F;repeat rw [← Fintype.card_coe]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; apply Fintype.card_of_bijective (rotate_pts₂_bijective _ _ _)

theorem rotate₃_pts_at'F
{l: ℕ}
(ph: Fin l.succ.succ → Bool)
(fold: Fin l.succ.succ → ℤ × ℤ)
       : ∀ i,
        pts_at'F rect i ph fold =
        pts_at'F rect i ph (fun i => rotate (rotate (rotate (fold i)))) := by
          intro i;unfold pts_at'F;repeat rw [← Fintype.card_coe]; simp only [Finset.mem_filter,
            Finset.mem_univ, true_and]
          apply Fintype.card_of_bijective (rotate_pts₃_bijective _ _ _)

/-- For some reason this is not needed below.-/
theorem global_orderliness_rotate {l:ℕ} (ph : Fin l.succ.succ → Bool)
(fold : Fin l.succ.succ → ℤ×ℤ) (f : isPathWitness rect fold)
: ∃ fold', ∃ _ : isPathWitness rect fold',
  pts_tot'F rect ph fold = pts_tot'F rect ph fold'
  ∧
  fold' 1 = rect 0 (fold' 0)
 := by
  cases rotate_until_right (f 0) with -- 0
  | inl h =>
    exists fold;exists f; simp only [true_and];
    let Q := (f 0).2; simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero] at Q
    rw [h] at Q;exact Q
  | inr h =>
    cases h with -- 1
    | inl h_1 =>
      exists (λ i ↦ rotate (fold i))
      exists (λ i ↦ ⟨rotateIndex (f i),by rw [← rotate_basic,← (f i).2]⟩)
      constructor
      . unfold pts_tot'F;rw [funext (rotate_pts_at'F _ _)]
      . let Q := (f 0).2; simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero] at Q ;
        simp only;rw [Q];(repeat rw [rotate_basic]);congr
    | inr h_1 =>
      cases h_1 with -- 2, 3
      | inl =>
        exists (λ i ↦ rotate (rotate (fold i)))
        exists (λ i ↦ ⟨rotateIndex (rotateIndex (f i)),by
          (repeat rw [← rotate_basic]);rw [← (f i).2]
        ⟩)
        constructor
        . unfold pts_tot'F;rw [funext (rotate₂_pts_at'F _ _)]
        . let Q := (f 0).2; simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero] at Q ;congr;
          simp only;rw [Q];repeat rw [rotate_basic]
          congr
      | inr h =>
        exists (λ i ↦ rotate (rotate (rotate (fold i))))
        exists (λ i ↦ ⟨rotateIndex (rotateIndex (rotateIndex (f i))),by
          (repeat rw [← rotate_basic]);rw [← (f i).2]
        ⟩)
        constructor
        . unfold pts_tot'F;rw [funext (rotate₃_pts_at'F _ _)]
        . let Q := (f 0).2; simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero] at Q ;
          simp only;rw [Q];repeat rw [rotate_basic]
          rw [h]

/-- The global perspective makes this easy.-/
lemma global_orderliness_noninjective {l:ℕ}
(fold : Fin l.succ.succ → ℤ×ℤ) (f : isPathWitness rect fold) (k : Fin l)
: (f (Fin.castSucc k)).1 = 0 → (f (Fin.succ k)).1 = 1 → ¬ Function.Injective fold
 := by
  have hcomm: Fin.succ (Fin.castSucc k)
    = Fin.castSucc (Fin.succ k) := by exact rfl
  have hcanc: ∀ x, rect 1 (rect 0 x) = x := by
    intro x;show x + (1,0) + (-1,0) = x;apply Prod.ext; simp only [Prod.fst_add,
      add_neg_cancel_right];
    simp only [Prod.snd_add, add_zero]
  intro h₀ h₁ hc
  let Q₀ := (f (Fin.castSucc k)).2
  rw [h₀,hcomm] at Q₀
  let Q₁ := (f (Fin.succ k)).2
  rw [h₁,Q₀,hcanc _] at Q₁
  have : k.1.succ.succ = k.1 := by exact Fin.mk_eq_mk.mp (hc Q₁)
  linarith

/-- If `fold` starts with a `0` and the first nonzero is a `3`
 then there's another `fold'` that starts with a `0` and the first nonzero is a `2`.
 Namely, apply `reflect`. -/
lemma global_orderliness_2_of_3 {l:ℕ} (ph : Fin l.succ.succ → Bool)
(fold : Fin l.succ.succ → ℤ×ℤ) (f : isPathWitness rect fold)
(h_inj : Function.Injective fold)
(i : Fin l) (hi : (f (Fin.succ i)).1 = 3 ∧ ∀ j, j.1 ≤ i.1 → (f j).1 = 0)

: ∃ fold', ∃ f' : isPathWitness rect fold',
  pts_tot'F rect ph fold = pts_tot'F rect ph fold'
  ∧
  (f' (Fin.succ i)).1 = 2 ∧ (∀ j, j.1 ≤ i.1 → (f' j).1 = 0)
  ∧ Function.Injective fold' := by
  exists (λ i ↦ reflect (fold i))
  exists (λ i ↦ ⟨reflectIndex (f i),by rw [← reflect_basic,← (f i).2]⟩)
  constructor
  unfold pts_tot'F;rw [funext (reflect_pts_at'F _ _)]
  constructor
  simp only
  rw [hi.1]
  rfl
  constructor
  intro j hj
  simp only
  let Q := hi.2 j hj
  rw [Q]
  rfl
  intro x y hxy
  simp only at hxy
  apply reflect_injective at hxy
  exact h_inj hxy

lemma global_orderliness_reflect_2_of_nonzero {l:ℕ} (ph : Fin l.succ.succ → Bool)
(fold : Fin l.succ.succ → ℤ×ℤ) (f : isPathWitness rect fold)
(h_inj : Function.Injective fold)
(i : Fin l) (hi : (f (Fin.succ i)).1 ≠ 0 ∧ ∀ j, j.1 ≤ i.1 → (f j).1 = 0)

: ∃ fold', ∃ f' : isPathWitness rect fold',
  pts_tot'F rect ph fold = pts_tot'F rect ph fold'
  ∧
  (f' (Fin.succ i)).1 = 2 ∧ (∀ j, j.1 ≤ i.1 → (f' j).1 = 0)
  ∧ Function.Injective fold' := by
  have : (f (Fin.succ i)).1 = 0 ∨
    (f (Fin.succ i)).1 = 1 ∨
    (f (Fin.succ i)).1 = 2 ∨
    (f (Fin.succ i)).1 = 3 := four_choices _
  cases this with
  | inl => exfalso; tauto
  | inr h =>
    cases h with
    | inl =>
      have : (f (Fin.castSucc i)).1 = 0 := hi.2 (Fin.castSucc i) (le_refl _)
      let Q := global_orderliness_noninjective fold f i
      tauto
    | inr h_1 =>
      cases h_1 with
      | inl   => exists fold; exists f; tauto
      | inr h => exact global_orderliness_2_of_3 ph fold f h_inj i (And.intro h hi.2)

lemma global_orderliness_injective {l:ℕ} (ph : Fin l.succ.succ → Bool)
(fold : Fin l.succ.succ → ℤ×ℤ) (f : isPathWitness rect fold)
(h_inj : Function.Injective fold)
: ∃ fold', ∃ _ : isPathWitness rect fold',
  pts_tot'F rect ph fold = pts_tot'F rect ph fold'
  ∧
  fold' 1 = rect 0 (fold' 0)
  ∧
  Function.Injective fold'
 := by
  cases rotate_until_right (f 0) with -- 0
  | inl h =>
    exists fold;exists f; simp only [true_and];let Q := (f 0).2;
    simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero] at Q
    rw [h] at Q;
    constructor
    exact Q
    exact h_inj
  | inr h =>
    cases h with -- 1
    | inl =>
      exists (λ i ↦ rotate (fold i))
      exists (λ i ↦ ⟨rotateIndex (f i),by rw [← rotate_basic,← (f i).2]⟩)
      constructor
      . unfold pts_tot'F;rw [funext (rotate_pts_at'F _ _)]
      . let Q := (f 0).2; simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero] at Q ;
        simp only;rw [Q];(repeat rw [rotate_basic]);
        constructor
        congr
        intro x y hxy
        simp only at hxy
        exact h_inj (rotate_injective hxy)
    | inr h_1 =>
      cases h_1 with -- 2, 3
      | inl =>
        exists (λ i ↦ rotate (rotate (fold i)))
        exists (λ i ↦ ⟨rotateIndex (rotateIndex (f i)),by
          (repeat rw [← rotate_basic]);rw [← (f i).2]
        ⟩)
        constructor
        . unfold pts_tot'F;rw [funext (rotate₂_pts_at'F _ _)]
        . let Q := (f 0).2; simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero] at Q ;congr;
          simp only;rw [Q];repeat rw [rotate_basic]
          constructor
          congr
          intro x y hxy
          simp only at hxy
          exact h_inj (rotate_injective (rotate_injective hxy))
      | inr h =>
        exists (λ i ↦ rotate (rotate (rotate (fold i))))
        exists (λ i ↦ ⟨rotateIndex (rotateIndex (rotateIndex (f i))),by
          (repeat rw [← rotate_basic]);rw [← (f i).2]
        ⟩)
        constructor
        . unfold pts_tot'F;rw [funext (rotate₃_pts_at'F _ _)]
        . let Q := (f 0).2;simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero] at Q ;
          simp only;rw [Q];repeat rw [rotate_basic]
          constructor
          rw [h]
          intro x y hxy
          simp only at hxy
          exact h_inj (rotate_injective (rotate_injective (rotate_injective hxy)))

theorem global_orderliness_reflect {l:ℕ} (ph : Fin l.succ.succ → Bool)
(fold : Fin l.succ.succ → ℤ×ℤ) (f : isPathWitness rect fold)
(h_inj : Function.Injective fold)
: ∃ fold', Function.Injective fold'
  ∧ pts_tot'F rect ph fold = pts_tot'F rect ph fold'
  ∧
  ∃ f' : isPathWitness rect fold',
  (f' 0).1 = 0 ∧
  ((∃ i, (f' (Fin.succ i)).1 ≠ 0 ∧ ∀ j, j.1 ≤ i.1 → (f' j).1 = 0) →
   (∃ i, (f' (Fin.succ i)).1 = 2 ∧ ∀ j, j.1 ≤ i.1 → (f' j).1 = 0))
  := by
  -- let fold'' be as obtained in `global_orderliness_injective`.
  -- then, if the antecedent holds, let fold' be as in `global_orderliness_reflect_stronger`.
  obtain ⟨fold'', hfold''⟩ := global_orderliness_injective ph fold f h_inj
  obtain ⟨f'',hf''⟩ := hfold''
  by_cases then_if : (∃ i, (f'' (Fin.succ i)).1 ≠ 0 ∧ ∀ j, j.1 ≤ i.1 → (f'' j).1 = 0)
  . obtain ⟨i₀,hi₀⟩ := then_if
    obtain ⟨fold',hfold'⟩ := global_orderliness_reflect_2_of_nonzero ph fold'' f'' (hf''.2.2) i₀ hi₀
    obtain ⟨f',hf'⟩ := hfold'
    exists fold'
    constructor
    -- injective:
    exact hf'.2.2.2
    constructor
    -- pts_tot
    let A := hf''.1
    let B := hf'.1
    exact Eq.trans A B
    exists f'


    constructor

    exact hf'.2.2.1 0 (by simp only [Fin.val_zero, zero_le])

    intro h
    exists i₀
    tauto

  . exists fold''
    constructor
    exact hf''.2.2
    constructor
    -- pts_tot
    exact hf''.1
    exists f''
    constructor
    . unfold isPathWitness at f'' -- this is awkward because the "wrong" thing was proved before
      let Q := (f'' 0).2
      let R := hf''.2.1
      simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero] at Q R
      rw [Q] at R
      apply left_injective_rect at R
      exact R
    . intro h;exfalso;contrapose then_if;simp only [ne_eq, not_exists, not_and, not_forall,
      exists_prop, not_not];tauto

end Global_orderliness
