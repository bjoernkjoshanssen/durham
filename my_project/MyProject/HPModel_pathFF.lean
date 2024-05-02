import MyProject.HPModelF

-- pathF' is like pathF but without the infinity
def pathF'  {α β:Type} [OfNat α 0] {l:ℕ} (go : β → α → α)
  (moves : Fin l → β): Fin l.succ → α := by
  induction l
  intro
  exact 0
  intro i
  rename_i n n_ih
  by_cases h : i.1 < n.succ
  exact                n_ih (λ j ↦ moves (Fin.castSucc j)) ⟨i.1,h⟩
  exact go (moves n)  (n_ih (λ j ↦ moves (Fin.castSucc j)) n)


def pathM {α β:Type} [OfNat α 0] {l:ℕ} (go : β → α → α)
  (moves : Fin l.succ → β) (i:Fin l.succ.succ) : α := --loop ⟨l.succ, Nat.lt.base l.succ⟩ where
  loop i where
  loop : Fin l.succ.succ → α
  | ⟨0, _⟩ => 0
  | ⟨i+1, h⟩ => go (moves ⟨i, Nat.succ_lt_succ_iff.mp h⟩) (loop ⟨i, Nat.le_of_lt h⟩ )

def morF {l:ℕ} -- 3/10/24
  {α:Type} [OfNat α 0] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁.succ)
  (go : Fin b₀ → α → α)
  (moves : Fin l.succ →  (Fin b₀))
  :        Fin l.succ → (Fin b₁.succ) := by
  induction l
  intro i
  have : i = 0 := Fin.eq_zero i
  subst this
  . exact f (moves 0) 0
  intro i
  let R := pathF' go moves ⟨i.1,Nat.lt.step i.2⟩
  exact f (moves i) R


theorem orderly_injective'M {l :ℕ} (i:Fin l.succ)
-- a success story for pathM, 3/18/2024.
-- still, not clear how to do sym_morfM
(moves : Fin l.succ.succ → (Fin 4)) (h: moves (Fin.castSucc i) = 0 ∧ moves (Fin.succ i) = 1) :
¬ Function.Injective (λ i ↦ (pathM rect moves) i) := by
  intro hc

  have h₀: rect 1 (rect 0 ((pathM rect moves) ⟨i.1, Nat.lt.step (Nat.lt.step i.2)⟩))
  = (pathM rect moves) ⟨i.1, Nat.lt.step (Nat.lt.step i.2)⟩ := by
    unfold rect
    have : rectMap 0 + rectMap 1 = 0 := by decide
    rw [← plane_assoc,this]
    simp
  have h₂: (pathM rect moves) ⟨i.1+2,by simp_rw [Nat.succ_eq_add_one];simp⟩
       = rect 1 ((pathM rect moves) ⟨i.1+1, Nat.succ_lt_succ (Nat.lt_add_right 1 i.2)⟩)
       := by
    unfold pathM pathM.loop
    rw [← h.2];
    exact rfl
  have h₁: (pathM rect moves) ⟨i.1+1, Nat.succ_lt_succ_iff.mpr (Nat.lt.step i.2)⟩
        = rect 0 ((pathM rect moves) ⟨i.1, Nat.lt.step (Nat.lt.step i.2)⟩)
    := by
    rw [← h.1];
    rfl
  have : (pathM rect moves) ⟨i.1, Nat.lt.step (Nat.lt.step i.2)⟩
       = (pathM rect moves) ⟨i.1+2,by simp_rw [Nat.succ_eq_add_one];simp⟩ := by
    rw [h₂, h₁, h₀]
  let Q := hc this
  simp at Q -- is not injective because equals at i and i+2. See orderly-injective.lean


lemma sym_morfF {α:Type} [OfNat α 0] {l b:ℕ} {go : Fin b.succ → α → α}
  (moves: Fin l.succ → Fin b.succ) (k : Fin l.succ.succ)
  (sym : α → α) (h0 : sym 0 = 0)
  -- This is a generalization of rotate_morfF and reflect_morfF, 3/18/2024.
  -- rotate_morfF finished 3/10/24. After generalizing, all of a sudden apply?
  -- suggested an easy proof.
  -- if we try this with pathF instead of pathF' then the dif_pos doesn't work
  (symIndex : Fin b.succ → Fin b.succ)
  (sym_basic : (u : α) → (c: Fin b.succ) → sym (go c u) = go (symIndex c) (sym u))
  :
  sym (pathF' go                 moves  k) =
      (pathF' go (morfF symIndex moves)) k
  := by
  induction l
  . -- zero
    cases Nat.of_le_succ (Fin.is_le k)

    . rename_i h
      have : k = 0 := Fin.le_zero_iff.mp h
      subst this;unfold pathF';
      simp only [Fin.val_zero, Nat.lt_succ_self,
        Nat.cast_zero, dite_eq_ite, ite_true, Nat.zero_eq]
      rw [h0]

    . rename_i h
      have : k = 1 := Fin.ext h
      subst this;unfold pathF'; simp only [Fin.val_one, lt_self_iff_false,
        Nat.cast_zero, dite_eq_ite, ite_false, Nat.zero_eq]
      rw [sym_basic, h0]
      rfl

  . -- succ
    rename_i n n_ih
    let Ri := n_ih (λ i ↦ moves (Fin.castSucc i))
    by_cases h : k.1 < n.succ.succ

    . -- pos
      have h₀: pathF' go                        moves                     k
             = pathF' go                 (λ i ↦ moves (Fin.castSucc i))  ⟨k.1,h⟩ := dif_pos h -- vindicating pathF'
      have h₁: pathF' go (morfF symIndex        moves)                    k
             = pathF' go (morfF symIndex (λ i ↦ moves (Fin.castSucc i))) ⟨k.1,h⟩
           := by unfold pathF'; simp only [Nat.zero_eq, Fin.cast_nat_eq_last,
             Fin.val_last, lt_self_iff_false, dite_false, Nat.rec_add_one];unfold morfF;rw [dif_pos h] -- apply? suggested: exact (dif_pos h).symm
      let R := Ri ⟨k.1,h⟩
      rw [h₀, h₁, ← R]
    . -- neg
      have h₀: k.1 = n.succ.succ := Nat.eq_of_lt_succ_of_not_lt k.2 h
      have : k = ⟨n.succ.succ, Nat.lt.base (Nat.succ (Nat.succ n))⟩
        := Fin.eq_mk_iff_val_eq.mpr h₀
      subst this

      simp only at h₀
      unfold pathF'
      simp only [lt_self_iff_false, Nat.zero_eq, Fin.cast_nat_eq_last, Fin.val_last,
        dite_false]
      repeat (rw [sym_basic])
      let R₁ := Ri ⟨n, Nat.lt.step (Nat.lt.base n)⟩
      unfold pathF' at R₁
      simp only [Nat.lt_succ_self, Nat.zero_eq, Fin.cast_nat_eq_last, dite_true] at R₁
      exact
        congrArg (go (symIndex (moves (Fin.last (Nat.succ n)))))
          (congrArg (go (symIndex (moves (Fin.castSucc (Fin.last n))))) R₁)

lemma rotate_morfF {l:ℕ} (moves: Fin l.succ → Fin 4) (k : Fin l.succ.succ):
  rotate (pathF' rect                  moves  k) =
         (pathF' rect (morfF rotateIndex moves)) k
:= sym_morfF moves k rotate rfl rotateIndex rotate_basic

lemma reflect_morfF {l:ℕ} (moves: Fin l.succ → Fin 4) (k : Fin l.succ.succ):
  reflect (pathF' rect                  moves  k) =
         (pathF' rect (morfF reflectIndex moves)) k
:= sym_morfF moves k reflect rfl reflectIndex reflect_basic

theorem rotate_preserves_pt_loc'F {l:ℕ}
-- completed 3/10/24 at the cost of adding ".succ" to l
  (moves : Fin l.succ → (Fin 4)) (i j : Fin l.succ.succ) (ph: Fin l.succ.succ → Bool)
  (hpt: pt_locF κ (pathF' rect             moves)  i j ph)
  :     pt_locF κ (pathF' rect (morfF rotateIndex moves)) i j ph
  := by
    unfold pt_locF at *
    simp only [Bool.and_eq_true, decide_eq_true_eq] at *
    let R := rotate_preserves_nearby hpt.2
    rw [rotate_morfF moves i, rotate_morfF moves j] at R
    tauto

theorem reflect_preserves_pt_loc'_morfF {l:ℕ}
  (moves : Fin l.succ → (Fin 4)) (i j : Fin l.succ.succ) (ph: Fin l.succ.succ → Bool)
  (hpt: pt_locF κ (pathF' κ             moves)  i j ph)
  :     pt_locF κ (pathF' κ (morfF reflectIndex moves)) i j ph
  := by
    unfold pt_locF at *
    simp only [Bool.and_eq_true, decide_eq_true_eq] at *
    constructor
    . tauto
    . repeat rw [← reflect_morfF moves]
      exact reflect_preserves_nearby hpt.2

theorem rotate_pts'_atF {l:ℕ} (k : Fin l.succ.succ)
  (ph    : Fin l.succ.succ → Bool)
  (moves : Fin l.succ → (Fin 4)):
  pts_at'F κ k ph (pathF' κ moves) ≤
  pts_at'F κ k ph (pathF' κ (morfF rotateIndex moves)) := by
  -- Completed March 10, 2024. The point of using pathF' and morfF here is to be able to combine
  -- with the work on "orderly".
  apply Finset.card_le_card
  intro i hi
  let Q :=  rotate_preserves_pt_loc'F moves i k ph
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
  tauto

theorem reflect_pts'_atF {l:ℕ} (k : Fin l.succ.succ)
  (ph    : Fin l.succ.succ → Bool)
  (moves : Fin l.succ → (Fin 4)):
  -- 3/10/24
  pts_at'F κ k ph (pathF' κ moves) ≤
  pts_at'F κ k ph (pathF' κ (morfF reflectIndex moves)) := by
  apply Finset.card_le_card
  intro i hi
  let Q :=  reflect_preserves_pt_loc'_morfF moves i k ph
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
  tauto

theorem rotate_pts_totF
  -- 3/10/24. Combine with "orderly" work
  {l:ℕ} (ph : Fin l.succ.succ → Bool) (moves : Fin l.succ → (Fin 4)):
  pts_tot'F κ ph (pathF' κ moves) ≤
  pts_tot'F κ ph (pathF' κ (morfF rotateIndex moves))
  := by
    unfold pts_tot'F
    apply Finset.sum_le_sum
    intro k
    intro
    exact rotate_pts'_atF k ph moves

theorem reflect_pts_tot_morfF
  {l:ℕ} (ph : Fin l.succ.succ → Bool) (moves : Fin l.succ → (Fin 4)):
  pts_tot'F κ ph (pathF' κ moves) ≤
  pts_tot'F κ ph (pathF' κ (morfF reflectIndex moves))
  -- 3/8/24
  := by
    unfold pts_tot'F
    apply Finset.sum_le_sum
    intro k
    intro
    exact reflect_pts'_atF k ph moves

/-- We can assume a walk starts by going right (indicated by `0`).-/
theorem towards_orderlyishF
-- 3/10/24. Note some "simp" uses are unnecessary when using pathF', morfF
  {l:ℕ} (ph : Fin l.succ.succ → Bool)(moves : Fin l.succ → (Fin 4)):
  ∃ moves' : Fin l.succ → (Fin 4), moves' 0 = 0 ∧
  pts_tot'F κ ph (pathF' κ moves) ≤
  pts_tot'F κ ph (pathF' κ moves')
  := by
  let m₀ := moves
  let m₁ := (morfF rotateIndex m₀)
  let m₂ := (morfF rotateIndex m₁)
  let m₃ := (morfF rotateIndex m₂)

  cases rotate_until_right (m₀ 0)
  . exists m₀
  . rename_i h
    cases h
    . exists m₁
      rename_i h_1
      constructor
      . rw [← h_1, rotate_headF]
      . exact rotate_pts_totF ph m₀
    . rename_i h_1
      cases h_1
      . exists m₂
        rename_i h
        constructor
        . rw [← h];repeat rw[rotate_headF]
        . calc
              pts_tot'F κ ph (pathF' κ m₀)
            ≤ pts_tot'F κ ph (pathF' κ m₁) := rotate_pts_totF ph m₀
          _ ≤ pts_tot'F κ ph (pathF' κ m₂) := rotate_pts_totF ph m₁
      . exists m₃
        rename_i h
        constructor
        . rw [← h];repeat rw[rotate_headF]
        . calc
          pts_tot'F κ ph (pathF' κ m₀) ≤ pts_tot'F κ ph (pathF' κ m₁) := rotate_pts_totF ph m₀
          _                            ≤ pts_tot'F κ ph (pathF' κ m₂) := rotate_pts_totF ph m₁
          _                            ≤ _                            := rotate_pts_totF ph m₂

theorem towards_orderlyF
  {l:ℕ} (ph : Fin l.succ.succ → Bool)(moves : Fin l.succ → (Fin 4)):
  ∃ moves', moves' 0 = 0 ∧
  (∀ j, (∀ i, i < j → moves' i = 0 ∨ moves' i = 1) → moves' j ≠ 3) ∧
  pts_tot'F κ ph (pathF' κ moves) ≤
  pts_tot'F κ ph (pathF' κ moves')
  -- completed 3/10/24.
  := by
  obtain ⟨moves₀,hmoves₀⟩ := towards_orderlyishF ph moves
  by_cases h₃: (∀ j, (∀ i, i < j → moves₀ i = 0 ∨ moves₀ i = 1) → moves₀ j ≠ 3)
  . exists moves₀
    . tauto
  . exists (morfF reflectIndex moves₀)
    constructor
    . unfold reflectIndex morfF; simp only;rw [hmoves₀.1];rfl

    . constructor
      . intro j₁ hj₁;
        have : ∃ (j : Fin (l + 1)),
          (∀ i < j, moves₀ i = 0 ∨ moves₀ i = 1) ∧ moves₀ j = 3 := by
            contrapose h₃; simp only [ne_eq, not_forall, not_not, exists_prop,
            not_exists, not_and];intro x hx;contrapose h₃; simp only [not_exists,
              not_and, not_forall, not_not, exists_prop];
            simp only [not_not] at h₃ ;exists x
        obtain ⟨j,hj⟩ := this
        by_cases h : j₁ < j
        -- now it's easy using morfF
        cases hj.1 j₁ h
        . rename_i h_1;intro hc;unfold morfF at hc;rw [h_1] at hc;contrapose hc;decide
        . rename_i h_1;intro hc;unfold morfF at hc;rw [h_1] at hc;contrapose hc;decide
        by_cases he : j₁ = j
        . unfold morfF reflectIndex
          rw [he, hj.2];decide

        . have : j < j₁ ∨ j = j₁ ∨ j₁ < j := lt_trichotomy j j₁
          have : j < j₁ := by tauto
          cases (hj₁ j this)
          . rename_i h_1;unfold morfF at h_1;rw [hj.2] at h_1;contrapose h_1;decide
          . rename_i h_1;unfold morfF at h_1;rw [hj.2] at h_1;contrapose h_1;decide
      . calc
        _ ≤ pts_tot'F κ ph (pathF' κ moves₀) := hmoves₀.2
        _ ≤ _                                := reflect_pts_tot_morfF ph moves₀
