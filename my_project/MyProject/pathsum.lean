import MyProject.HPModelF

/--! The idea here is to use the inherent sum structure of ℤ×ℤ to avoid inductively defined "path".
-/

def pth -- "path"
 {α:Type} [AddCommMonoid α] [DecidableEq α] {β : Type} [Fintype β] (goMap : β → α)
   {l : ℕ} (moves : Fin l → β) : Fin l.succ → α :=
  λ i ↦ Finset.sum Finset.univ (
    λ (j : Fin i) ↦ (goMap (moves (⟨j.1, Fin.val_lt_of_le j (Fin.is_le i)⟩)))
  )

#eval pth rectMap ![0,0,0] 0
#eval pth rectMap ![0,0,0] 1
#eval pth rectMap ![0,0,0] 2
#eval pth rectMap ![0,0,0] 3

-- Now we can cycle through "moves" and prove things about "pth" without any induction
-- Only problem is it only works for rect, hex, not for tri


def ptdir {α:Type} [DecidableEq α] [AddCommMonoid α] {β : Type} [Fintype β]
(goMap : β → α)
 {l:ℕ}  (moves: Fin l → β) (ph : Fin l.succ → Bool) (j : Fin l.succ)
: β → Fin l.succ → Prop  := λ a i ↦ ph i ∧ ph j ∧ i.1.succ < j.1 ∧
  pth goMap moves j = goMap a + pth goMap moves i

def nearBy {α β : Type} [DecidableEq α] [AddCommMonoid α] [Fintype β] (goMap : β → α)
  (p q : α) : Bool := ∃ a : β, q = goMap a + p

def ptloc {α β : Type} [DecidableEq α] [AddCommMonoid α] [Fintype β] (goMap : β → α)
 {l : ℕ} (fold : Fin l → α) (i j : Fin l) (phobic : Fin l → Bool) : Bool
:=  phobic i && phobic j && i.1.succ < j.1 && nearBy goMap (fold i) (fold j)

-- #print ptdir

instance  {α:Type} [DecidableEq α] [AddCommMonoid α] {β : Type} [Fintype β] (goMap : β → α)
 {l:ℕ} (j : Fin l.succ) (moves: Fin l → β) (ph : Fin l.succ → Bool) (a:β) (i:Fin l.succ)
 : Decidable (ptdir goMap moves ph j a i) := by
  unfold ptdir
  exact And.decidable

#eval ptdir rectMap ![0,2,1] ![true,true,true,true] 3 2 0 -- true

-- Now we replicate some results for pathᵥ for pathsum:
theorem uniqueloc  {α: Type} [AddCommGroup α] [DecidableEq α] {β: Type} [Fintype β]
  {goMap: β → α}
  {l:ℕ} {j: Fin l.succ}
  {moves: Fin l → β} {ph : Fin l.succ → Bool}
  (path_inj: Function.Injective (λ k : Fin l.succ ↦ (pth goMap moves) k))
  (a : β) (i₀ i₁ : Fin l.succ)
  (hai₀ : ptdir goMap moves ph j a i₀)
  (hai₁ : ptdir goMap moves ph j a i₁)
  :
  i₀ = i₁
  := by
    let R := Eq.trans hai₀.2.2.2.symm hai₁.2.2.2
    simp only [add_right_inj] at R ;apply path_inj;exact R

theorem uniquedir {α: Type} [AddCommGroup α] [DecidableEq α] {β: Type} [Fintype β]
  {goMap: β → α} {l:ℕ} (j: Fin l.succ)
  (moves: Fin l → β) (ph : Fin l.succ → Bool)
  (left_inj : Function.Injective goMap)

  (i : Fin l.succ) (a₀ a₁ : β)
  (hai₀ : ptdir goMap moves ph j a₀ i)
  (hai₁ : ptdir goMap moves ph j a₁ i)
  : a₀ = a₁
  := by
    let R := Eq.trans hai₀.2.2.2.symm hai₁.2.2.2
    simp only [add_left_inj] at R ;apply left_inj;exact R

theorem uniquelocdir
  {α: Type} [AddCommGroup α] [DecidableEq α]
  {β: Type} [Fintype β]
  {goMap: β → α}
  {l:ℕ} {j: Fin l.succ}
  (moves: Fin l → β) (ph : Fin l.succ → Bool)
  (path_inj: Function.Injective (λ k : Fin l.succ ↦ (pth goMap moves) k))
  (left_inj : Function.Injective goMap)
  :
  (∀ (a : β) (i₀ i₁ : Fin l.succ)
  (_ : ptdir goMap moves ph j a i₀)
  (_ : ptdir goMap moves ph j a i₁)
  ,
  i₀ = i₁)
  ∧
  (∀ (i : Fin l.succ) (a₀ a₁ : β)
  (_ : ptdir goMap moves ph j a₀ i)
  (_ : ptdir goMap moves ph j a₁ i)
  ,
  a₀ = a₁)
  := And.intro (uniqueloc path_inj)
               (uniquedir j _ ph left_inj)

theorem uniquelocdir_rect {l:ℕ} (j: Fin l.succ) -- location, direction
  (moves: Fin l → (Fin 4)) (ph : Fin l.succ → Bool)
  (path_inj: Function.Injective (λ k : Fin l.succ ↦ (pth rectMap moves) k)):
  (∀ (a : Fin 4) (i₀ i₁ : Fin l.succ)
  (_ : ptdir rectMap moves ph j a i₀)
  (_ : ptdir rectMap moves ph j a i₁),
  i₀ = i₁) ∧ (  ∀ (i : Fin l.succ) (a₀ a₁ : Fin 4)
  (_ : ptdir rectMap moves ph j a₀ i)
  (_ : ptdir rectMap moves ph j a₁ i),
  a₀ = a₁
) :=  uniquelocdir moves ph path_inj rectMap_injective


def ptsat'F {α:Type} [AddCommMonoid α] {β : Type} [Fintype β] (goMap : β → α)
  [DecidableEq α] {l:ℕ} (k : Fin l) (ph : Fin l → Bool) (fold : Fin l → α) : ℕ :=
  Finset.card (
    Finset.filter (λ i : Fin l ↦ (ptloc goMap fold i k ph))
    Finset.univ
  )

theorem ptsat'dir {α: Type} [AddCommGroup α] [DecidableEq α] {b:ℕ}
  {goMap: Fin b → α}
  {l:ℕ} (j : Fin l.succ) (ph : Fin l.succ → Bool)
  (moves: Fin l → Fin b)
  (path_inj : (Function.Injective fun k =>  (pth goMap moves) k))
  (left_inj: Function.Injective goMap)
  : ptsat'F goMap j ph (pth goMap moves) ≤ b :=
  by
    unfold ptsat'F
    have : Finset.filter (
        λ i : Fin (Nat.succ l) ↦ (∃ a, ptdir goMap moves ph j a i)) Finset.univ =
          Finset.filter (
        λ i : Fin (Nat.succ l) ↦  ptloc goMap (pth goMap moves) i j ph) Finset.univ
    := by
      apply Finset.ext;intro i;repeat (rw [Finset.mem_filter]); simp only [Finset.mem_univ,
        true_and, Finset.mem_filter];
      unfold ptdir ptloc nearBy; simp only [exists_and_left, Bool.and_eq_true,
        decide_eq_true_eq]; tauto
    rw [← this]
    rw [← choice_ex_finset_card (uniquelocdir moves ph path_inj left_inj)]
    apply card_finset_fin_le

-- need a pts_tot' for pth

-- Almost obsolete, except for `rect₃` fold which is not symmetric so that Handshake Lemma
--reasoning does not apply.
-- theorem ptsearnedbounddir' {α: Type} [AddCommGroup α] [DecidableEq α] {b:ℕ}
-- {goMap: Fin b → α}
-- {l:ℕ} (ph : Fin l.succ → Bool)
-- (moves: Fin l → Fin b)
-- (path_inj  : (Function.Injective fun k =>  (pth goMap moves) k))
-- (left_inj  : Function.Injective goMap)
-- : pts_tot' go ph (pathᵥ go moves) ≤ l.succ * b := by
  -- suffices pts_tot' go ph (pathᵥ go moves) ≤ Finset.sum (Finset.univ : Finset (Fin l.succ)) (λ _ ↦ b) by
  --   simp at this; tauto
  -- apply Finset.sum_le_sum; intro i; intro
  -- exact pts_at'_dir i ph moves path_inj right_inj left_inj
