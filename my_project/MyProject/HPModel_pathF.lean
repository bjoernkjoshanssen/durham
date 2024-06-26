import MyProject.HPModelF
import MyProject.pathsum

def pathF  {α β:Type} [OfNat α 0] {l:ℕ} (go : β → α → α)
  (moves : Fin l → β): Fin l.succ → α :=
  λ n ↦ pathf go moves n.1 0


def path_F  {α β:Type} [OfNat α 0] {l:ℕ} (go : β → α → α)
  (moves : Fin l → β): Fin l.succ → α := λ j ↦ match j with
| 0 => 0
| (@Fin.mk _ (Nat.succ i) isLt) =>
                      go (moves ⟨i,Nat.succ_lt_succ_iff.mp isLt⟩)
  (path_F go moves (Fin.castSucc ⟨i,Nat.succ_lt_succ_iff.mp isLt⟩))
-- maybe everything will be easier once we prove... :

theorem path_F_cons
  {α β:Type} [OfNat α 0] {l:ℕ} (go : β → α → α)
  (moves : Fin l.succ → β)
  (i : Fin l) (islt : Nat.succ i.1 < Nat.succ (l + 1)):
  path_F go moves ((@Fin.mk _ (Nat.succ i) islt))
  = go (moves ⟨i,Nat.succ_lt_succ_iff.mp islt⟩)
  (path_F go moves (Fin.castSucc ⟨i,Nat.succ_lt_succ_iff.mp islt⟩)) := by
    exact rfl

theorem path_F_cons₂
  {α β:Type} [OfNat α 0] {l:ℕ} (go : β → α → α)
  (moves : Fin l.succ → β)
  (i : Fin l) (islt : Nat.succ i.1 < Nat.succ (l + 1)):
  path_F go moves ⟨(Nat.succ i), islt⟩
  = go (moves ⟨i,Nat.succ_lt_succ_iff.mp islt⟩)
  (path_F go moves (Fin.castSucc ⟨i,Nat.succ_lt_succ_iff.mp islt⟩)) := by
    exact rfl

theorem path_F_cons₂_last
  {α β:Type} [OfNat α 0] {l:ℕ} (go : β → α → α)
  (moves : Fin l.succ → β)
  :
  path_F go moves (Fin.last l.succ)
  = go (moves (Fin.last l))
  (path_F go moves (⟨l, Nat.lt.step (Nat.lt.base l)
  ⟩)) := by
    exact rfl

theorem path_F_cons₂_second_last
  {α β:Type} [OfNat α 0] {l:ℕ} (go : β → α → α)
  (moves : Fin l.succ.succ → β)
  :
  path_F go moves (⟨l.succ, Nat.lt.step (Nat.lt.base _)⟩)
  = go (moves (⟨l,Nat.lt.step (Nat.lt.base _)⟩))
  (path_F go moves (⟨l, Nat.lt.step (Nat.lt.step (Nat.lt.base _))⟩)) := by
    exact rfl

theorem path_F_cons₃
  {α β:Type} [OfNat α 0] {l:ℕ} (go : β → α → α)
  (moves : Fin l.succ → β)
  (i : Fin l) (islt : Nat.succ i.1 < Nat.succ (l + 1)):
  path_F go moves ⟨(Nat.succ i), islt⟩
  = go (moves ⟨i,Nat.succ_lt_succ_iff.mp islt⟩)
  (path_F go moves (Fin.castSucc ⟨i,Nat.succ_lt_succ_iff.mp islt⟩)) := by
    exact rfl

def morF' {l:ℕ} -- 3/9/24 -- morF = "morphFin"
  {α:Type} [OfNat α 0] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁.succ)
  (go : Fin b₀ → α → α) (moves : Fin l.succ →  (Fin b₀))
  : ℕ → (Fin b₁.succ) := by
  intro n
  induction n with
  | zero => exact f (moves 0) 0
  | succ n_1 _ =>
    by_cases h : (n_1 < l)
    have h₁: n_1.succ < l.succ := Nat.lt_succ.mpr h
    let R := pathF go moves ⟨n_1.succ, Nat.lt.step h₁⟩
    . exact f (moves ⟨n_1.succ,h₁⟩) R
    . exact 0 -- a dummy value

def pt_dirF {α:Type} [OfNat α 0] [DecidableEq α] {β : Type} (go : β → α → α)
 {l:ℕ} (j : Fin l.succ) (moves: Fin l → β) (ph : Fin l.succ → Bool)
: β → Fin l.succ → Prop  := λ a i ↦
  ph i ∧ ph j ∧ i.1.succ < j ∧ (pathF go moves) j = go a ((pathF go moves) i)

theorem unique_locF  {α: Type} [OfNat α 0] [DecidableEq α] {β: Type} [Fintype β]
(go: β → α → α)
 {l:ℕ} (j: Fin l.succ)
  (moves: Fin l → β) (ph : Fin l.succ → Bool)
  (path_inj: Function.Injective (λ k : Fin l.succ ↦ (pathF go moves) k))
  (right_inj: right_injective go)
  :
  ∀ (a : β) (i₀ i₁ : Fin l.succ) (_ : pt_dirF go j moves ph a i₀) (_ : pt_dirF go j moves ph a i₁),
  i₀ = i₁
  := λ a _ _ hai₀ hai₁ ↦ path_inj (right_inj a (Eq.trans hai₀.2.2.2.symm hai₁.2.2.2))

theorem unique_dirF {α: Type} [OfNat α 0] [DecidableEq α] {β: Type} [Fintype β]
(go: β → α → α) {l:ℕ} (j: Fin l.succ)
  (moves: Fin l → β) (ph : Fin l.succ → Bool)
  (left_inj : left_injective go)
  :
  ∀ (i : Fin l.succ) (a₀ a₁ : β)
  (_ : pt_dirF go j moves ph a₀ i)
  (_ : pt_dirF go j moves ph a₁ i),
  a₀ = a₁
  := λ i _ _ hai₀ hai₁ ↦ left_inj ((pathF go moves) i) ((Eq.trans hai₀.2.2.2.symm hai₁.2.2.2))

theorem unique_loc_dirF {α: Type} [OfNat α 0] [DecidableEq α] {β: Type} [Fintype β]
{go: β → α → α} {l:ℕ} {j: Fin l.succ}
  {moves: Fin l → β} {ph : Fin l.succ → Bool}
  (path_inj: Function.Injective (λ k : Fin l.succ ↦ (pathF go moves) k))
  (right_inj: right_injective go)
  (left_inj : left_injective go)
  :
  (∀ (a : β) (i₀ i₁ : Fin l.succ) (_ : pt_dirF go j moves ph a i₀) (_ : pt_dirF go j moves ph a i₁),
  i₀ = i₁) ∧ (  ∀ (i : Fin l.succ) (a₀ a₁ : β)
  (_ : pt_dirF go j moves ph a₀ i)
  (_ : pt_dirF go j moves ph a₁ i),
  a₀ = a₁
) := And.intro (unique_locF go j _ ph path_inj right_inj)
               (unique_dirF go j _ ph left_inj)
theorem unique_loc_dir_rectF {l:ℕ} (j: Fin l.succ) -- location, direction
  (moves: Fin l → (Fin 4)) (ph : Fin l.succ → Bool)
  (path_inj: Function.Injective (λ k : Fin l.succ ↦ (pathF rect moves) k)):
  (∀ (a : Fin 4) (i₀ i₁ : Fin l.succ) (_ : pt_dirF rect j moves ph a i₀) (_ : pt_dirF rect j moves ph a i₁),
  i₀ = i₁) ∧ (  ∀ (i : Fin l.succ) (a₀ a₁ : Fin 4)
  (_ : pt_dirF rect j moves ph a₀ i)
  (_ : pt_dirF rect j moves ph a₁ i),
  a₀ = a₁
) :=  unique_loc_dirF path_inj right_injective_rect left_injective_rect

theorem unique_loc_dir_hexF {l:ℕ} (j: Fin l.succ)
  (moves: Fin l → (Fin 6)) (ph : Fin l.succ → Bool)
  (path_inj: Function.Injective (λ k : Fin l.succ ↦ (pathF hex moves) k)):
  (∀ (a : Fin 6) (i₀ i₁ : Fin l.succ) (_ : pt_dirF hex j moves ph a i₀) (_ : pt_dirF hex j moves ph a i₁),
  i₀ = i₁) ∧ (  ∀ (i : Fin l.succ) (a₀ a₁ : Fin 6)
  (_ : pt_dirF hex j moves ph a₀ i)
  (_ : pt_dirF hex j moves ph a₁ i),
  a₀ = a₁
) := unique_loc_dirF path_inj right_injective_hex left_injective_hex

instance  {α: Type} [OfNat α 0] [DecidableEq α] {b:ℕ}
{go: Fin b → α → α}
  {l:ℕ} (j : Fin l.succ) (ph : Fin l.succ → Bool) (moves: Fin l → (Fin b)) (a : Fin b)
(i : Fin l.succ)
: Decidable (pt_dirF go j moves ph a i) := decidable_of_iff (ph i = true ∧
      ph j = true ∧
        Nat.succ ↑i < ↑j ∧
        (pathF go moves) j = go a ((pathF go moves) i)) (by
          unfold pt_dirF;tauto
        )

theorem pts_at'_dirF {α: Type} [OfNat α 0] [DecidableEq α] {b:ℕ}
{go: Fin b → α → α}
  {l:ℕ} (j : Fin l.succ) (ph : Fin l.succ → Bool)
  (moves: Fin l → (Fin b))
  (path_inj : (Function.Injective fun k =>  (pathF go moves) k))
  (right_inj: right_injective go)
  (left_inj: left_injective go)
  : pts_at'F go j ph (pathF go moves) ≤ b := by
    unfold pts_at'F
    have : Finset.filter (
        λ i : Fin (Nat.succ l) ↦ (∃ a, pt_dirF go j moves ph a i)) Finset.univ =
          Finset.filter (
        λ i : Fin (Nat.succ l) ↦  pt_locF go (pathF go moves) i j ph) Finset.univ
    := by
      apply Finset.ext;intro i;repeat (rw [Finset.mem_filter]);
      simp only [Finset.mem_univ, true_and];
      unfold pt_dirF pt_locF nearby; simp only [exists_and_left,
        Bool.and_eq_true, decide_eq_true_eq]; tauto
    rw [← this,← choice_ex_finset_card (unique_loc_dirF path_inj right_inj left_inj)]
    apply card_finset_fin_le


theorem pts_earned_bound_dir'F {α: Type} [OfNat α 0] [DecidableEq α] {b:ℕ}
{go: Fin b → α → α}
{l:ℕ} (ph : Fin l.succ → Bool)
(moves: Fin l → (Fin b))
(path_inj  : (Function.Injective fun k => (pathF go moves) k))
(right_inj : right_injective go)
(left_inj  : left_injective go)
: pts_tot'F go ph (pathF go moves) ≤ l.succ * b := by
  suffices pts_tot'F go ph (pathF go moves) ≤ Finset.sum (Finset.univ : Finset (Fin l.succ)) (λ _ ↦ b) by
    simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul] at this ; tauto
  apply Finset.sum_le_sum; intro i; intro
  exact pts_at'_dirF i ph moves path_inj right_inj left_inj

theorem pts_earned_bound'F {α: Type} [OfNat α 0] [DecidableEq α] {b:ℕ}
{go: Fin b → α → α}
{l:ℕ} (ph : Fin l.succ → Bool)
(moves: Fin l → (Fin b))
(path_inj : (Function.Injective fun k => (pathF go moves) k))
(right_inj : right_injective go)
(left_inj : left_injective go)

: pts_tot'F go ph (pathF go moves) ≤ min (l.succ * b) (l.succ * l / 2)
:= by
  suffices (
    pts_tot'F go ph (pathF go moves) ≤ l.succ * b
    ∧ pts_tot'F go ph (pathF go moves) ≤ l.succ * l / 2) by
    exact Nat.le_min.mpr this
  constructor
  exact pts_earned_bound_dir'F ph moves path_inj right_inj left_inj
  exact pts_earned_bound_loc'F go ph (pathF go moves)

lemma pathF_dif_pos'
{l: ℕ}
(i: Fin (l))
(moves: Fin ((Nat.succ l)) → Fin 4)
: pathF rect moves { val := i.1 + 1, isLt := (by repeat (apply Nat.succ_lt_succ_iff.mpr); exact Nat.lt.step i.2 : i.1 + 1 < (Nat.succ (Nat.succ l))) }
  =
  rect (moves (i))
  (pathF rect moves { val := i.1, isLt := (by

      exact Nat.lt.step (Nat.lt.step i.2)
      : i.1 < l.succ.succ) })
:= by
  unfold pathF pathf
  simp only [Nat.rec_add_one, Fin.coe_eq_castSucc];

  have : i.1 < l.succ := Nat.lt.step i.2
  rw [dif_pos this]
  rfl

lemma pathF_dif_pos -- i+2,i+1,i+1
{l: ℕ}
(i: Fin (Nat.succ l))
(moves: Fin (Nat.succ (Nat.succ l)) → Fin 4)
: pathF rect moves { val := i.1 + 2, isLt := (by
  repeat (apply Nat.succ_lt_succ_iff.mpr)
  exact i.2
  : i.1 + 2 < Nat.succ (Nat.succ (Nat.succ l))) } =
  rect (moves (Fin.succ i))
    (pathF rect moves { val := i.1 + 1, isLt := (by
      apply Nat.succ_lt_succ_iff.mpr
      exact Nat.lt.step i.2
      : i.1 + 1 < l.succ.succ.succ) })
:= by
  unfold pathF pathf
  exact dif_pos (Nat.succ_lt_succ i.isLt) -- YES!

-- The following theorem is the motivation for all the theorems ending in "F":
theorem orderly_injective' {l :ℕ} (i:Fin l.succ)
(moves : Fin l.succ.succ → (Fin 4)) (h: moves (Fin.castSucc i) = 0 ∧ moves (Fin.succ i) = 1) :
¬ Function.Injective (λ i ↦ (pathF rect moves) i) := by
  intro hc
  have : rect 1 (rect 0 ((pathF rect moves) ⟨i.1, Nat.lt.step (Nat.lt.step i.2)⟩))
  = (pathF rect moves) ⟨i.1, Nat.lt.step (Nat.lt.step i.2)⟩ := by
    unfold rect
    have : rectMap 0 + rectMap 1 = 0 := by decide
    rw [← plane_assoc,this]
    simp
  have h₁: rect 1 ((pathF rect moves) ⟨i.1+1, by
    simp_rw [Nat.succ_eq_add_one]; simp only [add_lt_add_iff_right];exact Nat.lt_add_right 1 i.2
  ⟩)
       = (pathF rect moves) ⟨i.1+2,by simp_rw [Nat.succ_eq_add_one];simp⟩ := by
    rw [← h.2];symm;
    exact pathF_dif_pos i moves
  have h₀: rect 0 ((pathF rect moves) ⟨i.1, Nat.lt.step (Nat.lt.step i.2)⟩)
       = (pathF rect moves) ⟨i.1+1,by
       simp_rw [Nat.succ_eq_add_one]; simp only [add_lt_add_iff_right];

       exact Nat.lt.step i.2
    ⟩ := by
    rw [← h.1];
    let Q := pathF_dif_pos' i moves
    simp only [Fin.coe_eq_castSucc] at Q
    rw [Q]
  have : (pathF rect moves) ⟨i.1, Nat.lt.step (Nat.lt.step i.2)⟩
       = (pathF rect moves) ⟨i.1+2,by simp_rw [Nat.succ_eq_add_one];simp⟩ := by
    rw [← h₁,← h₀,this]
  let Q := hc this
  simp at Q -- is not injective because equals at i and i+2. See orderly-injective.lean

theorem orderly_injective  {l :ℕ}
  (moves : Fin l.succ.succ → (Fin 4))
  (h₀ : moves 0 = 0)
  (j:Fin l) (hj : ∃ i, i.1 < j.1 ∧ moves (Fin.succ i) = 1)
  (h₂: ∀ i, i.1 < j.1 → moves i = 0 ∨ moves i = 1)
  :
  ¬ Function.Injective (λ i ↦ (pathF rect moves) i) := by
    let Q := orderly_injective_helper₂
      l.succ moves h₀ ⟨j.1,Nat.lt.step (Nat.lt.step j.2)⟩ hj h₂
    obtain ⟨i,hi⟩ := Q
    have h: moves (Fin.castSucc i) = 0 ∧ moves (Fin.succ i) = 1 := by tauto

    exact orderly_injective' i moves h

/-- This partially justifies the "global" approach of Apr 4, 2024.
-/
def obtainWitness
{α β:Type} [Fintype β] [DecidableEq α] [OfNat α 0] {l:ℕ} (go : β → α → α)
  (moves : Fin l.succ → β)
  : isPathWitness go (pathF go moves) := by
  intro i
  unfold pathF pathf
  simp only [Fin.val_succ, Nat.rec_add_one, Fin.is_lt, Fin.eta, dite_eq_ite, ite_true,
    Fin.coe_castSucc]

  induction l with
  | zero => exact ⟨moves i,by rw [Fin.coe_fin_one i]⟩
  | succ n _ =>
    by_cases h: (i = Fin.last n.succ)
    . exact ⟨moves (Fin.last n.succ),by subst h;simp⟩
    . exact ⟨moves i, rfl⟩


-- How about the other way: from isPathWitness to moves?
def moves_of_isPathWitness₁
{α:Type} [OfNat α 0] [DecidableEq α] {β : Type} [Fintype β] (go : β → α → α)
 {l:ℕ} (fold : Fin l.succ.succ → α) (h : isPathWitness go fold)
: Fin l.succ → β := λ i ↦ h i
