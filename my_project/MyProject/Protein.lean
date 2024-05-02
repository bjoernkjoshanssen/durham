import Mathlib.Computability.NFA
import Mathlib.Data.Nat.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Std.Data.Nat.Lemmas
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Vector.Basic

/- This proof is too complicated but it does illustrate the value
of a folding that can be extended infinitely, to avoid typecasting
issues. This is a surprising angle on the KKNS paper. -/

def nearby (p q : ℕ × ℕ) : Prop :=
  (p.1 = q.1) ∧ (p.2 = q.2 + 1) ∨
  (p.1 = q.1) ∧ (q.2 = p.2 + 1) ∨
  (p.2 = q.2) ∧ (p.1 = q.1 + 1) ∨
  (p.2 = q.2) ∧ (q.1 = p.1 + 1)

def is_folding {n:ℕ}
  (f : Vector (ℕ × ℕ) n)
  : Prop :=
  ∀ k l:Fin n, l.1=k.1.succ →
  nearby (f.get k) (f.get l)

def folding
  (f : ℕ → (ℕ × ℕ))
  : Prop :=
  ∀ k,
  nearby (f k) (f k.succ)

def f₀ (n:ℕ):  ℕ×ℕ  :=
  ite (n<4)
    (ite (n=0) (0,0) (ite (n=1) (1,0) (ite (n=2) (1,1) (0,1))))
    (0,n.pred.pred)

theorem trivvy (k: ℕ)
(h₀: ¬k = 0)
(h₁: ¬k = 1)
(h₂: ¬k = 2)
(h₃: ¬k = 3)
: ¬k < 4 := by {
  intro hc
  cases Nat.lt_or_eq_of_le (Nat.lt_succ.mp hc)
  rename k < 3 => H
  cases Nat.lt_or_eq_of_le (Nat.lt_succ.mp H)
  rename k < 2 => H
  cases Nat.lt_or_eq_of_le (Nat.lt_succ.mp H)
  rename k < 1 => H
  cases Nat.lt_or_eq_of_le (Nat.lt_succ.mp H)
  rename k < 0 => H
  contrapose H
  simp
  rename k = 0 => H
  exact h₀ H
  rename k = 1 => H
  exact h₁ H
  rename k = 2 => H
  exact h₂ H
  rename k = 3 => H
  exact h₃ H
}

theorem f₀olding : folding f₀ := by {
  intro k
  by_cases h₀:(k=0); subst h₀
  unfold f₀; simp; unfold nearby; decide
  by_cases h₁:(k=1); subst h₁
  unfold f₀; simp; unfold nearby; decide
  by_cases h₂:(k=2); subst h₂
  unfold f₀; simp; unfold nearby; decide
  by_cases h₃:(k=3); subst h₃
  unfold f₀; simp; unfold nearby; decide
  have ht: ¬ k < 4 := trivvy _ h₀ h₁ h₂ h₃
  unfold f₀
  rw [if_neg ht];simp
  rw [if_neg h₀,if_neg h₁]
  have : ¬ k.succ < 4 := by {
    intro hc
    have : k < 4 := Nat.lt_of_succ_lt hc
    exact ht this
  }
  rw [if_neg this]
  unfold nearby
  right
  left
  constructor
  rfl
  simp
  have : k ≥ 4 := Nat.not_lt.mp ht
  have : k.pred ≥ 3 := Nat.le_pred_of_lt this
  have : k = Nat.succ (Nat.succ (Nat.pred (Nat.pred k))) := by {
    have H₀: k.pred > 0 := Nat.zero_lt_of_lt this
    rw [Nat.succ_pred_eq_of_pos H₀]
    have H₁: k > 0 := Nat.pos_of_ne_zero h₀
    rw [Nat.succ_pred_eq_of_pos H₁]
  }
  exact this
}
  -- ⟨[(0,0), (1,0), (1,1), (0,1)],rfl⟩

-- def nontrivial_list : Vector (ℕ×ℕ) 4 :=
--   ⟨[(0,0), (1,0), (1,1), (0,1)],rfl⟩


-- example : is_folding (nontrivial_list) := by {
--   intro k l h
--   unfold nontrivial_list
--   by_cases hk0:(k=0)
--   subst hk0
--   have g : l=1 := Fin.ext h
--   subst g
--   unfold nearby
--   right
--   right
--   right
--   constructor;rfl;rfl
--   by_cases hk1: k=1
--   subst hk1
--   have : l=2 := Fin.ext h
--   subst this
--   unfold nearby
--   right
--   left
--   constructor;rfl;rfl
--   by_cases hk2:k=2
--   subst hk2
--   have : l = 3 := Fin.ext h
--   subst this
--   unfold nearby
--   right
--   right
--   left
--   constructor;rfl;rfl
--   exfalso
--   have : k=3 := sorry
--   subst this
--   norm_cast
--   have : l.1 < 4 := l.2
--   rw [h] at this
--   contrapose this
--   sorry

-- }

--   λ k l H ↦
--   dite (k=0) (
--     λ hk0 ↦
--     Or.inr (Or.inr (Or.inr (And.intro (
--       have hl1: l=1 := by {subst hk0;exact Fin.ext H}
--       by {unfold nontrivial_list;rw [hl1,hk0];exact rfl} --sorry
--     ) (
--       by {
--         unfold nontrivial_list
--         subst hk0
--         simp at H
--         have : l=1 := Fin.ext H
--         subst this
--         simp
--         rfl
--       }
--     ))))
--   )
--   (
--     λ hkn0 ↦ by {
--       unfold nearby

--       constructor
--       constructor

--       by_cases h:(k=1)
--       subst h
--       have : l = 2 := Fin.ext H
--       subst this
--       rfl
--       by_cases h₂:(k=2)
--       subst h₂
--       have : l=3 := Fin.ext H
--       subst this
--       unfold nontrivial_list
--       let G₂ := (nontrivial_list.get 2).1
--       have : G₂ = 1 := rfl
--       let G₃ := (nontrivial_list.get 3).1
--       have : G₃ = 0 := rfl
--       sorry
--       have : k=3 := sorry
--       subst this
--       sorry
--       sorry
--     })







-- -- def is_folding' {n:ℕ} (f:Fin n → (Fin n) × (Fin n)) : Prop :=
-- --   ∀ k l:Fin n, l.1=k.1.succ →
-- --   nearby (f k) (f l)

-- -- example : is_folding' (λ k:Fin 3, (0,k)) :=
-- --   λ k l H,
-- --     Or.inr (or.inl (and.intro rfl H))
-- -- def nontrivial_list' : Vector ((Fin 4)×(Fin 4)) 4 :=
-- --   ⟨[(0,0), (1,0), (1,1), (0,1)],rfl⟩
-- -- def to_fn' {n:ℕ} (alist: Vector ((Fin n)×(Fin n)) n) :
-- --   Fin n → (Fin n)×(Fin n) :=
-- --   λ k, alist.get k
-- -- example : is_folding' (to_fn' nontrivial_list') := λ k l H,
-- --   dite (k=0) (
-- --     λ hk0, -- TOO TEDIOUS
-- --         have l.1 = 1, from calc
-- --              l.1 = k.1.succ : H
-- --              ... = 1: by {rw hk0,simp,},
-- --         have hl: l=1, from by tidy,
-- --       Or.inr (Or.inr (Or.inr (and.intro (
-- --         by {rw [hl,hk0],unfold to_fn',unfold nontrivial_list',tidy,}
-- --       ) (
-- --         by {rw [hl,hk0],unfold to_fn',unfold nontrivial_list',tidy,}
-- --       ))))
-- --   ) (λ h, dite (k=1) (
-- --     λhk1, sorry
-- --     ) sorry)












-- -- def nearby (p q : ℤ × ℤ) : Prop :=
-- -- 	(p.1 = q.1) ∧ (p.2 = q.2 + 1) ∨ (p.1 = q.1) ∧ (q.2 = p.2 + 1) ∨	(p.2 = q.2) ∧ (p.1 = q.1 + 1) ∨	(p.2 = q.2) ∧ (q.1 = p.1 + 1)
-- -- def is_folding {n:ℕ} (f:Fin n → ℤ × ℤ) : Prop :=
-- --   ∀ k:Fin n, ∀ H: k.1.succ < n,
-- --   nearby (f k) (f ⟨k.1.succ, H⟩)
-- -- example : is_folding (λ k:Fin 3, (0,k.1)) :=
-- --   λ k H, Or.inr (or.inl (and.intro rfl rfl))
-- -- def mylist : Vector (ℤ×ℤ) 1 := ⟨[(0,0)],rfl⟩
-- -- def nontrivial_list : Vector (ℤ×ℤ) 4 := ⟨[(0,0), (1,0), (1,1), (0,1)],rfl⟩



-- -- def to_fn {n:ℕ} (alist: Vector (ℤ×ℤ) n) : Fin n → ℤ×ℤ := λ k, alist.get k

-- -- example : is_folding (to_fn mylist) := λ k H, false.elim (
-- --   have k.1<1, from k.2,
-- --   have k.1=0, from nat.lt_one_iff.mp this,
-- --   have 1<1, from lt_of_lt_of_eq' H (congr_arg nat.succ this).symm,
-- --   nat.lt_asymm this this
-- -- )


-- -- example (n : ℕ) (a b : Fin n) : a.1 = b.1 → a = b := Fin.eq_of_veq

-- -- example (n : ℕ) (a b : Fin n) : a = b → a.1 = b.1 := congr_arg (λ (a : Fin n), a.val)

-- -- example (n : ℕ) (a b : Fin n) (H: a.1 < n) (I: b.1 < n) :
-- --   b = a → (⟨a.1,H⟩:Fin n) = (⟨b.1,I⟩:Fin n) := sorry
-- --   --(eq_iff_eq_of_cmp_eq_cmp rfl).mp





-- -- example : is_folding (to_fn nontrivial_list) := λ k H, dite (k=0) (
-- --   λ h,
-- --     have h5': k.succ = 1, from congr_arg _ h,

-- --     have h5:(⟨k.1.succ, H⟩:Fin 4) = (1:Fin 4), from sorry,
-- --     -- i used to know this

-- --     have h6: nearby (0,0) (1,0), from Or.inr (Or.inr (Or.inr (and.intro rfl rfl))),
-- --     by {rw [h5,h],exact h6,}
-- --   )
-- --   sorry

-- -- def point_achieved {k:ℕ} (word : Vector (Fin 2) k) (f: Fin k → ℤ×ℤ) (l₀ l₁ : Fin k) : Prop :=
-- --   l₀.1.succ < l₁.1 ∧
-- --   nearby (f l₀) (f l₁) ∧
-- --   word.get l₀ = 0 ∧
-- --   word.get l₁ = 0

-- -- def points {k:ℕ} (word : Vector (Fin 2) k) (f: Fin k → ℤ×ℤ) : ℕ := sorry
