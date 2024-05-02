import Mathlib.Computability.NFA
import Mathlib.Data.Nat.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Std.Data.Nat.Lemmas
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Vector.Basic

set_option tactic.hygienic false

/- This proof is too complicated but it does illustrate the value
of a folding that can be extended infinitely, to avoid typecasting
issues. This is a surprising angle on the KKNS paper.
It also has pleasing uses of "decide".
-/

def left  (p: ℤ × ℤ) : ℤ × ℤ := (p.1-1,p.2)
def right (p: ℤ × ℤ) : ℤ × ℤ := (p.1+1,p.2)
def up    (p: ℤ × ℤ) : ℤ × ℤ := (p.1  ,p.2+1)
def down  (p: ℤ × ℤ) : ℤ × ℤ := (p.1  ,p.2-1)


def nearby (p q : ℤ × ℤ) : Prop :=
  -- q ∈ [down p, up p, left p, right p]
  q = down p --(p.1 = q.1) ∧ (p.2 = q.2 + 1)
  ∨
  q = up p --(p.1 = q.1) ∧ (q.2 = p.2 + 1)
  ∨
  (q = left  p) ∨
  (q = right p) --(p.2 = q.2) ∧ (q.1 = p.1 + 1)

def nearby' (p q : ℤ × ℤ) : Prop :=
  q ∈ [down p, up p, left p, right p]


instance (p q : ℤ × ℤ) : Decidable (nearby p q) := by {
  unfold nearby
  exact Or.decidable
}

instance (p q : ℤ × ℤ) : Decidable (nearby' p q) := by {
  unfold nearby'
  exact List.instDecidableMemListInstMembershipList q [down p, up p, left p, right p]
}


instance (K L : Vector (ℤ×ℤ) 4) (a : Fin K.length) (b: Fin L.length) : Decidable (
  nearby (K.get a) (L.get b)
) := by {
  exact instDecidableNearby (Vector.get K a) (Vector.get L b)
}

instance : Decidable (nearby
  (Vector.get ⟨[(0, 0), (1, 0), (1, 1), (0, 1)],rfl⟩ ⟨0, (zero_lt_four)⟩)
  (Vector.get ⟨[(0, 0), (1, 0), (1, 1), (0, 1)],rfl⟩ ⟨Nat.succ 0, one_lt_four⟩))
  := by {
      exact instDecidableNearby (Vector.get _ _) (Vector.get _ _)
  }

example : nearby'
  (Vector.get ⟨[(0, 0), (1, 0), (1, 1), (0, 1)],rfl⟩ ⟨0, (zero_lt_four)⟩)
  (Vector.get ⟨[(0, 0), (1, 0), (1, 1), (0, 1)],rfl⟩ ⟨Nat.succ 0, one_lt_four⟩) := by{
    unfold nearby'
    exact List.mem_of_mem_getLast? rfl
  }

-- instance (p q : ℤ × ℤ) : Decidable (q = down p) := by {
--   unfold down
--   exact decEq q (p.1, p.2 - 1)
-- }


def folding (f : ℕ → (ℤ × ℤ)) := ∀ k, nearby (f k) (f k.succ)

def folding' (f : ℕ → (ℤ × ℤ)) := ∀ k, nearby' (f k) (f k.succ)

def truebelow (k:ℕ) (P:ℕ→Prop) : Prop := by {
  induction k
  exact True
  exact And n_ih (P n)

}

theorem test (P:ℕ→Prop) : truebelow 3 P = (P 0 ∧ P 1 ∧ P 2) := by {
  unfold truebelow
  simp
  tauto

}









def one_of (n k : ℕ) : Prop := by {
  induction n; exact False; exact Or (k = n_1) n_ih
}

theorem test_4 (k:ℕ) : one_of 4 k = (k = 3 ∨ k = 2 ∨ k = 1 ∨ k = 0) := by {
  unfold one_of; simp
}

theorem one_of_fun (n k : ℕ) (h: k < n) : one_of n k := by {
  unfold one_of; induction n; trivial; simp
  have : k < n_1 ∨ k = n_1 := by exact Nat.lt_or_eq_of_le (Nat.lt_succ.mp h)
  cases this; right; exact n_ih h_1; left; exact h_1
}

theorem test_10 (k:ℕ) (h: k < 20) :
  k = 19 ∨ k = 18 ∨ k = 17 ∨ k = 16 ∨ k = 15 ∨ k = 14 ∨ k = 13 ∨ k = 12 ∨ k = 11 ∨ k = 10 ∨
  k = 9 ∨ k = 8 ∨ k = 7 ∨ k = 6 ∨ k = 5 ∨ k = 4 ∨ k = 3 ∨ k = 2 ∨ k = 1 ∨ k = 0
:= by {let G := one_of_fun 20 k h;unfold one_of at G;simp at G;exact G}





theorem test_it0 (k:ℕ) : one_of 0 k = (False) := by {
  unfold one_of
  simp
}
theorem test_it1 (k:ℕ) : one_of 1 k = (k = 0) := by {
  unfold one_of
  simp
}

theorem case3' {k:ℕ} (h: k < 4)
(h₄: ¬Nat.succ k < 4) : k = 3 := by {
  have : k < 3 ∨ k = 3 := Nat.lt_or_eq_of_le (Nat.lt_succ.mp h)
  cases this; exfalso; contrapose h₄; simp; exact Nat.lt_succ.mpr h_1
  exact h_1
}

theorem case_3 {k:ℕ} (h:k < 3) :
-- can now prove a general version of this using Or _ _
  k = 0 ∨ k = 1 ∨ k = 2 := by {
  have : k < 2 ∨ k = 2 := Nat.lt_or_eq_of_le (Nat.lt_succ.mp h)
  cases this
  have : k < 1 ∨ k = 1 := Nat.lt_or_eq_of_le (Nat.lt_succ.mp h_1)
  cases this
  have : k = 0 := Nat.lt_one_iff.mp h_2
  left;exact this;right;left;exact h_2;right;right;exact h_1
}


theorem case3 {k:ℕ} (h:k.succ < 4) :
  k = 0 ∨ k = 1 ∨ k = 2 := case_3 (Nat.succ_lt_succ_iff.mp h)


theorem true_of_below (P:ℕ→Prop) (h: truebelow 3 P) (hb: ∀ {n}, 3 ≤ n → P n) : ∀ n, P n := by {
  rw [test] at h
  intro n; by_cases h₃ : 3 ≤ n; exact hb h₃; have : n < 3 := by exact Nat.not_le.mp h₃
  -- unfold truebelow at h;
  cases case_3 this
  subst h_1; exact h.1; cases h_1; subst h_2; exact h.2.1; subst h_2; exact h.2.2
}

def myfold : List (ℤ×ℤ) := [(0,0),(1,0),(1,1),(0,1)]

def f₀ (n:ℕ):  ℤ×ℤ  := dite (n<4)
  (λ _ ↦ ite (n=0) (0,0) (ite (n=1) (1,0) (ite (n=2) (1,1) (0,1))))
  (λ _ ↦ (0,n-2))

def f₁ (n:ℕ):  ℤ×ℤ  := dite (n<4)
  (λ h ↦ myfold.get ⟨n,h⟩)
  (λ _ ↦ (0,n-2))


theorem f₁ldingbelow3' : truebelow 3 (λ k ↦ nearby' (f₁ k) (f₁ k.succ)) := by {
  unfold truebelow
  unfold nearby'
  unfold f₁
  simp
  decide -- this will work for very long folds too
}


theorem case3'' {k:ℕ}
(h₄: ¬ k < 4) :
¬ k.succ < 4 := by {by_contra; contrapose h₄; simp; exact Nat.lt_of_succ_lt a}

theorem f₁olding : folding' f₁ := by {
  apply true_of_below
  exact f₁ldingbelow3'

  intro n hn
  have h': ¬ n.succ < 4 := λ hc ↦ by {
    have : n < 3 := by exact Nat.succ_lt_succ_iff.mp hc
    have : 3 < 3 := by exact Nat.lt_of_le_of_lt hn this
    exact LT.lt.false this
  }

  unfold f₁
  by_cases h:(n<4)
  rw [dif_pos h]

  rw [dif_neg h']
  have : n=3 := case3' h h'
  subst this
  unfold myfold
  simp
  ring_nf
  decide

  rw [dif_neg h]
  rw [dif_neg h']
  simp
  unfold nearby'
  right
  unfold up
  simp
  ring_nf;
  left
}

example : List.Mem 0 [0,1,2] :=
List.Mem.head [1, 2]




theorem f₁lding' : folding' f₁ := by {
  intro k
  unfold f₁
  by_cases h:(k<4)
  rw [dif_pos h]
  by_cases h₄: k.succ < 4
  rw [dif_pos h₄]
  cases case3 h₄
  subst h_1
  simp; decide;

  unfold myfold;cases h_1;
  subst h_2; simp; decide
  subst h_2; simp; decide
  unfold nearby';
  have : k = 3 := case3' h h₄; subst this
  rw [dif_neg h₄]; simp; ring_nf; right;left;rfl

  rw [dif_neg h,dif_neg (case3'' h)]

  right; simp; unfold up; ring_nf; left
}


theorem f₁lding : folding f₁ := by {
  intro k
  by_cases h:(k<4)
  unfold f₁
  rw [dif_pos h]
  by_cases h₄: k.succ < 4
  rw [dif_pos h₄]
  cases case3 h₄
  subst h_1
  simp; decide;
  cases h_1
  subst h_2
  unfold myfold; simp; decide; subst h_2
  unfold myfold; simp; decide

  have : k = 3 := case3' h h₄; subst this
  right;left;rfl
  unfold f₁; rw [dif_neg h]
  have : ¬ k.succ < 4 := by {by_contra; contrapose h; simp; exact Nat.lt_of_succ_lt a}
  rw [dif_neg this]
  unfold nearby
  right; left; simp; unfold up; apply Prod.ext; rfl; simp; ring
}

theorem lt4 {k: ℕ} (h₀: ¬k = 0) (h₁: ¬k = 1) (h₂: ¬k = 2) (h₃: ¬k = 3) :
  ¬k < 4 := by {
  intro h;
  cases Nat.lt_or_eq_of_le (Nat.lt_succ.mp h)
  cases Nat.lt_or_eq_of_le (Nat.lt_succ.mp h_1)
  cases Nat.lt_or_eq_of_le (Nat.lt_succ.mp h_2)
  cases Nat.lt_or_eq_of_le (Nat.lt_succ.mp h_3)
  contrapose h_4; simp
  exact h₀ h_4;exact h₁ h_3;exact h₂ h_2;exact h₃ h_1
}

theorem f₀lding : folding f₀ := by {
  intro k
  by_cases h₀:(k=0); subst h₀; unfold f₀; simp; decide
  by_cases h₁:(k=1); subst h₁; unfold f₀; simp; decide
  by_cases h₂:(k=2); subst h₂; unfold f₀; simp; decide
  by_cases h₃:(k=3); subst h₃; unfold f₀; simp; decide

  have ht: ¬ k < 4 := lt4 h₀ h₁ h₂ h₃
  have H₂: ¬ k.succ < 4 := λ hc ↦ ht (Nat.lt_of_succ_lt hc)

  unfold f₀
  rw [dif_neg ht];simp
  rw [if_neg h₀,if_neg h₁,if_neg H₂]
  unfold nearby
  right
  left
  unfold up
  simp
  ring
}






-- theorem l (p q : ℤ×ℤ) : q = left p ↔ (p.2 = q.2) ∧ (p.1 = q.1 + 1)
-- := by {
--   unfold left; constructor; intro h; constructor
--   exact congr_arg (λ x ↦ x.2) h.symm
--   let G := congr_arg (λ x ↦ x.1) h.symm
--   simp at G; rw [← G]; simp; intro h; apply Prod.ext
--   simp; rw [h.2]; simp; simp; exact h.1.symm
-- }

-- theorem li (p q : ℤ × ℤ) : q ∈ [down p, up p, left p, right p] ↔
--   q = down p ∨ q = up p ∨ (q = left  p) ∨ (q = right p)
-- := by {
--   constructor
--   intro h
--   cases h;                 left; rfl
--   cases a; right;          left; rfl
--   cases a_1; right; right; left; rfl
--   cases a; right; right; right; rfl
--   cases a_1

--   intro h
--   simp
--   cases h;                                                  left; exact h_1
--   cases h_1;  right;                                        left; exact h
--   cases h;    right; right; left; exact h_1; right; right; right; exact h_1
-- }
