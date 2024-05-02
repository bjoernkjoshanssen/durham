import Mathlib.Computability.NFA
import Mathlib.Data.Nat.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Std.Data.Nat.Lemmas
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Vector.Basic

set_option tactic.hygienic false

/- This proof illustrate the value
of a folding that can be extended infinitely, to avoid typecasting
issues. This is a surprising angle on the KKNS paper.
It also has pleasing uses of "decide".
-/

def left  (p: ℤ × ℤ) : ℤ × ℤ := (p.1-1,p.2)
def right (p: ℤ × ℤ) : ℤ × ℤ := (p.1+1,p.2)
def up    (p: ℤ × ℤ) : ℤ × ℤ := (p.1  ,p.2+1)
def down  (p: ℤ × ℤ) : ℤ × ℤ := (p.1  ,p.2-1)

def nearby' (p q : ℤ × ℤ) : Prop :=
  q ∈ [down p, up p, left p, right p]


instance (p q : ℤ × ℤ) : Decidable (nearby' p q) := by {
  unfold nearby'
  exact List.instDecidableMemListInstMembershipList q [down p, up p, left p, right p]
}

def folding' (f : ℕ → (ℤ × ℤ)) := ∀ k, nearby' (f k) (f k.succ)

def truebelow (k:ℕ) (P:ℕ→Prop) : Prop := by {
  induction k
  exact True
  exact And (P n) n_ih

}

theorem three_characterize (P:ℕ→Prop) : truebelow 3 P = (P 0 ∧ P 1 ∧ P 2) := by {
  unfold truebelow
  simp
  tauto

}

def one_of (n k : ℕ) : Prop := by {
  induction n; exact False; exact Or (k = n_1) n_ih
}

theorem one_of_fun (n k : ℕ) (h: k < n) : one_of n k := by {
  unfold one_of; induction n; trivial; simp
  have : k < n_1 ∨ k = n_1 := by exact Nat.lt_or_eq_of_le (Nat.lt_succ.mp h)
  cases this; right; exact n_ih h_1; left; exact h_1
}

theorem case3' {k n:ℕ} (h: k < n.succ)
(h₄: ¬Nat.succ k < n.succ) : k = n := by {
  have : k < n ∨ k = n := Nat.lt_or_eq_of_le (Nat.lt_succ.mp h)
  cases this; exfalso; contrapose h₄; simp; exact Nat.lt_succ.mpr h_1
  exact h_1
}

theorem case_3 {k:ℕ} (h:k < 3) : k = 0 ∨ k = 1 ∨ k = 2 :=
  by {let G := one_of_fun 3 k h; unfold one_of at G; simp at G; revert G; tauto}



theorem case3 {k:ℕ} (h:k.succ < 4) :
  k = 0 ∨ k = 1 ∨ k = 2 := case_3 (Nat.succ_lt_succ_iff.mp h)



theorem one_of_succ  {k n_1:ℕ}
(hn: one_of (Nat.succ n_1) k)
(h₁: ¬n_1 = k)
: one_of n_1 k := by {cases hn; exfalso; exact h₁ h.symm; exact h}

theorem propositional_syllogism {k n:ℕ} (P:ℕ→Prop) (h: truebelow n P) (hn : one_of n k) : P k := by {
  induction n

  exfalso; contrapose hn; unfold one_of; simp

  by_cases h₁: (n_1=k)
  subst h₁; exact h.left
  exact n_ih h.right (one_of_succ hn h₁)
}
theorem true_of_below' {k n:ℕ} (P:ℕ→Prop) (h: truebelow n P) (hn : k < n) : P k := by {
  let G := one_of_fun n k hn
  exact propositional_syllogism P h G
}

theorem true_of_below''' (k:ℕ) (P:ℕ→Prop) (h: truebelow k P) (hb: ∀ {n}, k ≤ n → P n) : ∀ n, P n := by {
  intro i
  by_cases hk : k ≤ i
  exact hb hk
  have : i < k := by exact Nat.not_le.mp hk
  exact true_of_below' P h this
}


def myfold : List (ℤ×ℤ) := [(0,0),(1,0),(1,1),(0,1)]

def f₁ (n:ℕ):  ℤ×ℤ  := dite (n<4)
  (λ h ↦ myfold.get ⟨n,h⟩)
  (λ _ ↦ (0,n-2))

def point_achieved'
  (l : ℕ → (ℤ×ℤ)) (a b : ℕ) (phobic : ℕ → Bool) : Prop
:= by {
  exact phobic a ∧ phobic b ∧ a.succ < b ∧ nearby' (l a) (l b)
}

def point_achieved''
  (l : ℕ → (ℤ×ℤ)) (a b : ℕ) (phobic : ℕ → Bool) : Bool
:= by {
  exact phobic a && phobic b && a.succ < b && nearby' (l a) (l b)
}


-- to use point_achieved' need to make an infinite version of [true,b₀,b₁,true]:
def phobe (n:ℕ): Bool   := dite (n<4)
  (λ h ↦ [true,false,false,true].get ⟨n,h⟩)
  (λ _ ↦ false)

instance (a b : ℕ) (ph : ℕ → Bool)
  (f : ℕ → (ℤ×ℤ))
  : Decidable (point_achieved' f a b ph) := by {
  unfold point_achieved'
  exact And.decidable
}
instance (a b : ℕ) (ph : ℕ → Bool)
  (f : ℕ → (ℤ×ℤ))
  : Decidable (point_achieved'' f a b ph) := by {
  unfold point_achieved''
  exact Bool.decEq (ph a && ph b && decide (Nat.succ a < b) && decide (nearby' (f a) (f b))) true
}

theorem first_point'' : point_achieved'' f₁ 0 3 phobe
:= by decide
def F : Bool → ℕ := λ b ↦ ite (b=true) 1 0

theorem fp : List.sum (List.map F [
  point_achieved'' f₁ 0 3 phobe,
  point_achieved'' f₁ 1 3 phobe
]) = 1 :=
by {
  decide
}

def pts_at (k : ℕ) (ph : ℕ → Bool)
  (f : ℕ → (ℤ×ℤ)) :=
  List.sum (List.map F (List.ofFn (λ i : Fin k ↦   point_achieved'' f i k ph)))

-- pts_below is the protein folding scoring function
def pts_below (k : ℕ) (phobic : ℕ → Bool) (fold : ℕ → (ℤ×ℤ))
:= List.sum (List.ofFn (λ i : Fin k ↦ pts_at i phobic fold))

def rect_fold : List (ℤ×ℤ) :=
  [(0, -1), (-1, -1), (-1, -2), (0, -2), (1, -2), (1, -1), (1, 0), (0, 0)]

-- #eval [(0,0),(1,0),(1,-1),(1,-2),(0,-2),(-1,-2),(-1,-1),(0,-1)].reverse

def rfi : ℕ → (ℤ×ℤ) := λ n ↦ dite (n < 8)
  (λ h ↦ rect_fold.get ⟨n,h⟩)
  (λ _ ↦ (-(n-7),0))


theorem fp'' : pts_at 3 phobe f₁ = 1 := by decide
theorem fp''' : pts_below 4 phobe f₁ = 1 := by decide
theorem first_point' : point_achieved' f₁ 0 3 phobe := by decide

instance : OfNat (Fin (List.length myfold)) 0 := ⟨0,by {unfold myfold;simp}⟩
instance : OfNat (Fin (List.length myfold)) 3 := ⟨3,by {unfold myfold;simp}⟩
theorem fpl {b₀ b₁ : Bool} :  List.length [true, b₀, b₁, true] = List.length myfold
:= by {simp;rfl}


theorem f₁ldingbelow3' : truebelow 3 (λ k ↦ nearby' (f₁ k) (f₁ k.succ)) := by {
  unfold truebelow; unfold nearby'; unfold f₁; simp; decide
}

theorem rectfoldbelow : truebelow 8 (λ k ↦ nearby' (rfi k) (rfi k.succ)) := by {
  unfold truebelow; unfold nearby'; unfold rfi; simp; decide
}

theorem case'' {k l:ℕ}
(h₄: ¬ k < l) :
¬ k.succ < l := by {by_contra; contrapose h₄; simp; exact Nat.lt_of_succ_lt a}

theorem fr_duh : folding' rfi := by {
  unfold rfi
  have hl: ∀ n, n < 8 → nearby' (rfi n) (rfi n.succ) := by {
    decide -- so all the "truebelow" and "one_of" stuff was superfluous!?
  }
  have hnl: ∀ n, ¬ n < 8 → nearby' (rfi n) (rfi n.succ) := by {
    intro n hn
    unfold rfi
    rw [dif_neg hn]
    simp
    have : ¬ n.succ < 8 := by exact case'' hn
    rw [dif_neg this]
    unfold nearby'
    right
    right
    unfold left
    ring_nf
    left
  }
  intro n
  by_cases h : n < 8
  exact hl _ h
  exact hnl _ h
}

theorem fr : folding' rfi := by {
  apply true_of_below''' 8
  exact rectfoldbelow

  intro k hk
  unfold rfi
  have : ¬ k < 8 := by exact Nat.not_lt.mpr hk
  rw [dif_neg this]
  simp
  have : ¬ k.succ < 8 := by exact case'' this
  rw [dif_neg this]
  unfold nearby'
  right
  right
  unfold left
  ring_nf
  left
}


theorem f₁olding : folding' f₁ := by {
  apply true_of_below'''
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

  rw [dif_neg h,dif_neg (case'' h)]

  right; simp; unfold up; ring_nf; left
}

-- OBSOLETE:
-- theorem true_of_below (P:ℕ→Prop) (h: truebelow 3 P) (hb: ∀ {n}, 3 ≤ n → P n) : ∀ n, P n := by {
--   rw [three_characterize] at h
--   intro n; by_cases h₃ : 3 ≤ n; exact hb h₃; have : n < 3 := by exact Nat.not_le.mp h₃
--   -- unfold truebelow at h;
--   cases case_3 this
--   subst h_1; exact h.1; cases h_1; subst h_2; exact h.2.1; subst h_2; exact h.2.2
-- }
