import Mathlib.Computability.NFA
import Mathlib.Data.Nat.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Std.Data.Nat.Lemmas
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Digits
set_option tactic.hygienic false
set_option maxHeartbeats 3000000

/- This proof illustrate the value
of a folding that can be extended infinitely, to avoid typecasting
issues. This is a surprising angle on the KKNS paper.
It also has pleasing uses of "decide".
-/

def left  (p: ℤ × ℤ) : ℤ × ℤ := (p.1-1,p.2) -- A
def right (p: ℤ × ℤ) : ℤ × ℤ := (p.1+1,p.2) -- D
def up    (p: ℤ × ℤ) : ℤ × ℤ := (p.1  ,p.2+1) -- W
def down  (p: ℤ × ℤ) : ℤ × ℤ := (p.1  ,p.2-1) -- S



def nearby' (p q : ℤ × ℤ) : Prop :=
  q ∈ [down p, up p, left p, right p]

-- Graph theoretic approach:
def nearby (p q : ℤ × ℤ) : Prop :=
  (p.1-q.1)^2 + (p.2-q.2)^2 = 1
def Z2 : SimpleGraph (ℤ×ℤ) := {
  Adj := λ p q ↦ nearby p q
  symm := by {intros _ _ h; unfold nearby at h; unfold nearby; rw [← h]; ring}
  loopless := by {intro p; unfold nearby; simp}
}

-- Instead of Fin n perhaps we should have a graph structure on Fin n
def FinGraph {n:ℕ} : SimpleGraph (Fin n) := {
  Adj := λ k l ↦ l.1 = k.1 + 1 ∨ k.1 = l.1 + 1
  symm := λ k l h ↦ by {
    cases h;
    right; assumption
    left;  assumption
  }
  loopless := by {intro k; simp}
}

def folding {α β:Type} {A:SimpleGraph α}{B:SimpleGraph β} (f : β → α)
  := Function.Injective f ∧ ∀ k l, B.Adj k l → A.Adj (f k) (f l)
-- For a graph obtained by symmetrizing a digraph, this can be stated
-- more simply, though.

-- this is basically an injective weak homomorphism and we have a set
-- on which we want many ctrexamples to strong homomorphism.

-- def folding (f : ℕ → (ℤ × ℤ)) := ∀ k, Z2.Adj (f k) (f k.succ)



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
  have : k < n_1 ∨ k = n_1 := Nat.lt_or_eq_of_le (Nat.lt_succ.mp h)
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
  have : i < k := Nat.not_le.mp hk
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



def some_moves : List Char := [
  'D', 'W', 'W', 'A', 'F', 'S', 'A', 'E', 'E', 'D', 'F'
]

def move₃ : Char → ((ℤ×ℤ×ℤ) → (ℤ×ℤ×ℤ))
| 'A'  => λ x ↦ (x.1 - 1,x.2.1    ,x.2.2)
| 'W'  => λ x ↦ (x.1    ,x.2.1 + 1,x.2.2)
| 'S'  => λ x ↦ (x.1    ,x.2.1 - 1,x.2.2)
| 'F'  => λ x ↦ (x.1    ,x.2.1    ,x.2.2 + 1)
| 'D'  => λ x ↦ (x.1 + 1,x.2.1    ,x.2.2)
| 'E'  => λ x ↦ (x.1    ,x.2.1    ,x.2.2 - 1)
| _ => λ _ ↦ (0,0,0)

def move₂ : Char → ((ℤ×ℤ) → (ℤ×ℤ))
| 'A'  => λ x ↦ (x.1 - 1,x.2    )
| 'W'  => λ x ↦ (x.1    ,x.2 + 1)
| 'S'  => λ x ↦ (x.1    ,x.2 - 1)
| 'D'  => λ x ↦ (x.1 + 1,x.2    )
| _ => λ _ ↦ (0,0)


def A : ℤ×ℤ×ℤ → ℤ×ℤ×ℤ := λ x ↦ x -- change this

def fold_of_moves₃ (sm : List Char) : {l : List (ℤ×ℤ×ℤ) // l ≠ List.nil} := by {
  induction sm
  exact ⟨[(0,0,0)],List.cons_ne_nil _ _⟩
  let new := move₃ head (List.head tail_ih.1 tail_ih.2)
  exact ⟨(new) :: tail_ih.1,List.cons_ne_nil _ _⟩
}
def fold_of_moves₂' (sm : List Char) : {l : List (ℤ×ℤ) // l ≠ List.nil} := by {
  induction sm
  exact ⟨[(0,0)],List.cons_ne_nil _ _⟩
  let new := move₂ head (List.head tail_ih.1 tail_ih.2)
  exact ⟨(new) :: tail_ih.1,List.cons_ne_nil _ _⟩
}
-- def fold_of_moves₂ (sm : List Char) : {l : List (ℤ×ℤ) // l ≠ List.nil} :=
-- ⟨(fold_of_moves₂' sm).1.reverse,by {simp;exact (fold_of_moves₂' sm).2}⟩

def fold_of_moves₂ (sm : List Char) : List (ℤ×ℤ) :=
(fold_of_moves₂' sm).1.reverse

-- #eval fold_of_moves₃ some_moves
def rect_fold : List (ℤ×ℤ) :=
  [(0, -1), (-1, -1), (-1, -2), (0, -2), (1, -2), (1, -1), (1, 0), (0, 0)]



def move_of_digit₂ : Fin 4 → Char
| 0 => 'D'
| 1 => 'A'
| 2 => 'W' -- up on screen but down in coords :-\
| 3 => 'S'
def move_of_digit₃ : Fin 6 → Char
| 0 => 'D'
| 1 => 'A'
| 2 => 'W'
| 3 => 'S'
| 4 => 'E'
| 5 => 'F'
def moves_of_digits₂ (l:List (Fin 4)): List Char := List.map move_of_digit₂ l
def moves_of_digits₃ (l:List (Fin 6)): List Char := List.map move_of_digit₃ l

#eval Function.Injective (λ i ↦ (fold_of_moves₃ some_moves).1.get i)

#eval Function.Injective (λ i ↦ (fold_of_moves₃ (moves_of_digits₃ [0,1,2,3])).1.get i)
-- Will be faster if avoid the char's
def move_fin : Fin 4 → ((ℤ×ℤ) → (ℤ×ℤ))
| 0 => λ x ↦ (x.1 + 1,x.2    )
| 1 => λ x ↦ (x.1 - 1,x.2    )
| 2 => λ x ↦ (x.1    ,x.2 + 1)
| 3 => λ x ↦ (x.1    ,x.2 - 1)

def moves_fin' (l : List (Fin 4)) :  {l : List (ℤ×ℤ) // l ≠ List.nil} := by {
  induction l
  exact ⟨[(0,0)],List.cons_ne_nil _ _⟩
  let new := move_fin head (List.head tail_ih.1 tail_ih.2)
  exact ⟨(new) :: tail_ih.1,List.cons_ne_nil _ _⟩
}

def moves_fin (l : List (Fin 4)) : List (ℤ×ℤ) := (moves_fin' l.reverse).1

#eval moves_fin []
#eval moves_fin [0]
#eval moves_fin [0,0]
#eval moves_fin [0,1]

-- instance (l: List (Fin 4)) (m : List (ℤ×ℤ)) : Decidable (moves_fin l = m) := sorry

#eval moves_fin [(0:Fin 4),1,2,3]

#eval Function.Injective (λ i ↦ (moves_fin [0,1,2,3]).get i)
-- This is now a MonoPred


-- #eval (fold_of_moves₂ ['D','S','S','A','A','W','D'].reverse).reverse
theorem sdfg : rect_fold = (fold_of_moves₂' ['D','S','S','A','A','W','D'].reverse).1
:= rfl

-- #eval [(0,0),(1,0),(1,-1),(1,-2),(0,-2),(-1,-2),(-1,-1),(0,-1)].reverse


theorem fp'' : pts_at 3 phobe f₁ = 1 := by decide
-- theorem fp''' : pts_below 4 phobe f₁ = 1 := by decide
theorem first_point' : point_achieved' f₁ 0 3 phobe := by decide

instance : OfNat (Fin (List.length myfold)) 0 := ⟨0,by {unfold myfold;simp}⟩
instance : OfNat (Fin (List.length myfold)) 3 := ⟨3,by {unfold myfold;simp}⟩
theorem fpl {b₀ b₁ : Bool} :  List.length [true, b₀, b₁, true] = List.length myfold
:= by {simp;rfl}



theorem case'' {k l:ℕ}
(h₄: ¬ k < l) :
¬ k.succ < l := by {by_contra; contrapose h₄; simp; exact Nat.lt_of_succ_lt a}

-- For the optimization problem we want max over all choices of "rect_fold" here
-- howeve
def rfi : ℕ → (ℤ×ℤ) := λ n ↦ dite (n < rect_fold.length)
  (λ h ↦ rect_fold.get ⟨n,h⟩)
  (λ _ ↦ (-(n-7),0))


def extend_fold (rf : List (ℤ×ℤ)): ℕ → (ℤ×ℤ) := λ n ↦ dite (n < rf.length)
  (λ h ↦ rf.get ⟨n,h⟩)
  (λ _ ↦ (0,0))

def folding'' (rf : List (ℤ×ℤ))
:= ∀ k, k < rf.length.pred → nearby' (extend_fold rf k) (extend_fold rf k.succ)

-- Here we have an automated checking whether a finite sequence is a fold:
theorem fr_ext : folding'' rect_fold := by {
  unfold folding''
  decide
}

def rfpi (b:Bool) : ℕ → Bool := λ n ↦ dite (n < 8)
  (λ h ↦ [true,false,true,false,true,false,b,true].reverse.get ⟨n,h⟩)
  (λ _ ↦ false)

def extendBool (p : List Bool) : ℕ → Bool := λ n ↦ dite (n < p.length)
  (λ h ↦ p.get ⟨n,h⟩)
  (λ _ ↦ false)

theorem fr_duh : folding' rfi := by {
  unfold rfi
  have hl: ∀ n, n < rect_fold.length → nearby' (rfi n) (rfi n.succ) := by {
    decide -- so all the "truebelow" and "one_of" stuff was superfluous!?
  }
  have hnl: ∀ n, ¬ n < rect_fold.length → nearby' (rfi n) (rfi n.succ) := by {
    intro n hn; unfold rfi; rw [dif_neg hn]; simp
    have : ¬ n.succ < rect_fold.length := case'' hn
    rw [dif_neg this]; unfold nearby'; right; right; unfold left
    ring_nf; left
  }
  intro n; by_cases h : n < 8; exact hl _ h; exact hnl _ h
}
-- pts_below is the protein folding scoring function
def pts_below (k : ℕ) (phobic : ℕ → Bool) (fold : ℕ → (ℤ×ℤ))
:= List.sum (List.ofFn (λ i : Fin k ↦ pts_at i phobic fold))

def pts_below' (k : ℕ) (phobic : ℕ → Bool) (fold : List (ℤ×ℤ))
:= List.sum (List.ofFn (λ i : Fin k ↦ pts_at i phobic (extend_fold fold)))

def pts_below'' (k : ℕ) (phobic : List Bool) (fold : List (ℤ×ℤ))
:= List.sum (List.ofFn (λ i : Fin k ↦ pts_at i (extendBool phobic.reverse) (extend_fold fold)))

def pts (phobic : List Bool) (fold : List (ℤ×ℤ))
:= List.sum (List.ofFn (λ i : Fin (fold.length) ↦ pts_at i (extendBool phobic.reverse) (extend_fold fold)))


def points (phobic : List Bool) (moves : List Char)
:= pts phobic (fold_of_moves₂ moves)

theorem pts_duh' : pts_below' 8 (rfpi true) (rect_fold) = 3
:= by {
  decide
}

#eval pts_below' 8 (extendBool [true,false,true,false,true,false,true,true].reverse) (rect_fold)
theorem pts_duh'' :
  pts_below' 8 (extendBool [true,false,true,false,true,false,true,true].reverse)
  (rect_fold) = 3
:= by {
  decide
}

theorem pts_duh''' :
  pts_below'' 8 ([true,false,true,false,true,false,true,true])
  (rect_fold) = 3
:= by {
  decide
}

theorem pts_duh'''' :
  pts [true,false,true,false,true,false,true,true]
  (fold_of_moves₂ ['D','S','S','A','A','W','D']) = 3
:= by {
  decide
}

theorem points_example :
  points [true,false,true,false,true,false,true,true]
            ['D',  'S', 'S',  'A', 'A',  'W', 'D'] = 3
:= by {
  decide
}

theorem points_example2 :
  points [true,false,false,true]
            ['D',  'S',  'A'] = 1
:= by {
  decide
}

def mnbv := List.maximum [
  points [true,false,false,true] ['D',  'A',  'A'],
  points [true,false,false,true] ['D',  'W',  'A'],
  points [true,false,false,true] ['D',  'S',  'A'],
  points [true,false,false,true] ['D',  'D',  'A'],
]



def add0 : List ℕ → List ℕ := λ v ↦ 0 :: v


def extend (k:ℕ) (l: List ℕ) : List ℕ :=
ite (l.length < k)
(l ++ List.replicate (k-l.length) 0)
l

-- theorem why_so_slow : ∀ v : Vector (Fin 4) 2,
-- points [true,false,false,true] (moves_of_digits₂ (add0 v.1)) ≤ 1 := by {
--   decide
-- }

-- theorem why_so_slow : ∀ v : List (Fin 4), v.length = 2 →
-- points [true,false,false,true] (moves_of_digits₂ (add0 v)) ≤ 1 := by {
--   decide
-- }


theorem hacky_but_fast : ∀ k : ℕ, k < 4^2 →
points [true,false,false,true]
(moves_of_digits₂ (extend (Nat.succ 2) (add0 (Nat.digits 4 k)))) ≤ 1 := by {
  decide
}

-- theorem hacky_but_fast' : ∀ k : ℕ, k < 4^3 →
-- points [true,false,false,true,false]
-- (moves_of_digits₂ (extend (Nat.succ 3) (add0 (Nat.digits 4 k)))) ≤ 1 := by {
--   decide
-- }


-- #eval extend3 (add0 (Nat.digits 4 0))
-- #eval extend3 (add0 (Nat.digits 4 1))
-- #eval extend3 (add0 (Nat.digits 4 2))
-- #eval extend3 (add0 (Nat.digits 4 3))
-- #eval extend3 (add0 (Nat.digits 4 4))
-- #eval extend3 (add0 (Nat.digits 4 5))
-- #eval extend3 (add0 (Nat.digits 4 6))
-- #eval extend3 (add0 (Nat.digits 4 7))
-- #eval extend3 (add0 (Nat.digits 4 8))
-- #eval extend3 (add0 (Nat.digits 4 9))
-- #eval extend3 (add0 (Nat.digits 4 10))
-- #eval extend3 (add0 (Nat.digits 4 11))
-- #eval extend3 (add0 (Nat.digits 4 12))
-- #eval extend3 (add0 (Nat.digits 4 13))
-- #eval extend3 (add0 (Nat.digits 4 14))
-- #eval extend3 (add0 (Nat.digits 4 15))

-- #eval Nat.digits 4 3
-- #eval Nat.digits 4 4
-- #eval Nat.digits 4 5
-- #eval Nat.digits 4 6
def mnb := List.maximum (
    List.map
    (points [true,false,false,true])
    [
      ['D',  'A',  'A'],
      ['D',  'W',  'A'],
      ['D',  'S',  'A'],
      ['D',  'D',  'A'],
      ['D',  'A',  'D'],
      ['D',  'W',  'D'],
      ['D',  'S',  'D'],
      ['D',  'D',  'D'],
      ['D',  'A',  'S'],
      ['D',  'W',  'S'],
      ['D',  'S',  'S'],
      ['D',  'D',  'S'],
      ['D',  'A',  'W'],
      ['D',  'W',  'W'],
      ['D',  'S',  'W'],
      ['D',  'D',  'W'],
    ]
)

theorem points_example3 :
  mnb = 1
:= by {
  decide
}


-- This shows P(010101b0) ≥ 3 in the paper page 2:
#eval pts_below 8 (rfpi true) rfi
theorem pts_duh (b:Bool) : pts_below 8 (rfpi b) rfi = 3 := by {
  have : b = true ∨ b = false := Bool.eq_false_or_eq_true b
  cases this
  rw [h]; decide
  rw [h]; decide
}
