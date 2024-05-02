import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector.Basic
import MyProject.MonoPred
import MyProject.FoldPred
set_option tactic.hygienic false
set_option maxHeartbeats 3000000

def some_moves : List Char := [
  'D', 'W', 'W', 'A', 'F', 'S', 'A', 'E', 'E', 'D', 'F'
] -- make a CHAR file

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

-- #eval moves_fin []
-- #eval moves_fin [0]
-- #eval moves_fin [0,0]
-- #eval moves_fin [0,1]

-- instance (l: List (Fin 4)) (m : List (ℤ×ℤ)) : Decidable (moves_fin l = m) := sorry

-- #eval moves_fin [(0:Fin 4),1,2,3]

-- #eval Function.Injective (λ i ↦ (moves_fin [0,1,2,3]).get i)
-- This is now a MonoPred

def points (phobic : List Bool) (moves : List Char)
:= pts phobic (fold_of_moves₂ moves)
-- This should use the Fin 4 structure from Backtracking.lean instead of the ad hoc "nearby" function.

-- #eval (fold_of_moves₂ ['D','S','S','A','A','W','D'].reverse).reverse
theorem sdfg : rect_fold = (fold_of_moves₂' ['D','S','S','A','A','W','D'].reverse).1
:= rfl

-- #eval [(0,0),(1,0),(1,-1),(1,-2),(0,-2),(-1,-2),(-1,-1),(0,-1)].reverse

example : pts [true,false,true,false,true,false,true,true] (fold_of_moves₂ ['D','S','S','A','A','W','D']) = 3 := by decide
example : points [true,false,true,false,true,false,true,true] ['D',  'S', 'S',  'A', 'A',  'W', 'D'] = 3 := by decide
example : points [true,false,false,true] ['D',  'S',  'A'] = 1 := by decide

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
