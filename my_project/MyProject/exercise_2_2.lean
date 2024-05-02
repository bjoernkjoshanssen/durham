import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fintype.Vector

-- Solution to Exercise 2.2.

def squarefree {b:ℕ} (w: List (Fin b)) : Prop :=
∀ l:ℕ, l < w.length → ∀ v : Vector (Fin b) l,
v.1 ≠ List.nil → ¬ List.IsInfix (v.1 ++ v.1) w

def cubefree {b:ℕ} (w: List (Fin b)) : Prop :=
∀ l:ℕ, l < w.length → ∀ v : Vector (Fin b) l,
v.1 ≠ List.nil → ¬ List.IsInfix (v.1 ++ v.1 ++ v.1) w


instance (b:ℕ) (w : List (Fin b)) : Decidable (squarefree w)
:=
decidable_of_iff (∀ l:ℕ, l < w.length → ∀ v : Vector (Fin b) l,
v.1 ≠ List.nil → ¬ List.IsInfix (v.1 ++ v.1) w
) (by rw [squarefree])

instance (b:ℕ) (w : List (Fin b)) : Decidable (cubefree w)
:=
decidable_of_iff (∀ l:ℕ, l < w.length → ∀ v : Vector (Fin b) l,
v.1 ≠ List.nil → ¬ List.IsInfix (v.1 ++ v.1 ++ v.1) w
) (by rw [cubefree])


example : ∀ w : Vector (Fin 2) 4,
¬ squarefree w.1 := by decide
