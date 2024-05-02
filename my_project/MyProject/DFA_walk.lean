import Mathlib.Computability.DFA
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import MyProject.HydrophobicPolarModel
-- DFA as Walk: Given x : List α, and a DFA M α σ, make a walk in σ.
-- then use getVert

open SimpleGraph

def DFA_of_go {α σ : Type} [OfNat σ 0] (go : α → σ → σ) : DFA α σ := {
  step := λ q a ↦ go a q
  start := 0
  accept := ∅ -- doesn't matter
}

structure SimpleDFA (α σ : Type) extends DFA α σ where
  symm : ∀ q₀ q₁ : σ, ∀ a : α, step q₀ a = q₁ → ∃ b : α, step q₁ b = q₀
  loopless : ∀ q : σ, ∀ a : α, step q a ≠ q

def dfaGraph {α σ : Type} (M : SimpleDFA α σ)
: SimpleGraph σ := {
  Adj := λ q₀ q₁ ↦ ∃ a : α, M.step q₀ a = q₁
  loopless := by
      intro q hc
      obtain ⟨a,ha⟩ := hc
      exact M.loopless q a ha
  symm := by
      intro q₀ q₁ h
      obtain ⟨a,ha⟩ := h
      exact M.symm q₀ q₁ a ha
}


def rectMapInverse : Fin 4 → Fin 4 := λ a ↦ match a with
| 0 => 1
| 1 => 0
| 2 => 3
| 3 => 2

theorem rect_inverse (a : Fin 4) (x : ℤ × ℤ) : rect (rectMapInverse a) (rect a x) = x := by
  unfold rect rectMap rectMapInverse
  match a with
  | 0 => exact add_eq_of_eq_sub rfl
  | 1 => exact add_eq_of_eq_sub rfl
  | 2 => exact add_eq_of_eq_sub rfl
  | 3 => exact add_eq_of_eq_sub rfl

def DFA_rect : SimpleDFA (Fin 4) (ℤ × ℤ) := {
  step   := (DFA_of_go rect).step
  start  := (DFA_of_go rect).start
  accept := (DFA_of_go rect).accept
  symm := by
    intro q₀ q₁ a h
    exists rectMapInverse a

    simp only at *
    unfold DFA.step at *
    unfold DFA_of_go at *
    simp only
    simp only at h
    rw [← h]
    exact rect_inverse _ _
  loopless := by
    intro q a
    unfold DFA.step at *
    unfold DFA_of_go at *
    simp only [ne_eq]
    match a with
    | 0 => unfold rect; simp only [add_right_eq_self, ne_eq];decide
    | 1 => unfold rect; simp only [add_right_eq_self, ne_eq];decide
    | 2 => unfold rect; simp only [add_right_eq_self, ne_eq];decide
    | 3 => unfold rect; simp only [add_right_eq_self, ne_eq];decide
}

def WalkDFA {α σ : Type} (M : SimpleDFA α σ) (x : List α) (q₀ : σ) :
  Walk (dfaGraph M) q₀ (M.evalFrom q₀ x)
  := match x with
  |List.nil => Walk.nil' q₀
  | a :: y  => Walk.cons' q₀ (M.step q₀ a) _
    (by unfold dfaGraph;simp) (WalkDFA M y _)

#eval (DFA_of_go rect).start
#eval (DFA_rect).start
#eval (WalkDFA DFA_rect [0,0,0] 0).getVert 0
#eval (WalkDFA DFA_rect [0,0,0] 0).getVert 1
#eval (WalkDFA DFA_rect [0,0,0] 0).getVert 2
#eval (WalkDFA DFA_rect [0,0,0] 0).getVert 3
#eval (WalkDFA DFA_rect [0,0,0] 0).getVert 4
