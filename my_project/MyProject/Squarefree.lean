import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Nat.Digits

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

theorem suffix_squarefree (b:ℕ) (u v : List (Fin b))
(h: u <:+ v) (hu : squarefree v) : squarefree u := by {
  unfold squarefree; unfold squarefree at hu; intro lx; intro; intro x hx
  rcases h with ⟨t,ht⟩; intro hc
  have h₂: (x.1 ++ x.1).length ≤ u.length :=  List.IsInfix.length_le hc
  rcases hc with ⟨s₀,hs₀⟩; rcases hs₀ with ⟨s₁,hs₁⟩
  have : lx < v.length := calc
        lx  = x.1.length              := x.2.symm
        _   < x.1.length + x.1.length := Nat.lt_add_of_pos_left (List.length_pos.mpr hx)
        _   = (x.1 ++ x.1).length     := (List.length_append x.1 x.1).symm
        _   ≤ u.length                := h₂
        _   ≤ t.length + u.length     := by linarith
        _   = v.length                := by {rw [← List.length_append t u,ht]}
  let G := hu lx this x hx; unfold List.IsInfix at G
  have : ∃ s t, s ++ (x.1 ++ x.1) ++ t = v := by {exists t ++ s₀; exists s₁; rw [← ht,← hs₁]; simp}
  exact G this
}

theorem suffix_cubefree (b:ℕ) (u v : List (Fin b))
(h: u <:+ v) (hu : cubefree v) : cubefree u := by {
  unfold cubefree; unfold cubefree at hu; intro lx; intro; intro x hx
  rcases h with ⟨t,ht⟩; intro hc
  have h₃: (x.1 ++ x.1 ++ x.1).length ≤ u.length :=  List.IsInfix.length_le hc
  rcases hc with ⟨s₀,hs₀⟩; rcases hs₀ with ⟨s₁,hs₁⟩
  have : lx < v.length := calc
        lx  = x.1.length                            := x.2.symm
        _   < x.1.length + x.1.length               := Nat.lt_add_of_pos_left (List.length_pos.mpr hx)
        _   ≤ x.1.length + x.1.length + x.1.length  := Nat.le_add_right _ _
        _   = (x.1 ++ x.1).length + x.1.length      := by rw[(List.length_append x.1 x.1).symm]
        _   = (x.1 ++ x.1 ++ x.1).length            := (List.length_append (x.1 ++ x.1) x.1).symm
        _   ≤ u.length                              := h₃
        _   ≤ t.length + u.length                   := by linarith
        _   = v.length                              := by {rw [← List.length_append t u,ht]}
  let G := hu lx this x hx; unfold List.IsInfix at G
  have : ∃ s t, s ++ (x.1 ++ x.1 ++ x.1) ++ t = v := by {exists t ++ s₀; exists s₁; rw [← ht,← hs₁]; simp}
  exact G this
}
