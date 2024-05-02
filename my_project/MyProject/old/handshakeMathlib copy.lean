-- import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Data.Vector.Basic

set_option tactic.hygienic false

/- In response to ICMS referee, actually using the handshake lemma from Mathlib:
theorem SimpleGraph.dart_card_eq_twice_card_edges{V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] [Fintype (Sym2 V)] :
Fintype.card (SimpleGraph.Dart G) = 2 * (SimpleGraph.edgeFinset G).card
-/

instance G₂ : SimpleGraph (Fin 2) := {
  Adj := λ b₀ b₁ ↦ b₀ ≠ b₁
}

instance G₃ : SimpleGraph (Fin 3) := {
  Adj := λ b₀ b₁ ↦ b₀ ≠ b₁
}

lemma cancel₃ (a b : Fin 3)
  (ha : a = a + b)
  : b = 0 := by
  by_contra h₀
  by_cases h₁ : b = 1
  subst h₁
  contrapose ha
  exact self_ne_add_right.mpr h₀
  have : b.1 = 2 := by
    have : b.1 ≤ 2 := Fin.is_le b
    have h₂: b.1 < 2 ∨ b.1 = 2 := Nat.lt_or_eq_of_le this
    cases h₂
    exfalso
    have h₃: b.1 ≤ 1 := Nat.lt_succ.mp h
    have : b.1 < 1 ∨ b.1 = 1 := Nat.lt_or_eq_of_le h₃
    cases this
    have : b.1 = 0 := Nat.lt_one_iff.mp h_1
    have : b = 0 := Fin.ext this
    tauto
    have : b = 1 := Fin.ext h_1
    tauto
    tauto
  have : b = 2 := Fin.ext this
  subst this
  contrapose ha
  exact self_ne_add_right.mpr h₀

instance :  Finite (SimpleGraph.Dart G₃) :=
by
  apply Finite.of_equiv (Fin 3 × Fin 2)
  exact {
    toFun := λ i ↦ by
      exact {
        fst := i.1,snd := i.1 + 1 + i.2,is_adj := by
          unfold SimpleGraph.Adj G₃;simp;
          intro hc
          have : 1 + Fin.castSucc i.2 = 0 := by
            have : i.1 = i.1 + (1 + Fin.castSucc i.2) := by
              nth_rewrite 1 [hc]
              ring
            exact cancel₃ i.1 (1 + Fin.castSucc i.2) this
          sorry
      }
    invFun := λ i ↦ i.1.1
    left_inv := by
      unfold Function.LeftInverse
      intro z
      simp
      sorry
    right_inv := by
      unfold Function.RightInverse Function.LeftInverse
      simp
      intro z
      apply SimpleGraph.Dart.toProd_injective
      apply Prod.ext
      simp
      let Q := z.2
      unfold SimpleGraph.Adj G₃ at Q
      simp at Q
      -- let R := inst_help z.toProd.1 z.toProd.2 Q
      -- exact R
      sorry
      sorry
  }


lemma inst_help (a b : Fin 2) (h : a ≠ b) : a + 1 =b := by
  by_cases ha : a =0
  subst ha
  simp
  exact (Fin.eq_one_of_neq_zero b (id (Ne.symm h))).symm
  have : a = 1 := by exact Fin.eq_one_of_neq_zero a ha
  subst this
  contrapose h
  simp
  rw [Fin.eq_one_of_neq_zero b]
  tauto

instance :  Finite (SimpleGraph.Dart G₂) :=
by
  apply Finite.of_equiv (Fin 2)
  exact {
    toFun := λ i ↦ by
      exact {
        fst := i,snd := i+1,is_adj := by
          unfold SimpleGraph.Adj G₂;simp;
      }
    invFun := λ i ↦ i.1.1
    left_inv := by
      unfold Function.LeftInverse
      intro z
      simp
    right_inv := by
      unfold Function.RightInverse Function.LeftInverse
      simp
      intro z
      apply SimpleGraph.Dart.toProd_injective
      apply Prod.ext
      simp
      simp
      let Q := z.2
      unfold SimpleGraph.Adj G₂ at Q
      simp at Q
      let R := inst_help z.toProd.1 z.toProd.2 Q
      exact R
  }


instance :
  Fintype (SimpleGraph.edgeSet G₂) :=
    by
    sorry

 noncomputable instance :
  Fintype (SimpleGraph.Dart G₂) := by
    apply Fintype.ofFinite

theorem myPractice : Fintype.card (SimpleGraph.Dart G₂) = 2 * (SimpleGraph.edgeFinset G₂).card
  := sorry
