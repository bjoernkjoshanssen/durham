import Mathlib.Computability.NFA
import Mathlib.Data.Nat.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Std.Data.Nat.Lemmas
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Digits
import MyProject.Squarefree
import MyProject.FoldPred
import MyProject.MonoPred
import MyProject.Backtracking
set_option tactic.hygienic false
set_option maxHeartbeats 3000000

def FoldScore_unverified : MonoPred_unverified 4 := {
  P := λ w ↦ Function.Injective (λ i ↦ (moves_fin w).get i)
  Q := λ w ↦ True
}


def FoldScore₃ : MonoPred_unverified 6 := {
  P := λ w ↦ Function.Injective (λ i ↦ (moves_fin₃ w).get i)
  Q := λ w ↦ True
}

instance : DecidablePred (FoldScore_unverified.Q) := by {
  unfold FoldScore_unverified
  simp
  exact Set.decidableUniv
}

instance : DecidablePred (FoldScore_unverified.P) := by {
  unfold FoldScore_unverified
  simp
  unfold Function.Injective
  sorry
  -- unfold moves_fin
  -- unfold moves_fin'
  -- simp
  -- apply?
}

-- def Fold : MonoPred 4 := {
--   P := λ w ↦ Function.Injective (λ i ↦ (moves_fin w).get i)
--   preserved_under_suffixes := by {
--     intro u v huv hi
--     intro x y hxy
--     simp at hxy
--     unfold Function.Injective at hi
--     simp at hi
--     rcases huv with ⟨s,hs⟩
--     symm at hs
--     subst hs
--     have : (moves_fin (s++u)).length = (s++u).length.succ := moves_fin_len _

--     let x'' : Fin ((List.length (moves_fin (u))) + s.length) := Fin.castAdd _ x
--     let y'' : Fin ((List.length (moves_fin (u))) + s.length) := Fin.castAdd _ y


--     have : (moves_fin u).length ≤ (moves_fin (s ++ u)).length := by {
--       rw [moves_fin_len,moves_fin_len]; simp; apply Nat.succ_le_succ_iff.mpr; simp
--     }
--     have hy: y.1 < (moves_fin (s ++ u)).length := calc
--       _ < (moves_fin u).length := y.2
--       _ ≤ _ := this
--     have hx: x.1 < (moves_fin (s ++ u)).length := calc
--       _ < (moves_fin u).length := x.2
--       _ ≤ _ := this
--     let x' : Fin (List.length (moves_fin (s ++ u))) := ⟨x.1,hx⟩
--     let y' : Fin (List.length (moves_fin (s ++ u))) := ⟨y.1,hy⟩

--     have H: moves_fin s <:+ moves_fin (s ++ u) := sorry
--     rcases H with ⟨v,hv⟩
--     have h₂: List.get (moves_fin u) x = List.get (moves_fin (s ++ u)) (x') := by {
--       -- this needs to be "reversed"...?

--       sorry
--     }
--     have h₃: List.get (moves_fin u) y = List.get (moves_fin (s ++ u)) (y') := sorry
--     -- need to know that moves_fin respects extension

--     have h₁: List.get (moves_fin (s ++ u)) (x') = List.get (moves_fin (s ++ u)) y'
--       := by {
--         rw [← h₂, ← h₃]
--         exact hxy
--       }
--     have h₀: x'.1 = y'.1 := congrArg Fin.val (hi h₁)
--     have : x.1 = y.1 := h₀
--     exact Fin.ext this
--   }
-- }

def first_nonzero_entry (w : List (Fin 4)) : Option (Fin 4) := by {
  induction w
  exact none
  exact ite (tail_ih ≠ none) tail_ih (
    ite (head = 0) none head
  )
}

#eval first_nonzero_entry [0,0,2,3,0]
-- def myvec : Vector (Fin 2) (3-1) := ⟨[0,1],rfl⟩


def myvec (b n : ℕ) : Gap b n n := ⟨[],by simp⟩

#eval count_those_with_suffix (CBF 2) (myvec 2 9)

-- From https://oeis.org/A001411 :
#eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_fin₃ w).get i)) (myvec 6 6) -- 16926
#eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_fin₃ w).get i)) (myvec 6 7) -- 81390



-- #eval those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_tri w).get i)) (λ _ ↦ True) myvec32

-- #eval moves_tri [0,2]
-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_tri w).get i)) myvec31
-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_tri w).get i)) myvec32
-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_tri w).get i)) myvec33
-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_tri w).get i)) myvec34
-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_tri w).get i)) myvec35
-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_tri w).get i)) myvec36
-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_tri w).get i)) myvec37
-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_tri w).get i)) myvec38
-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_tri w).get i)) myvec39
-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_tri w).get i)) myvec3A
-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_tri w).get i)) myvec3B
-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_tri w).get i)) myvec3C

-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_hex w).get i)) myvec61 -- 6
-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_hex w).get i)) myvec62 -- 30

-- #eval those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_hex w).get i)) (λ w ↦ True) myvec62 -- 26

-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_hex w).get i)) myvec63 -- 138
-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_hex w).get i)) myvec64 -- 618
-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_hex w).get i)) myvec65 -- 2730
-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_hex w).get i)) myvec66 -- 7810
-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_hex w).get i)) myvec67 -- 31890

-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_fin w).get i)) myvec4C -- 120292


-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_fin w).get i)) myvec4B -- 120292

-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_fin w).get i)) myvec4A -- 44100
-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_fin w).get i)) myvec49 -- 16268
-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_fin w).get i)) myvec48 -- 5916
-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_fin w).get i)) myvec47 -- 2172
-- #eval count_those_with_suffix' (λ w ↦ Function.Injective (λ i ↦ (moves_fin w).get i)) myvec46 -- 780

#eval count_those_with_suffix''
  (λ w ↦ Function.Injective (λ i ↦ (moves_fin w).get i))
  (
    λ w ↦ pts
      [true,false,true,false,true,false, true,true]
      (moves_fin w)
      > 2
  ) -- now let's just
  (myvec 4 8) -- 780

-- #eval count_those_with_suffix''
--   (λ w ↦ Function.Injective (λ i ↦ (moves_fin w).get i))
--   (
--     λ w ↦ pts_at_with move_fin 8
--       (extend_bool [true,false,true,false,true,false, true,true])
--       (moves_fin w)
--       > 2
--   ) -- now let's just
--   myvec48 -- 780


def orderly (w: List (Fin 4)) := w.reverse.getLast? = some (0:Fin 4)
      ∧ first_nonzero_entry w = some 2


#eval those_with_suffix'
  (λ w ↦ Function.Injective (λ i ↦ (moves_fin w).get i))
  (
    λ w ↦ pts
      [true,false,true,false,true,false, true,true].reverse
      (moves_fin w) > 2
      ∧ w.reverse.getLast? = some (0:Fin 4)
      ∧ first_nonzero_entry w = some 2
  )
  (myvec 4 7) -- 780

#eval those_with_suffix'
  (λ w ↦ Function.Injective (λ i ↦ (moves_fin w).get i))
  (
    λ w ↦ pts
      [true,false,true,false,true,false, true,true,false].reverse
      (moves_fin w) > 2
      ∧ w.reverse.getLast? = some (0:Fin 4)
      ∧ first_nonzero_entry w = some 2
  )
  (myvec 4 8) -- 780

def stecher_conjecture_counterexample : Prop :=
those_with_suffix'
  (λ w ↦ Function.Injective (λ i ↦ (moves_fin w).get i))
  (
    λ w ↦ pts
      [true,false,true,false,true,false, true,true].reverse
      (moves_fin w) > 2
      ∧ w.reverse.getLast? = some (0:Fin 4)
      ∧ first_nonzero_entry w = some 2
  )
  (myvec 4 7) -- 780
 = {⟨[0, 3, 1, 1, 2, 2, 0],rfl⟩}
∧ those_with_suffix'
  (λ w ↦ Function.Injective (λ i ↦ (moves_fin w).get i))
  (
    λ w ↦ pts
      [true,false,true,false,true,false, true,true,false].reverse
      (moves_fin w) > 2
      ∧ w.reverse.getLast? = some (0:Fin 4)
      ∧ first_nonzero_entry w = some 2
  )
  (myvec 4 8) = ∅

instance : Decidable stecher_conjecture_counterexample := by {
  unfold stecher_conjecture_counterexample
  exact And.decidable
}

#eval stecher_conjecture_counterexample

-- theorem stecher_conjecture : those_with_suffix'
--   (λ w ↦ Function.Injective (λ i ↦ (moves_fin w).get i))
--   (
--     λ w ↦ pts
--       [true,false,true,false,true,false, true,true].reverse
--       (moves_fin w) > 2
--       ∧ w.reverse.getLast? = some (0:Fin 4)
--       ∧ first_nonzero_entry w = some 2
--   )
--   (myvec 4 7) -- 780
--  = {⟨[0, 3, 1, 1, 2, 2, 0],rfl⟩} := by decide -- SLOW

-- #eval moves_fin [0,1,2,3]

-- #eval those_with_suffix (CBF 2) myvec9  -- NICE
--#eval those_with_suffix (SQF 3) myvec

-- #eval count_those_with_suffix CBF myvec8
-- #eval count_those_with_suffix CBF myvec7
-- example : count_those_with_suffix SQF myvec10 = 0 := by decide

-- #eval count_those_with_suffix CBF (⟨[],rfl⟩ : Gap 10 10) -- 118 cubefree words of length 10
-- but producing a proof takes longer:
-- example : count_those_with_suffix CBF (⟨[],rfl⟩ : Gap 4 4) = 10 := by decide
-- example : count_those_with_suffix CBF (⟨[],rfl⟩ : Gap 5 5) = 16 := by decide
-- example : count_those_with_suffix CBF (⟨[],rfl⟩ : Gap 6 6) = 24 := by decide
--The number of binary cubefree words of length
-- n=1, 2, 3,  4,  5,  6,  7,  8,  9,  10, ... are
--   2, 4, 6, 10, 16, 24, 36, 56, 80, 118, ... (OEIS A028445)
