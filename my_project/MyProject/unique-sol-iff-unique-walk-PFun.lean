import Mathlib.Computability.NFA
import Mathlib.Data.Nat.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Std.Data.Nat.Lemmas
import Mathlib.Data.Matrix.Basic
import MyProject.DecisionProblem
import MyProject.Bjoern
import MyProject.Cursive
import MyProject.Knapsack

set_option tactic.hygienic false

-- set_option maxHeartbeats 10000000

/-
Connect the diophantine equation (a.val 0)x+(a.val 1)y=n with
a walk in a digraph that has a cycle of length (a.val 0) followed by a cycle of length (a.val 1).
-/

-- We can prove my_reduction is a Reduction


def walk_of_solution' (i:KnapsackInstance 2)
  : {p : ℕ×ℕ // i.target.succ = i.wt.val 0 * p.1 + 1 + i.wt.val 1 * p.2}
  → {w : ℕ → ℕ // curs_walks i.wt w ∧ w i.target.succ = i.wt.val 0}
  := by {
    intro p; let k := p.1.1
    exists walk_' i.wt k; constructor
    exact walk_walks' i.wt k; rw [p.2];
    let pfun : Fin 2 → ℕ := λ i ↦ [p.1.1, p.1.2].get i
    exact keep_arriving' i.wt pfun
  }

theorem walk_of_solution_injective' (i:KnapsackInstance 2) :
Function.Injective (walk_of_solution' i) := by {
  unfold Function.Injective
  intro p₁ p₂ hp
  unfold walk_of_solution' at hp
  simp at hp
  have h₁₁: p₁.1.1 = p₂.1.1 := walk__injective' i.wt p₁.1.1 p₂.1.1 hp
  have h₁₂: p₁.1.2 = p₂.1.2 := l_unique' i.wt (Eq.trans p₁.2.symm (by {rw [h₁₁]; exact p₂.2}))
  exact SetCoe.ext (Prod.ext h₁₁ h₁₂)
}

theorem walk_of_solution_surjective' (i:KnapsackInstance 2) :
Function.Surjective (walk_of_solution' i) := by {
  unfold Function.Surjective
  intro wpair
  let ⟨hw,hT⟩ := wpair.2; let k := getk1' i.wt hw hT
  have hwp : wpair.1 = walk_' i.wt k := getk2' i.wt _ _
  rw [hwp] at hT
  rename wpair.1 (Nat.succ i.target) = (i.wt.val 0) => hTold
  let lpair := (getl' i.wt hT); let l := lpair.1
  exists ⟨(k,l), lpair.2⟩; exact SetCoe.ext (id hwp.symm)
}

theorem walk_of_solution_bijective' (i:KnapsackInstance 2) :
Function.Bijective (walk_of_solution' i) := by {
  constructor;
  exact walk_of_solution_injective' i
  exact walk_of_solution_surjective' i
}

theorem main' (i:KnapsackInstance 2) : (∃! p : ℕ×ℕ, i.target.succ = i.wt.val 0 * p.1 + 1 + i.wt.val 1 * p.2)
↔ (∃! w, curs_walks i.wt w ∧ w i.target.succ = i.wt.val 0)
  := unique_iff_of_bijective (walk_of_solution_bijective' i)

-- We can now elegantly get rid of the successor in theorem main:
theorem main_n' {n:ℕ}  (a : PF 2)
: (∃! p : ℕ×ℕ, n = a.val 0 * p.1 + 1 + a.val 1 * p.2)
↔ (∃! w, curs_walks a w ∧ w n = a.val 0) :=
by {
  cases n;
  -- n is 0:
  constructor; intro h; exfalso; rcases h with ⟨p,hp⟩; let g := hp.1
  have : 1 ≤ 0 := calc
         1 ≤ (a.val 0) * p.1 + 1 := Nat.le_add_left 1 ((a.val 0) * p.1)
         _ ≤ (a.val 0) * p.1 + 1 + (a.val 1) * p.2 := Nat.le_add_right ((a.val 0) * p.1 + 1) ((a.val 1) * p.2)
         _ = 0 := self_eq_add_left.mp g
  exact Nat.not_succ_le_zero 0 this

  intro h; exfalso; rcases h with ⟨w,hw⟩; let G := hw.1.2; rw [hw.1.1.1] at G
  exact LT.lt.false (Nat.lt_of_lt_of_eq (a.pos 0) (id G.symm))
  -- n is T.succ:
  let i : KnapsackInstance 2 := {
    target := n_1
    wt := a
  }
  exact main' i
}

theorem fin2cases (i : Fin 2) : i = 0 ∨ i = 1 := by {
  have : i ≤ 1 := Fin.le_last _
  have : i < 1 ∨ i = 1 := by exact lt_or_eq_of_le this
  cases this
  have : i ≤ 0 := by exact Fin.succ_le_succ_iff.mp h
  have : i = 0 := by exact Fin.le_zero_iff.mp this
  left
  exact this
  right
  exact h
}

theorem main_prod' {n:ℕ} (a : PF 2)
: (∃! p : Fin 2 → ℕ, n = a.val 0 * p 0 + 1 + a.val 1 * p 1)
↔ (∃! w, curs_walks a w ∧ w n = a.val 0) :=
by {
  constructor; intro h
  rcases h with ⟨p,hp⟩
  exact (main_n' a).mp (by {
    exists (p 0, p 1); simp
    constructor; exact hp.1
    intro p'0 p'1 hp'; let g := hp.2 (λ i ↦ [p'0, p'1].get i) hp'
    constructor
    exact congr_arg (λ x ↦ x 0) g
    exact congr_arg (λ x ↦ x 1) g
  })
  intro h
  let g := (main_n' a).mpr h
  rcases g with ⟨p,hp⟩
  exists (λ i ↦ [p.1, p.2].get i)
  constructor; simp; exact hp.1; intro p' hp'
  let g := hp.2 (p' 0, p' 1) hp'; apply funext; intro i
  have : i ≤ 1 := Fin.le_last _
  have : i < 1 ∨ i = 1 := by exact lt_or_eq_of_le this
  cases this
  have : i ≤ 0 := by exact Fin.succ_le_succ_iff.mp h_1
  have : i = 0 := by exact Fin.le_zero_iff.mp this
  rw [this]; simp; exact congr_arg (λ x ↦ x.1) g; rw [h_1]
  simp; exact congr_arg (λ x ↦ x.2) g
}

theorem main_dot' {n:ℕ} (a : PF 2)
: (∃! p : Fin 2 → ℕ, n = Matrix.dotProduct a.val p + 1)
↔ (∃! w, curs_walks a w ∧ w n = a.val 0) :=
by {
  constructor; intro h; rcases h with ⟨p,hp⟩
  have : (∃! p : Fin 2 → ℕ, n = (a.val 0) * p 0 + 1 + (a.val 1) * p 1) := by {
    exists p; constructor; let g := hp.1
    unfold Matrix.dotProduct at g; rw [g];
    simp; ring; intro y h
    apply hp.2 y; rw [h]
    have : (a.val 0) * y 0 + 1 + (a.val 1) * y 1 = (a.val 0) * y 0 + (a.val 1) * y 1 + 1 := by ring
    rw [this];
    unfold Matrix.dotProduct
    rfl
  }
  exact (main_prod' a).mp this
  intro h
  have : (∃! p : Fin 2 → ℕ, n = (a.val 0) * p 0 + 1 + (a.val 1) * p 1) := (main_prod' a).mpr h
  rcases this with ⟨p,hp⟩
  exists p; constructor; let g := hp.1; rw [g]; simp;unfold Matrix.dotProduct
  simp; ring
  intro y hy; let g := hp.2 y; simp at g;apply g -- smart!
  rw [hy]; unfold Matrix.dotProduct
  have : (a.val 0) * y 0 + 1 + (a.val 1) * y 1 = (a.val 0) * y 0 + (a.val 1) * y 1 + 1 := by ring
  rw [this]; rfl
}


def my_reduction {c:PNat} (i : KnapsackInstance c) : CursiveWalkInstance c :=
{
  length := i.target.succ
  cycleLength := i.wt
}

def my_reduction' (i : Knapsack2.Instance) : CursiveWalkInstance 2 :=
{
  length := i.target.succ
  cycleLength := i.wt
}

def my_reduction'' (i : Knapsack2.Instance) : CursiveWalk.Instance :=
{
  length := i.target.succ
  cycleLength := i.wt
}


def small_lemma (i:Knapsack2.Instance) (s : Knapsack2Solution i):
  (Nat.succ (Matrix.dotProduct i.wt.val s.val)) =
             (i.wt.val 0 * s.val 0 + 1 + i.wt.val 1 * s.val 1)
      := by {
        have : (i.wt.val 0 * s.val 0 + 1 + i.wt.val 1 * s.val 1) =
               (i.wt.val 0 * s.val 0 + i.wt.val 1 * s.val 1) + 1 := by ring
        rw [this]
        rfl
      }

def walk_of_solution'' (i:Knapsack2.Instance)
: Solution' i → CursiveWalkSolution (my_reduction i)
:= by {
  intro s
  -- let k := s.val 0
  exact {
    w           := walk_' i.wt (s.val 0)
    walks       := walk_walks' _ _
    timed       := by {
      let g := keep_arriving' i.wt s.val
      unfold my_reduction; simp; rw [← g,s.property]
      have : (Nat.succ (Matrix.dotProduct i.wt.val s.val)) =
             (i.wt.val 0 * s.val 0 + 1 + i.wt.val 1 * s.val 1)
      := small_lemma _ _
      exact congr_arg _ this
    }
  }
}

def walk_of_solution''' (i:Knapsack2.Instance)
: Solution' i → CursiveWalkSolution (my_reduction'' i)
:= by {
  intro s
  -- let k := s.val 0
  exact {
    w           := walk_' i.wt (s.val 0)
    walks       := walk_walks' _ _
    timed       := by {
      let g := keep_arriving' i.wt s.val
      unfold my_reduction''; simp; rw [← g,s.property]
      have : (Nat.succ (Matrix.dotProduct i.wt.val s.val)) =
             (i.wt.val 0 * s.val 0 + 1 + i.wt.val 1 * s.val 1)
      := small_lemma _ _
      exact congr_arg _ this
    }
  }
}


theorem main_dot_knapsack' (i : Knapsack2.Instance)
: (∃! p : Fin 2 → ℕ, i.target = Matrix.dotProduct i.wt.val p)
↔ (∃! w, curs_walks i.wt w ∧ w i.target.succ = i.wt.val 0) :=
by {
  constructor; intro h; rcases h with ⟨p,hp⟩; apply (main_dot' i.wt).mp
  exists p; constructor; simp; simp at hp; exact hp.1
  intro y; let g := hp.2 y; simp at g; intro h; simp at h; exact g h

  intro h
  have : (∃! p : Fin 2 → ℕ, i.target.succ = Matrix.dotProduct i.wt.val p + 1) := (main_dot' i.wt).mpr h
  rcases this with ⟨p,hp⟩; exists p; simp; simp at hp; exact hp
}


theorem walk_of_solution_injective'' (i:Knapsack2.Instance) :
Function.Injective (walk_of_solution'' i) := by {
  unfold Function.Injective; intro p₁ p₂ hp; unfold walk_of_solution'' at hp
  simp at hp
  have h₁₁: p₁.val 0 = p₂.val 0 := walk__injective' i.wt _ _ hp
  have hmm : i.target.succ = i.wt.val 0 * p₁.1 0 + 1 + i.wt.val 1 * p₂.1 1
    := by {
      unfold Solution' at p₂; let g := p₂.2
      unfold DecisionProblem.Solution Knapsack2 at g
      unfold Matrix.dotProduct at g; simp at g
      rw [← h₁₁] at g; let g' := congr_arg Nat.succ g
      rw [g',Nat.succ_eq_add_one]; ring
    }
  have : i.wt.val 0 * p₁.val 0 + 1 + i.wt.val 1 * p₁.val 1 =
         i.wt.val 0 * p₁.val 0 + 1 + i.wt.val 1 * p₂.val 1
  := calc
    _ = Nat.succ (Matrix.dotProduct i.wt.val p₁.val) := (small_lemma i p₁).symm
    _ = i.target.succ := congr_arg _ p₁.property.symm
    _ = _ := hmm
  have h₁₂: p₁.val 1 = p₂.val 1 := l_unique' i.wt this
  exact Subtype.eq (by {
    apply funext; intro i; have : i = 0 ∨ i = 1 := fin2cases _
    cases this; rw [h]; exact h₁₁; rw [h]; exact h₁₂
  })
}


theorem walk_of_solution_injective''' (i:Knapsack2.Instance) :
Function.Injective (walk_of_solution''' i) := by {
  unfold Function.Injective; intro p₁ p₂ hp; unfold walk_of_solution''' at hp
  simp at hp
  have h₁₁: p₁.val 0 = p₂.val 0 := walk__injective' i.wt _ _ hp
  have hmm : i.target.succ = i.wt.val 0 * p₁.1 0 + 1 + i.wt.val 1 * p₂.1 1
    := by {
      unfold Solution' at p₂; let g := p₂.2
      unfold DecisionProblem.Solution Knapsack2 at g
      unfold Matrix.dotProduct at g; simp at g
      rw [← h₁₁] at g; let g' := congr_arg Nat.succ g
      rw [g',Nat.succ_eq_add_one]; ring
    }
  have : i.wt.val 0 * p₁.val 0 + 1 + i.wt.val 1 * p₁.val 1 =
         i.wt.val 0 * p₁.val 0 + 1 + i.wt.val 1 * p₂.val 1
  := calc
    _ = Nat.succ (Matrix.dotProduct i.wt.val p₁.val) := (small_lemma i p₁).symm
    _ = i.target.succ := congr_arg _ p₁.property.symm
    _ = _ := hmm
  have h₁₂: p₁.val 1 = p₂.val 1 := l_unique' i.wt this
  exact Subtype.eq (by {
    apply funext; intro i; have : i = 0 ∨ i = 1 := fin2cases _
    cases this; rw [h]; exact h₁₁; rw [h]; exact h₁₂
  })
}

-- theorem main_dot_knapsack'' (i : Knapsack2.Instance)
-- : Nonempty (Unique (Knapsack2Solution i))
-- ↔ Nonempty (Unique (CursiveWalkSolution (my_reduction i)))
-- :=
-- by {
--   rw [unique_iff_exists_unique]
--   rw [unique_iff_exists_unique]
--   let H := main_dot_knapsack' i
--   constructor
--   intro h

--   unfold KnapsackSolution at h
--   rcases h with ⟨s,hs⟩
--   exists {
--     w := walk_' i.wt (s.val 0)
--     walks := sorry
--     timed := sorry
--   }
--   sorry
--   sorry
-- }

-- def my_reduction' : Reduction Knapsack2 CursiveWalk := {
--   Map := λ i ↦ {
--     length := i.target.succ
--     cycleLength := i.wt
--   }
--   Property := λ i ↦ by {
--     constructor
--     intro h
--     rcases h with ⟨p,hp⟩
--     exists walk_' i.wt (p 0)
--     unfold CursiveWalk
--     simp
--     unfold Knapsack2 at hp
--     simp at hp
--     rw [hp]
--     constructor
--     exact walk_walks' _ _
--     let g := keep_arriving' i.wt p
--     rw [← g]
--     have : (Nat.succ (Matrix.dotProduct i.wt.val p)) =
--            (i.wt.val 0 * p 0 + 1 + i.wt.val 1 * p 1) := small_lemma i ⟨p,hp⟩
--     exact congr_arg _ this

--     intro h
--     rcases h with ⟨w,hw⟩
--     unfold Knapsack2
--     simp
--     unfold CursiveWalk at hw
--     simp at hw
--     let k := getk1' i.wt hw.1 hw.2
--     let g := getk2' i.wt hw.1 hw.2
--     rw [g] at hw
--     let l := (getl' i.wt hw.2).1
--     let p := (λ i : Fin 2 ↦ [k,l].get i)
--     exists p
--     let G := keep_arriving' i.wt p
--     -- resurrect keep_arriving_when?
--     sorry -- use "main"
--   }
-- }
