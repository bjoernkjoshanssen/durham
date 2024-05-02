import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector.Basic
import MyProject.MonoPred
-- import MyProject.FoldPred
set_option tactic.hygienic false

--
-- import MyProject.Backtracking
/-

Start of FoldPredStecher to contain only the part of FoldPred needed here: moves_fin, pts
-/

def extend_fold (rf : List (ℤ×ℤ)): ℕ → (ℤ×ℤ) := λ n ↦ dite (n < rf.length)
  (λ h ↦ rf.get ⟨n,h⟩)
  (λ _ ↦ (0,0))

def move_fin : Fin 4 → ((ℤ×ℤ) → (ℤ×ℤ))
| 0 => λ x ↦ (x.1 + 1,x.2    )
| 1 => λ x ↦ (x.1 - 1,x.2    )
| 2 => λ x ↦ (x.1    ,x.2 + 1)
| 3 => λ x ↦ (x.1    ,x.2 - 1)

def F : Bool → ℕ := λ b ↦ ite (b=true) 1 0

/- Start of old-fashioned -/
def left  (p: ℤ × ℤ) : ℤ × ℤ := (p.1-1,p.2) -- A
def right (p: ℤ × ℤ) : ℤ × ℤ := (p.1+1,p.2) -- D
def up    (p: ℤ × ℤ) : ℤ × ℤ := (p.1  ,p.2+1) -- W
def down  (p: ℤ × ℤ) : ℤ × ℤ := (p.1  ,p.2-1) -- S

def nearby' (p q : ℤ × ℤ) : Prop :=
  q ∈ [down p, up p, left p, right p]

instance (p q : ℤ × ℤ) : Decidable (nearby' p q) := by {
  unfold nearby'
  exact List.instDecidableMemListInstMembershipList q [down p, up p, left p, right p]
}

/- End of old-fashioned -/



/- Start of semi-advanced version -/
def nearby_with₀  {b : ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ)
-- this is good enough to cover three of our HP models
-- in fact all our models could live in Z^3
-- [DecidablePred (λ (i,v,w) ↦ go i v = w)]
-- [∀ i v w, Decidable (go i v = w)]
(p q : ℤ×ℤ) : Bool :=
∃ a : Fin b, q = go a p

def point_achieved_with₁ (go : Fin 4 → ℤ×ℤ → ℤ×ℤ)
  (l : ℕ → (ℤ×ℤ)) (a b : ℕ) (phobic : ℕ → Bool) : Bool
:= by {
  exact phobic a && phobic b && a.succ < b && nearby_with₀ go (l a) (l b)
}

def pts_at_with (go : Fin 4 → ℤ×ℤ → ℤ×ℤ)
(k : ℕ) (ph : ℕ → Bool)
  (f : ℕ → ℤ×ℤ) :=
  List.sum (List.map F (List.ofFn (λ i : Fin k ↦   point_achieved_with₁ (go : Fin 4 → ℤ×ℤ → ℤ×ℤ) f i k ph)))

def points (go : Fin 4 → ℤ×ℤ → ℤ×ℤ) (ph : ℕ → Bool)
  (l : List (ℤ×ℤ)) := List.sum (List.ofFn (λ i : Fin l.length ↦ pts_at_with go i ph (extend_fold l)))

/- End of semi-advanced version -/



def point_achieved''
  (l : ℕ → (ℤ×ℤ)) (a b : ℕ) (phobic : ℕ → Bool) : Bool
:= by {
  exact phobic a && phobic b && a.succ < b && nearby' (l a) (l b)
}


def pts_at (k : ℕ) (ph : ℕ → Bool)
  (f : ℕ → (ℤ×ℤ)) :=
  List.sum (List.map F (List.ofFn (λ i : Fin k ↦   point_achieved'' f i k ph)))

def extendBool (p : List Bool) : ℕ → Bool := λ n ↦ dite (n < p.length)
  (λ h ↦ p.get ⟨n,h⟩) (λ _ ↦ false)


def pts (phobic : List Bool) (fold : List (ℤ×ℤ))
:= List.sum (List.ofFn (λ i : Fin (fold.length) ↦ pts_at i (extendBool phobic.reverse) (extend_fold fold)))

def walk' {α:Type} [OfNat α 0]  {b : ℕ} (go : Fin b → α → α)
  (l : List (Fin b)) :  {l : List α // l ≠ List.nil} := by {
  induction l
  exact ⟨[0], List.cons_ne_nil _ _⟩
  exact ⟨(go head (List.head tail_ih.1 tail_ih.2)) :: tail_ih.1, List.cons_ne_nil _ _⟩
}

def walk {α:Type} [OfNat α 0] {b : ℕ} (go : Fin b → α → α)
(l : List (Fin b)) : List α :=
  (walk' go l.reverse).1


def moves_fin' (l : List (Fin 4)) :  {l : List (ℤ×ℤ) // l ≠ List.nil} :=
  walk' move_fin l
def moves_fin (l : List (Fin 4)) : List (ℤ×ℤ) :=
  walk move_fin l

/- End of FoldPredStecher -/
-- Start of BacktrackingStecher
def Gap (b L k : ℕ) : Type := Vector (Fin b) (L - k)

/- Note that Gap_cons requires the use of L.succ instead of just L. -/
def Gap_cons {n L b:ℕ} (a:Fin b) (w : Gap b L.succ n.succ)
                  (h: ¬ n ≥ L.succ) : Gap b L.succ n
  := ⟨a :: w.1, by {rw [List.length_cons];simp;exact (Nat.succ_sub (Nat.not_lt.mp h)).symm}⟩

def Gap_nil {k b L : ℕ} (h : k ≥ L) : Gap b L k
  := ⟨List.nil, by {rw [Nat.sub_eq_zero_of_le h];rfl}⟩

def those_with_suffix' {k b :ℕ} {L:ℕ} (P: List (Fin b) → Prop) [DecidablePred P]
  (Q: List (Fin b) → Prop) [DecidablePred Q] (w : Gap b L.succ k) : Finset (Vector (Fin b) L.succ) :=
by {
  induction k
  -- Base case:
  exact ((ite (P w.1 ∧ Q w.1) {w} ∅))
  -- Inductive case:
  exact
    (ite (P w.1))
    (
      dite (n ≥ L.succ)
      (λ h ↦ n_ih (Gap_nil h))
      (
        λ h ↦ Finset.biUnion (Finset.univ : Finset (Fin b)) (
          (λ a ↦ (n_ih (Gap_cons a w h)))
        )
      )
    )
    ∅
}
-- end of BacktrackingStecher

set_option tactic.hygienic false
set_option maxHeartbeats 3000000


def first_nonzero_entry (w : List (Fin 4)) : Option (Fin 4) := by {
  induction w
  exact none
  exact ite (tail_ih ≠ none) tail_ih (
    ite (head = 0) none head
  )
}

def myvec (b n : ℕ) : Gap b n n := ⟨[],by simp⟩

def orderly (w: List (Fin 4)) := w.reverse.getLast? = some (0:Fin 4)
      ∧ first_nonzero_entry w = some 2

instance (w : List (Fin 4)) : Decidable (orderly w) := by
  unfold orderly
  exact And.decidable

def stecher_conjecture_counterexample : Prop := by
  let x := [true,false,true,false,true,false, true,true]
  exact
  those_with_suffix'
    (λ w ↦ Function.Injective (λ i ↦ (moves_fin w).get i))
    (
      λ w ↦ pts
        x.reverse
        (moves_fin w) > 2
        ∧ orderly w
    )
    (myvec 4 7) -- 780
  = {⟨[0, 3, 1, 1, 2, 2, 0],rfl⟩}
  ∧ those_with_suffix'
    (λ w ↦ Function.Injective (λ i ↦ (moves_fin w).get i))
    (
      λ w ↦ pts
        (x ++ [false]).reverse
        (moves_fin w) > 2
        ∧ orderly w
    )
    (myvec 4 8) = ∅

instance : Decidable stecher_conjecture_counterexample := by {
  unfold stecher_conjecture_counterexample
  exact And.decidable
}

#eval stecher_conjecture_counterexample
