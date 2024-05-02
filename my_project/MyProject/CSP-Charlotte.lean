import Mathlib.Computability.NFA
import Mathlib.Data.Nat.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Std.Data.Nat.Lemmas
import Mathlib.Data.Matrix.Basic
set_option tactic.hygienic false


-- CONSTRAINT SATISFACTION PROBLEMS
def mytern : Set (Vector Bool 3) := -- (¬ x ∨ ¬ y ∨ ¬ z)
{
  ⟨[false,false,false],rfl⟩,
  ⟨[false,false,true ],rfl⟩,
  ⟨[false,true, false],rfl⟩,
  ⟨[false,true, true ],rfl⟩,
  ⟨[true,false,false],rfl⟩,
  ⟨[true,false,true ],rfl⟩,
  ⟨[true,true, false],rfl⟩
}

structure CSP where
  Carrier : Type
  IsFinite : Fintype Carrier
  ConstraintFamily : (n:ℕ) → Finset (Set (Vector Carrier n))

def constraint (C:CSP) := Σ (n:ℕ) , (
    (Vector ℕ n) × ({F : Set (Vector C.Carrier n) // F ∈ C.ConstraintFamily n})
  )

def boundedConstraint (C:CSP) (b:ℕ) := Σ (n:ℕ) , (
    (Vector (Fin b) n) × ({F : Set (Vector C.Carrier n) // F ∈ C.ConstraintFamily n})
  )

def boundedCSPinstance (C : CSP) (b:ℕ) := List (boundedConstraint C b)
def CSPinstance (C : CSP) := List (constraint C)



instance (C:CSP) :
  Membership (constraint C) (CSPinstance C) := by {
    unfold CSPinstance
    exact List.instMembershipList
  }

  instance (C:CSP) (b:ℕ) :
  Membership (boundedConstraint C b) (boundedCSPinstance C b)
  := by {
    unfold boundedCSPinstance
    exact List.instMembershipList
  }

def satisfiableBounded (C : CSP) (b:ℕ) (P:boundedCSPinstance C b)  : Prop :=
∃ f : (Fin b) → C.Carrier, ∀ Con : boundedConstraint C b, Con ∈ P →
  (Vector.map f Con.2.1) ∈ Con.2.2.1


def satisfiable (C : CSP) (P:CSPinstance C)  : Prop :=
∃ f : ℕ → C.Carrier, ∀ Con : constraint C, Con ∈ P →
  (Vector.map f Con.2.1) ∈ Con.2.2.1

  -- C.1 = 3 ∧ C.2.1 = ⟨[5,6,2],sorry⟩ ∧ mytern = C.2.2.1

def mysatCSP : CSP := {
  Carrier := Bool
  IsFinite := Bool.fintype
  ConstraintFamily := λ n ↦ dite (n=3) (λ h ↦ {
    by {
      let out := mytern
      rw [h]
      exact out
    }
  }) (λ _ ↦ ∅)
}

def mysat : CSPinstance (mysatCSP) :=  [
    ⟨3,(⟨[3,15,7],rfl⟩,⟨
      mytern,
      by {
        unfold mysatCSP
        simp
      }
    ⟩)⟩
  ]
