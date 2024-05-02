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
/-
Connect the diophantine equation (a.val 0)x+(a.val 1)y=n with a walk in a digraph that has a cycle of length (a.val 0) followed by a cycle of length (a.val 1).
-/



-- refactor of walk_of_solution' to reduce use of moveOne
-- and work entirely with instances:
-- def walk_of_solution (i:KnapsackInstance 2)
--   : {p : ℕ×ℕ // i.target = Matrix.dotProduct i.wt.val p}
--   → {w : ℕ → ℕ // curs_walks i.wt w ∧ w i.target.succ = i.wt.val 0}
-- := sorry

-- KnapsackInstance_of_CursiveWalkInstance
def KI_of_CI (i : CursiveWalk.Instance): Knapsack2.Instance
:= {
  target := i.length.val.pred
  wt := i.cycleLength
}
def CI_of_KI (i : Knapsack2.Instance) : CursiveWalk.Instance :=
{
  length := ⟨i.target.succ,Nat.succ_pos _⟩
  cycleLength := i.wt
}

theorem inverses1 (i : Knapsack2.Instance) : KI_of_CI (CI_of_KI i) = i
  := rfl

theorem inverses2 (i : CursiveWalk.Instance) : CI_of_KI (KI_of_CI i) = i
  := by {
  unfold KI_of_CI; unfold CI_of_KI
  have :  Nat.succ (Nat.pred ↑i.length) = i.length.val := PNat.natPred_add_one _
  simp_rw [this]
  exact rfl
  }

instance : Nonempty CursiveWalk.Instance :=
-- needed for more_inverses
  ⟨1,⟨λ _ ↦ (1:ℕ),by {intro;simp;}⟩⟩


theorem more_inverses : CI_of_KI = Function.invFun KI_of_CI := by {
  unfold Function.invFun
  apply funext
  intro i
  have h : ∃ x, KI_of_CI x = i := by {exists CI_of_KI i;}
  rw [dif_pos h]
  let P := (λ x ↦ KI_of_CI x = i)
  have : P (Exists.choose h) := Exists.choose_spec _
  have : KI_of_CI (Exists.choose h) = i := this
  have : CI_of_KI (KI_of_CI (Exists.choose h)) = CI_of_KI i := congrArg CI_of_KI this
  have : Exists.choose h = CI_of_KI i := by {
    rw [inverses2] at this;
    exact this
  }
  exact this.symm
}






theorem CS_of_KS_property {i:Knapsack2.Instance} (s : Solution_of i) :
  curs_walks i.wt (walk_' i.wt (s.val 0))
  ∧ walk_' i.wt (s.val 0) (Nat.succ i.target) = i.wt.val 0
  := by {
      constructor
      exact walk_walks' _ _
      let G := keep_arriving i.wt s.val
      rw [← G,s.property]
    }

-- The parsimonious function, CursiveWalkSolution_of_KnapsackSolution
def CS_of_KS (i:Knapsack2.Instance)
: Solution_of i
→ Solution_of (CI_of_KI i)
:= λ s ↦ {
    val      := walk_' i.wt (s.val 0)
    property := CS_of_KS_property _
  }

-- def move_one (i:Knapsack2.Instance) (s : Fin 2 → ℕ):
--   (Nat.succ (Matrix.dotProduct i.wt.val s)) =
--              (i.wt.val 0 * s 0 + 1 + i.wt.val 1 * s 1)
--   := moveOne i.wt.val s

theorem CS_of_KS_injective
  (i:Knapsack2.Instance) :
  Function.Injective (CS_of_KS i)
  := by {
  unfold Function.Injective; intro p₁ p₂ hp;
  unfold CS_of_KS at hp
  have h₁₁: p₁.val 0 = p₂.val 0
    := walk__injective' i.wt _ _ (congr_arg (λ x ↦ x.1) hp)

  have h₁₂: p₁.val 1 = p₂.val 1 := l_unique i.wt (p₁.val 0) _ _ (by {
    unfold Solution_of at p₂; let g := p₂.2
    unfold DecisionProblem.Solution Knapsack2 at g
    unfold Matrix.dotProduct at g; simp at g
    rw [← h₁₁] at g;
    let G := p₁.2.symm
    have : Matrix.dotProduct i.wt.val p₁.val
    =  (Matrix.dotProduct i.wt.val fun i_1 => List.get [p₁.val 0, p₁.val 1] i_1)
     := by {unfold Matrix.dotProduct;simp}
    rw [← this,G,g]
    unfold Matrix.dotProduct
    simp
  })

  exact Subtype.eq (by {
    apply funext; intro i; have : i = 0 ∨ i = 1 := fin2cases _
    cases this; rw [h]; exact h₁₁; rw [h]; exact h₁₂
  })
}
-- KnapsackSolution_of_CursiveWalkSolution = KS_of_CS
-- noncomputable def KS_of_CS_val  (i : CursiveWalk.Instance):
-- Solution_of i → (Fin 2 → ℕ) :=
-- λ wpair ↦  by {
--   let j := KI_of_CI i
--   unfold KI_of_CI at j
--   have : j.target.succ = i.length.val := PNat.natPred_add_one _
--   let ⟨hw,hT⟩ := wpair.2;
--   rw [← this] at hT
--   let k := getk1' j.wt hw hT

--   have hwp : wpair.1 = walk_' j.wt k := getk2' j.wt _ _
--   rw [hwp] at hT
--   let l := (getl j.wt hT).1

--   exact (λ i ↦ [k,l].get i)
--   }
-- noncomputable def KS_of_CS_val'_of0  (i : CursiveWalk.Instance):
-- Solution_of i → (ℕ) :=
-- -- December 30. This is literally getk1''.
-- λ wpair ↦  getk1'' i wpair
-- noncomputable def KS_of_CS_val'_of1  (i : CursiveWalk.Instance):
-- Solution_of i → (ℕ) :=
-- λ wpair ↦  by {
--   let j := KI_of_CI i
--   unfold KI_of_CI at j
--   have : j.target.succ = i.length.val := PNat.natPred_add_one _
--   let hT := wpair.2.2;
--   rw [← this] at hT
--   let ⟨k,hwp⟩ := getk i wpair
--   rw [hwp] at hT
--   exact (getl j.wt hT).1
--   }


-- noncomputable def KS_of_CS_val'  (i : CursiveWalk.Instance):
-- Solution_of i → (Fin 2 → ℕ) :=
-- -- December 30
-- λ wpair b ↦
-- ite (b=0) (KS_of_CS_val'_of0 i wpair)
--           (KS_of_CS_val'_of1 i wpair)

-- theorem KS_is_getk1''  (i : CursiveWalk.Instance)
-- (wpair : Solution_of i) :
-- KS_of_CS_val' i wpair 0 = getk1'' i wpair := by {
--   unfold KS_of_CS_val'
--   rw [if_pos (rfl)]
--   unfold KS_of_CS_val'_of0
--   simp
-- }

noncomputable def KS_of_CS_val  (i : CursiveWalk.Instance):
Solution_of i → (Fin 2 → ℕ) :=
-- December 30
λ wpair ↦
by {
  let j := KI_of_CI i
  unfold KI_of_CI at j
  have : j.target.succ = i.length.val := PNat.natPred_add_one _
  let hT := wpair.2.2;
  rw [← this] at hT
  let ⟨k,hwp⟩ := getk i wpair
  rw [hwp] at hT
  exact (λ b ↦ [(getk i wpair).1, (getl j.wt hT).1].get b)
  }
theorem KS_is_getk  (i : CursiveWalk.Instance)
(wpair : Solution_of i) :
KS_of_CS_val i wpair 0 = getk i wpair := by {
  rfl
}
noncomputable def KS_of_CS_2024 (j : CursiveWalk.Instance):
Solution_of j → Solution_of (KI_of_CI j) :=
λ wpair ↦ {
  val := KS_of_CS_val j wpair
  property := by {
    let i := KI_of_CI j; let ⟨hw,hT⟩ := wpair.2;
    have : i.target.succ = j.length.val := PNat.natPred_add_one _
    rw [← this,(getk _ _).2] at hT;
    rw [(getk _ _).2] at hw;
    have get_getl: KS_of_CS_val j wpair 1
      = (getl i.wt hT).1 := by {
        unfold KS_of_CS_val; simp
      }
    unfold Knapsack2
    unfold Matrix.dotProduct;
    simp;
    let pro := (getl i.wt hT).2
    apply Nat.succ_injective at pro
    simp_rw [pro]
    unfold Matrix.dotProduct
    simp
    rw [← get_getl,← KS_is_getk]
  }
}



-- December 30, 2023: an inverse of CS_of_KS
-- noncomputable def KS_of_CS (j : CursiveWalk.Instance):
-- Solution_of j → Solution_of (KI_of_CI j) :=
-- λ wpair ↦ {
--   val := KS_of_CS_val' j wpair
--   property := by {
--     let i := KI_of_CI j; let ⟨hw,hT⟩ := wpair.2;
--     have : i.target.succ = j.length.val := PNat.natPred_add_one _
--     rw [← this,getk2''] at hT; rw [getk2''] at hw;
--     have get_getl: KS_of_CS_val' j wpair 1
--       = (getl i.wt hT).1 := by {
--         unfold KS_of_CS_val'; simp
--         unfold KS_of_CS_val'_of1; simp
--       }
--     unfold Knapsack2
--     unfold Matrix.dotProduct; simp;
--     let pro := (getl i.wt hT).2
--     apply Nat.succ_injective at pro
--     simp_rw [KS_is_getk1'',get_getl,pro,]
--     unfold Matrix.dotProduct
--     simp
--   }
-- }



-- theorem inspired_by_dillies {α β: Type} (u₁ u₂ : β) {P : β → α → Prop} (a:α) (h₁ : P u₁ a) (h₂ : P u₂ a) (hu : u₁ = u₂)
-- (h₃ : {a // P u₁ a} = {a // P u₂ a}):
-- cast h₃ (⟨a,h₁⟩) = (⟨a,h₂⟩)
-- := by {subst hu; exact rfl}

-- Thanks to Dillies:
theorem cast_val (u₁ u₂ : CursiveWalk.Instance) (a:ℕ→ℕ)
(h₁ : CursiveWalk.Solution ⟨u₁,a⟩) (h₂ : CursiveWalk.Solution ⟨u₂,a⟩) (hu : u₁ = u₂)
(h₃ : {a // CursiveWalk.Solution ⟨u₁,a⟩} = {a // CursiveWalk.Solution ⟨u₂,a⟩}):
cast h₃ (⟨a,h₁⟩) = (⟨a,h₂⟩)
    := by {subst hu; exact rfl}

theorem inverses_dot1_2024 (j : CursiveWalk.Instance) (wpair : Solution_of j):
wpair.1 = (Eq.mp
  ((congr_arg _ (inverses2 j)) : Solution_of (CI_of_KI (KI_of_CI j)) = Solution_of j)
  (CS_of_KS (KI_of_CI j) (KS_of_CS_2024 j wpair))).1 := by {
    unfold CS_of_KS; unfold KS_of_CS_2024; simp;
    have : j.cycleLength = (KI_of_CI j).wt := rfl; simp_rw [← this]

    let wk := walk_' j.cycleLength (getk j wpair).1
    have h₂ : CursiveWalk.Solution ⟨j,wk⟩ := by {
      have : wk = wpair.1 := (getk j wpair).2.symm
      rw [this]
      exact wpair.2
    }
    let H := (getk j wpair).2
    have h₁ : CursiveWalk.Solution ⟨CI_of_KI (KI_of_CI j), wk⟩
      := by {simp; rw [inverses2,← H]; exact wpair.2}
    have h₃ : Solution_of (CI_of_KI (KI_of_CI j)) = Solution_of j := by rw [inverses2]
    rw [H]
    simp_rw [KS_is_getk]
    have : cast h₃ ⟨wk,h₁⟩ = ⟨wk,h₂⟩
      := cast_val ((CI_of_KI (KI_of_CI j))) j wk h₁ h₂ (inverses2 j) h₃
    rw [this]
    }


-- theorem inverses_dot1 (j : CursiveWalk.Instance) (wpair : Solution_of j):
-- wpair.1 = (Eq.mp
--   ((congr_arg _ (inverses2 j)) : Solution_of (CI_of_KI (KI_of_CI j)) = Solution_of j)
--   (CS_of_KS (KI_of_CI j) (KS_of_CS j wpair))).1 := by {
--     unfold CS_of_KS; unfold KS_of_CS; unfold KS_of_CS_val'; simp; unfold KS_of_CS_val'_of0
--     have : j.cycleLength = (KI_of_CI j).wt := rfl; simp_rw [← this]

--     let wk := walk_' j.cycleLength (getk1'' j wpair)
--     have h₂ : CursiveWalk.Solution ⟨j,wk⟩ := by {
--       have : wk = wpair.1 := (getk2'' j wpair).symm
--       rw [this]
--       exact wpair.2
--     }
--     let H := getk2'' j wpair
--     have h₁ : CursiveWalk.Solution ⟨CI_of_KI (KI_of_CI j), wk⟩
--       := by {simp; rw [inverses2,← H]; exact wpair.2}
--     have h₃ : Solution_of (CI_of_KI (KI_of_CI j)) = Solution_of j := by rw [inverses2]
--     have : cast h₃ ⟨wk,h₁⟩ = ⟨wk,h₂⟩
--       := cast_val ((CI_of_KI (KI_of_CI j))) j wk h₁ h₂ (inverses2 j) h₃
--     rw [H,this]
--     }


-- instance (j : CursiveWalk.Instance) : Nonempty (Solution_of (CI_of_KI (KI_of_CI j)))
-- := by {
--   sorry
-- }
-- instance (j : CursiveWalk.Instance) : Nonempty (Solution_of j)
-- := by {
--   sorry
-- }
-- This is type-inconsistent:
-- theorem inverses' (j : CursiveWalk.Instance) (wpair : Solution_of j):
--  CS_of_KS (KI_of_CI j) (KS_of_CS j wpair) = wpair := sorry
-- nor is this
-- theorem inverses' (j : CursiveWalk.Instance) :
--  CS_of_KS (KI_of_CI j) = Function.invFun (KS_of_CS j) := sorry



theorem inverses (j : CursiveWalk.Instance) (wpair : Solution_of j):
-- December 31, 2023.
 -- We first want to prove: CS_of_KS (KI_of_CI j) (KS_of_CS j wpair) = wpair, but that's not type-hygienic so we do:
-- ( by {
--   let wpair' := CS_of_KS (KI_of_CI j) (KS_of_CS j wpair)
--   rw [inverses2] at wpair'
--   exact (wpair = wpair')
-- })
-- which becomes:
wpair = Eq.mp
  ((congr_arg _ (inverses2 j)) : Solution_of (CI_of_KI (KI_of_CI j)) = Solution_of j)
  (CS_of_KS (KI_of_CI j) (KS_of_CS_2024 j wpair))

:= by {
    apply SetCoe.ext -- prove .1's are equal only
    exact inverses_dot1_2024 _ _
}

-- theorem KS_CS_inverses' (j : CursiveWalk.Instance) [Nonempty (Solution_of j)]:
--   CS_of_KS (KI_of_CI j) = Function.invFun (KS_of_CS j)
--   := sorry
-- requires some cast work to be stated, like theorem "invers`es"


theorem inverses'' (ci : CursiveWalk.Instance)  :
id = λ cs ↦ Eq.mp (congr_arg _ (inverses2 _)) (CS_of_KS (KI_of_CI ci) (KS_of_CS_2024 ci cs))
  := by {apply funext; intro; exact inverses _ _}

-- theorem KS_of_CS_surjective'
--   (i:CursiveWalk.Instance) :
--   Function.Surjective (KS_of_CS i)
--   := by {
--   intro s
--   unfold Solution_of at s
--   let t := CS_of_KS (KI_of_CI i) s
--   have : t = CS_of_KS (KI_of_CI i) s := rfl
--   unfold CS_of_KS at this
--   rw [inverses2] at t
--   exists t
--   sorry
--   }

-- theorem inverses_rev' (j : Knapsack2.Instance) (s : Solution_of j):
-- s =
--   (KS_of_CS (CI_of_KI j) (CS_of_KS j s))
-- := by {
--     unfold Solution_of at s
--     let Q := KS_of_CS_surjective (CI_of_KI j) s
--     rcases Q with ⟨wpair,hwpair⟩
--     rw [← hwpair]
--     have : wpair = (CS_of_KS j (KS_of_CS (CI_of_KI j) wpair)) := inverses _ _
--     exact congr_arg _ this
-- }

-- Now try not to use the unproven KS_of_CS_surjective:
-- theorem inverses_rev {j : Knapsack2.Instance} (s : Solution_of j):
-- s =
--   (KS_of_CS_2024 (CI_of_KI j) (CS_of_KS j s))
-- := by {
--     unfold Solution_of at s
--     unfold KS_of_CS_2024
--     apply SetCoe.ext
--     simp
--     apply funext
--     intro x
--     cases fin2cases x
--     rw [h]
--     unfold KS_of_CS_val
--     simp
--     rw [← KS_is_getk]
--     sorry
--     rw [h]
--     sorry
--     -- let Q := KS_of_CS_surjective (CI_of_KI j) s
--     -- rcases Q with ⟨wpair,hwpair⟩
--     -- rw [← hwpair]
--     -- have : wpair = (CS_of_KS j (KS_of_CS (CI_of_KI j) wpair)) := inverses _ _
--     -- exact congr_arg _ this
-- }

theorem KS_of_CS_injective :
  ∀ (j : CursiveWalk.Instance), Function.Injective fun s => KS_of_CS_2024 j s
  := by {
    intro j s₁ s₂ hs
    simp at hs
    let G₁ := inverses j s₁
    let G₂ := inverses j s₂
    rw [G₁,G₂,hs]
  }

-- theorem inverses_rev_dot1 (j : Knapsack2.Instance) (wpair : Solution_of j):
-- wpair.1 = (
--   (KS_of_CS (CI_of_KI j) (CS_of_KS j wpair))).1 :=
--   by {
--     sorry
--   }

-- theorem KS_of_CS_surjective
--   (i:CursiveWalk.Instance) :
--   Function.Surjective (KS_of_CS i)
--   := by {
--   intro s
--   let G := inverses_rev s
--   let Q := inverses2 i

--   let a' := CS_of_KS (KI_of_CI i) s
--   let b' := KS_of_CS (CI_of_KI (KI_of_CI i)) a'
--   rw [Q] at b'-- have : a' = CS_of_KS (KI_of_CI i) s := rfl
--   rw [Q] at a'
--   exists a'
--   -- simp_rw [Q] at G
--   rw [G]


--   -- apply KS_of_CS_injective
--   sorry
--   }


theorem CS_of_KS_surjective
  (i:Knapsack2.Instance) :
  Function.Surjective (CS_of_KS i)
  := by {
  unfold Function.Surjective
  intro wpair
  let ⟨_,hT⟩ := wpair.2;
  let ⟨k,hwp⟩ := getk (CI_of_KI i) wpair
  rw [hwp] at hT
  let ⟨l,lproof⟩ := (getl i.wt hT);

  exists ⟨
    (λ i ↦ [k,l].get i),
    by {
      apply Nat.succ_injective
      have hh: (CI_of_KI i).length = i.target.succ := rfl
      rw [← hh,lproof]
    }
  ⟩
  exact SetCoe.ext (id hwp.symm)
}
def CI_of_KI_reduction : Reduction Knapsack2 CursiveWalk := {
  Map := CI_of_KI
  Property := λ i ↦ by {
    constructor
    intro h; rcases h with ⟨p,hp⟩
    let CW := CS_of_KS i ⟨p,hp⟩; exact ⟨CW.1,CW.2⟩

    intro h; rcases h with ⟨w,hw⟩
    let KS := (KS_of_CS_2024 (CI_of_KI i) ⟨w,hw⟩); exact ⟨KS.1,KS.2⟩
  }
}


-- Note the following example doesn't require g to be injective.
-- example {α β γ δ: Type} (f : α → β) (g : α → γ → δ)
-- (hf : Function.Injective f)
-- (hg : ∀ x, Function.Injective (λ y  ↦ g x y))
-- : Function.Injective (λ (x,y) ↦ (f x, g x y))
-- := by {
--   intro p₁ p₂ h; let R := hf (congr_arg (λ u ↦ u.1) h)
--   apply Prod.ext; exact R
--   let Q := (congr_arg (λ u ↦ u.2) h)
--   simp at Q; rw [← R] at Q; exact hg p₁.1 Q
-- }

-- Here is a dependent type version. However, the output type δ is constant.
-- example {α β δ: Type} {γ : α → Type} (f : α → β) (g : (a:α) → (γ a) → δ)
-- (hf : Function.Injective f)
-- (hg : ∀ x, Function.Injective (λ y  ↦ g x y))
-- : Function.Injective (λ (p : Σ a : α, γ a) ↦ (f p.fst, g p.fst p.snd))
-- := by {
--   intro ⟨x₁,y₁⟩ ⟨x₂,y₂⟩ h;simp at h;have : x₁ = x₂ := hf h.1;subst this
--   have : y₁ = y₂ := hg x₁ h.2;subst this;rfl
-- }

-- The general statement that can be applied to our case
theorem jointly_inductive_decision_problem
  {I₁ I₂: Type}
  {space₁ : I₁ → Type} {space₂ : I₂ → Type}
  {reduction : I₁ → I₂} {parsimone : (i:I₁) → (space₁ i) → (space₂ (reduction i))}
  (hf : Function.Injective reduction)
  (hg : ∀ i, Function.Injective (λ s  ↦ parsimone i s))
  : Function.Injective (
    λ (⟨i,s⟩ : Σ _ : I₁, space₁ _) ↦ ((⟨reduction i, parsimone i s⟩) : Σ j : I₂, _)
  )
  := by {
    intro ⟨i₁,s₁⟩ ⟨i₂,s₂⟩ h; simp at h; have : i₁ = i₂ := hf h.1
    subst this; simp at h; have : s₁ = s₂ := hg _ h; subst this; rfl
  }

theorem KI_of_CI_injective : Function.Injective KI_of_CI := by {
  intro x y h
  have : CI_of_KI (KI_of_CI x) = CI_of_KI (KI_of_CI y) := congrArg CI_of_KI h
  rw [inverses2] at this
  rw [inverses2] at this
  exact this
}

theorem CI_of_KI_injective : Function.Injective CI_of_KI := by {
  intro x y h
  exact congr_arg KI_of_CI h
}



-- theorem KS_CS_inverses (j : Knapsack2.Instance) [Nonempty (Solution_of j)]:
--   KS_of_CS (CI_of_KI j) = Function.invFun (CS_of_KS j)
--   :=
--   by {
--     unfold Function.invFun
--     apply funext
--     intro s
--     have h : ∃ x, CS_of_KS j x = s := CS_of_KS_surjective j s
--     rw [dif_pos (CS_of_KS_surjective j s)]
--     let P := (λ x ↦ CS_of_KS j x = s)
--     have : P (Exists.choose h) := Exists.choose_spec _
--     have : CS_of_KS j (Exists.choose h) = s := this
--     let H := inverses_rev (Exists.choose h)
--     rw [H]
--     simp_rw [this]
--   }


theorem K_of_C_jointly_inductive :
Function.Injective (
  λ (⟨i,s⟩ : Σ i' : CursiveWalk.Instance, Solution_of _)
  ↦ ((⟨KI_of_CI i, KS_of_CS_2024 i s⟩) : Σ _ : Knapsack2.Instance, _)
) := jointly_inductive_decision_problem KI_of_CI_injective KS_of_CS_injective

theorem C_of_K_jointly_inductive :
Function.Injective (
  λ (⟨i,s⟩ : Σ i' : Knapsack2.Instance, Solution_of _)
  ↦ ((⟨CI_of_KI i, CS_of_KS i s⟩) : Σ _ : CursiveWalk.Instance, _)
) := jointly_inductive_decision_problem CI_of_KI_injective CS_of_KS_injective
