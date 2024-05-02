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
def KI (i : CursiveWalk.Instance): Knapsack2.Instance
:= {
  target := i.length.val.pred
  wt := i.cycleLength
}
def CI (i : Knapsack2.Instance) : CursiveWalk.Instance :=
{
  length := ⟨i.target.succ,Nat.succ_pos _⟩
  cycleLength := i.wt
}

theorem inverses_KCI (i : Knapsack2.Instance) : KI (CI i) = i
  := rfl

theorem inverses_CKI (i : CursiveWalk.Instance) : CI (KI i) = i
  := by {
  unfold KI; unfold CI
  have :  Nat.succ (Nat.pred ↑i.length) = i.length.val := PNat.natPred_add_one _
  simp_rw [this]
  exact rfl
  }

instance : Nonempty CursiveWalk.Instance :=
-- needed for more_inverses
  ⟨1,⟨λ _ ↦ (1:ℕ),by {intro;simp;}⟩⟩


theorem more_inverses : CI = Function.invFun KI := by {
  unfold Function.invFun
  apply funext
  intro i
  have h : ∃ x, KI x = i := by {exists CI i;}
  rw [dif_pos h]
  let P := (λ x ↦ KI x = i)
  have : P (Exists.choose h) := Exists.choose_spec _
  have : KI (Exists.choose h) = i := this
  have : CI (KI (Exists.choose h)) = CI i := congrArg CI this
  have : Exists.choose h = CI i := by {
    rw [inverses_CKI] at this;
    exact this
  }
  exact this.symm
}






theorem CS_property {i:Knapsack2.Instance} (s : Solution_of i) :
  curs_walks i.wt (walk_' i.wt (s.val 0))
  ∧ walk_' i.wt (s.val 0) (Nat.succ i.target) = i.wt.val 0
  := by {
      constructor
      exact walk_walks' _ _
      let G := keep_arriving i.wt s.val
      rw [← G,s.property]
    }

-- theorem CS'_property {j:CursiveWalk.Instance} (s : Solution_of (KI j)) :
--   curs_walks (KI j).wt (walk_' (KI j).wt (s.val 0))
--   ∧ walk_' (KI j).wt (s.val 0) (Nat.succ (KI j).target) = (KI j).wt.val 0
--   := CS_property s

-- The parsimonious function, CursiveWalkSolution_of_KnapsackSolution
def CS {i:Knapsack2.Instance}
 (s : Solution_of i)
: Solution_of (CI i)
:=  {
    val      := walk_' i.wt (s.val 0)
    property := CS_property _
  }

  -- how about a CS' that maps KI i solutions to i solutions?
def CS' {j:CursiveWalk.Instance}
 (s : Solution_of (KI j))
: Solution_of (j)
:=  {
    val      := walk_' (KI j).wt (s.val 0)
    property := by {
      let Q := CS_property s
      unfold DecisionProblem.Solution
      unfold CursiveWalk
      simp
      have : j.cycleLength = (KI j).wt := rfl;
      rw [this]
      have : (KI j).target.succ = j.length.val := PNat.natPred_add_one _
      rw [← this]
      exact Q
    }
  }


-- As needed replace CS i by (λ sc : Solution_of i ↦ CS sc)



-- def move_one (i:Knapsack2.Instance) (s : Fin 2 → ℕ):
--   (Nat.succ (Matrix.dotProduct i.wt.val s)) =
--              (i.wt.val 0 * s 0 + 1 + i.wt.val 1 * s 1)
--   := moveOne i.wt.val s

theorem CS_injective
  (i:Knapsack2.Instance) :
  Function.Injective (λ sc : Solution_of i ↦ CS sc)
  := by {
  unfold Function.Injective; intro p₁ p₂ hp;
  unfold CS at hp
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
-- KnapsackSolution_of_CursiveWalkSolution = KS
-- noncomputable def KS_val  (i : CursiveWalk.Instance):
-- Solution_of i → (Fin 2 → ℕ) :=
-- λ wpair ↦  by {
--   let j := KI i
--   unfold KI at j
--   have : j.target.succ = i.length.val := PNat.natPred_add_one _
--   let ⟨hw,hT⟩ := wpair.2;
--   rw [← this] at hT
--   let k := getk1' j.wt hw hT

--   have hwp : wpair.1 = walk_' j.wt k := getk2' j.wt _ _
--   rw [hwp] at hT
--   let l := (getl j.wt hT).1

--   exact (λ i ↦ [k,l].get i)
--   }
-- noncomputable def KS_val'_of0  (i : CursiveWalk.Instance):
-- Solution_of i → (ℕ) :=
-- -- December 30. This is literally getk1''.
-- λ wpair ↦  getk1'' i wpair
-- noncomputable def KS_val'_of1  (i : CursiveWalk.Instance):
-- Solution_of i → (ℕ) :=
-- λ wpair ↦  by {
--   let j := KI i
--   unfold KI at j
--   have : j.target.succ = i.length.val := PNat.natPred_add_one _
--   let hT := wpair.2.2;
--   rw [← this] at hT
--   let ⟨k,hwp⟩ := getk i wpair
--   rw [hwp] at hT
--   exact (getl j.wt hT).1
--   }


-- noncomputable def KS_val'  (i : CursiveWalk.Instance):
-- Solution_of i → (Fin 2 → ℕ) :=
-- -- December 30
-- λ wpair b ↦
-- ite (b=0) (KS_val'_of0 i wpair)
--           (KS_val'_of1 i wpair)

-- theorem KS_is_getk1''  (i : CursiveWalk.Instance)
-- (wpair : Solution_of i) :
-- KS_val' i wpair 0 = getk1'' i wpair := by {
--   unfold KS_val'
--   rw [if_pos (rfl)]
--   unfold KS_val'_of0
--   simp
-- }

noncomputable def KS_val  (i : CursiveWalk.Instance):
Solution_of i → (Fin 2 → ℕ) :=
-- December 30
λ wpair ↦
by {
  let j := KI i
  unfold KI at j
  have : j.target.succ = i.length.val := PNat.natPred_add_one _
  let hT := wpair.2.2;
  rw [← this] at hT
  let ⟨k,hwp⟩ := getk i wpair
  rw [hwp] at hT
  exact (λ b ↦ [(getk i wpair).1, (getl j.wt hT).1].get b)
  }
theorem KS_is_getk  (i : CursiveWalk.Instance)
(wpair : Solution_of i) :
KS_val i wpair 0 = getk i wpair := by {
  rfl
}
noncomputable def KS {j : CursiveWalk.Instance}
(wpair : Solution_of j) : Solution_of (KI j) :=
 {
  val := KS_val j wpair
  property := by {
    let i := KI j; let ⟨hw,hT⟩ := wpair.2;
    have : i.target.succ = j.length.val := PNat.natPred_add_one _
    rw [← this,(getk _ _).2] at hT;
    rw [(getk _ _).2] at hw;
    have get_getl: KS_val j wpair 1
      = (getl i.wt hT).1 := by {
        unfold KS_val; simp
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



-- December 30, 2023: an inverse of CS
-- noncomputable def KS (j : CursiveWalk.Instance):
-- Solution_of j → Solution_of (KI j) :=
-- λ wpair ↦ {
--   val := KS_val' j wpair
--   property := by {
--     let i := KI j; let ⟨hw,hT⟩ := wpair.2;
--     have : i.target.succ = j.length.val := PNat.natPred_add_one _
--     rw [← this,getk2''] at hT; rw [getk2''] at hw;
--     have get_getl: KS_val' j wpair 1
--       = (getl i.wt hT).1 := by {
--         unfold KS_val'; simp
--         unfold KS_val'_of1; simp
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

theorem inverses_dot1 (j : CursiveWalk.Instance) (wpair : Solution_of j):
wpair.1 = (Eq.mp
  ((congr_arg _ (inverses_CKI j)) : Solution_of (CI (KI j)) = Solution_of j)
  ((λ sc : Solution_of (KI j) ↦ CS sc) (KS wpair))).1 := by {
    unfold CS; unfold KS; simp;
    have : j.cycleLength = (KI j).wt := rfl; simp_rw [← this]

    let wk := walk_' j.cycleLength (getk j wpair).1
    have h₂ : CursiveWalk.Solution ⟨j,wk⟩ := by {
      have : wk = wpair.1 := (getk j wpair).2.symm
      rw [this]
      exact wpair.2
    }
    let H := (getk j wpair).2
    have h₁ : CursiveWalk.Solution ⟨CI (KI j), wk⟩
      := by {simp; rw [inverses_CKI,← H]; exact wpair.2}
    have h₃ : Solution_of (CI (KI j)) = Solution_of j := by rw [inverses_CKI]
    rw [H]
    simp_rw [KS_is_getk]
    have : cast h₃ ⟨wk,h₁⟩ = ⟨wk,h₂⟩
      := cast_val ((CI (KI j))) j wk h₁ h₂ (inverses_CKI j) h₃
    rw [this]
    }


-- theorem inverses_dot1 (j : CursiveWalk.Instance) (wpair : Solution_of j):
-- wpair.1 = (Eq.mp
--   ((congr_arg _ (inverses_CKI j)) : Solution_of (CI (KI j)) = Solution_of j)
--   (CS (KI j) (KS j wpair))).1 := by {
--     unfold CS; unfold KS; unfold KS_val'; simp; unfold KS_val'_of0
--     have : j.cycleLength = (KI j).wt := rfl; simp_rw [← this]

--     let wk := walk_' j.cycleLength (getk1'' j wpair)
--     have h₂ : CursiveWalk.Solution ⟨j,wk⟩ := by {
--       have : wk = wpair.1 := (getk2'' j wpair).symm
--       rw [this]
--       exact wpair.2
--     }
--     let H := getk2'' j wpair
--     have h₁ : CursiveWalk.Solution ⟨CI (KI j), wk⟩
--       := by {simp; rw [inverses_CKI,← H]; exact wpair.2}
--     have h₃ : Solution_of (CI (KI j)) = Solution_of j := by rw [inverses_CKI]
--     have : cast h₃ ⟨wk,h₁⟩ = ⟨wk,h₂⟩
--       := cast_val ((CI (KI j))) j wk h₁ h₂ (inverses_CKI j) h₃
--     rw [H,this]
--     }


-- instance (j : CursiveWalk.Instance) : Nonempty (Solution_of (CI (KI j)))
-- := by {
--   sorry
-- }
-- instance (j : CursiveWalk.Instance) : Nonempty (Solution_of j)
-- := by {
--   sorry
-- }
-- This is type-inconsistent:
-- theorem inverses' (j : CursiveWalk.Instance) (wpair : Solution_of j):
--  CS (KI j) (KS j wpair) = wpair := sorry
-- nor is this
-- theorem inverses' (j : CursiveWalk.Instance) :
--  CS (KI j) = Function.invFun (KS j) := sorry



theorem inverses_CKS_eqmp (j : CursiveWalk.Instance) (wpair : Solution_of j):
-- December 31, 2023.
 -- We first want to prove: CS (KI j) (KS j wpair) = wpair, but that's not type-hygienic so we do:
-- ( by {
--   let wpair' := CS (KI j) (KS j wpair)
--   rw [inverses_CKI] at wpair'
--   exact (wpair = wpair')
-- })
-- which becomes:
wpair = Eq.mp
  ((congr_arg _ (inverses_CKI j)) : Solution_of (CI (KI j)) = Solution_of j)
  (CS (KS wpair))

:= by {
    apply SetCoe.ext -- prove .1's are equal only
    exact inverses_dot1 _ _
}

-- theorem KS_CS_inverses' (j : CursiveWalk.Instance) [Nonempty (Solution_of j)]:
--   CS (KI j) = Function.invFun (KS j)
--   := sorry
-- requires some cast work to be stated, like theorem "invers`es"


theorem inverses'' (ci : CursiveWalk.Instance)  :
id = λ cs ↦ Eq.mp (congr_arg _ (inverses_CKI _)) ((λ sc : Solution_of (KI ci) ↦ CS sc) (KS cs))
  := by {apply funext; intro; exact inverses_CKS_eqmp _ _}

-- theorem KS_surjective'
--   (i:CursiveWalk.Instance) :
--   Function.Surjective (KS i)
--   := by {
--   intro s
--   unfold Solution_of at s
--   let t := CS (KI i) s
--   have : t = CS (KI i) s := rfl
--   unfold CS at this
--   rw [inverses_CKI] at t
--   exists t
--   sorry
--   }

-- theorem inverses_rev' (j : Knapsack2.Instance) (s : Solution_of j):
-- s =
--   (KS (CI j) (CS j s))
-- := by {
--     unfold Solution_of at s
--     let Q := KS_surjective (CI j) s
--     rcases Q with ⟨wpair,hwpair⟩
--     rw [← hwpair]
--     have : wpair = (CS j (KS (CI j) wpair)) := inverses _ _
--     exact congr_arg _ this
-- }

-- Now try not to use the unproven KS_surjective:
theorem inverses_KCS {j : Knapsack2.Instance} (s : Solution_of j):
s =
  (KS ((λ sc : Solution_of j ↦ CS sc) s))
:= by {
    apply CS_injective
    let G := inverses_CKS_eqmp (CI j) ((λ sc : Solution_of j ↦ CS sc) s)
    nth_rewrite 1 [G]
    simp
}



def φ {i : CursiveWalk.Instance} := (congr_arg Solution_of (inverses_CKI i).symm)

def ψ {i : Knapsack2.Instance} := (congr_arg Solution_of (inverses_KCI i))
#check φ

theorem inverses_KCS_eqmp_helper2 {j : Knapsack2.Instance} (sk : Solution_of j)
:
 (φ ▸ (CS sk)) = CS sk
:= by {
  exact rfl
}

-- theorem inverses_KCS_eqmp_helper4 {i : CursiveWalk.Instance} (sc : Solution_of i)
-- :
--  (φ ▸ (sc)) = ( (sc))
-- := by {
--   sorry
-- }


-- theorem inverses_KCS_eqmp_helper3 {i : CursiveWalk.Instance} (sc : Solution_of i)
-- :
-- KS (φ.symm ▸ (sc)) = (KS (sc))
-- := congr_arg (KS) (inverses_KCS_eqmp_helper4 sc)


theorem inverses_KCS_eqmp_helper {j : Knapsack2.Instance} (sk : Solution_of j)
:
KS (φ ▸ (CS sk)) = (KS (CS sk))
:= congr_arg KS (inverses_KCS_eqmp_helper2 sk)



-- theorem inverses_KCS_eqmp {i : CursiveWalk.Instance} (sk : Solution_of (KI i))
-- :
-- KS (φ ▸ (CS sk)) = sk
-- := by {
--   let Q := (inverses_KCS sk)
--   -- simp only [← inverses_CKI] at Q
--   let R := inverses_KCI (KI i)
--   nth_rewrite 2 [Q]
--   simp
--   rw [← inverses_KCS_eqmp_helper sk]
--   -- rw [R]
--   -- have : (φ ▸ CS sk) =  ((fun sc => CS sc) sk)
--   -- := sorry
--   -- exact congr_arg KS this
--   -- let U := inverses_KCS_eqmp_helper3 _
--   let P := inverses_KCS_eqmp_helper2 sk
--   nth_rewrite 1 [← P]

--   simp
--   apply SetCoe.ext

--   unfold Solution_of
--   sorry

--   -- conv =>
--   --   rhs
--   --   congr
--   --   congr
--   --   unfold Solution_of

--     -- lhs
--     -- congr
--     -- arg 1
--     -- congr


--     -- exact inverses_KCS_eqmp_helper _
--     -- why is CI KI doubled up??

--     -- let O := ((λ sc : Solution_of (KI i) ↦ CS sc) sk)

--     -- have : O = ((λ sc : Solution_of (KI i) ↦ CS sc) sk) := rfl
--     -- rw [← this]

--     -- simp only [inverses_CKI] --{single_pass := tt}



--     -- sorry
-- }

theorem KS_injective :
  ∀ (j : CursiveWalk.Instance), Function.Injective fun s : Solution_of j => KS s
  := by {
    intro j s₁ s₂ hs
    simp at hs
    let G₁ := inverses_CKS_eqmp j s₁
    let G₂ := inverses_CKS_eqmp j s₂
    rw [G₁,G₂,hs]
  }

theorem KS_surjective (i:CursiveWalk.Instance) :
  Function.Surjective (λ s : Solution_of i ↦ KS s)
  := by {
  intro s
  exists (
    CS' s
  )
  let G := (inverses_KCS s).symm
  exact G
  }


theorem CS_surjective
  (i:Knapsack2.Instance) :
  Function.Surjective (λ sc : Solution_of i ↦ CS sc)
  := by {
  unfold Function.Surjective
  intro wpair
  let ⟨_,hT⟩ := wpair.2;
  let ⟨k,hwp⟩ := getk (CI i) wpair
  rw [hwp] at hT
  let ⟨l,lproof⟩ := (getl i.wt hT);

  exists ⟨
    (λ i ↦ [k,l].get i),
    by {
      apply Nat.succ_injective
      have hh: (CI i).length = i.target.succ := rfl
      rw [← hh,lproof]
    }
  ⟩
  exact SetCoe.ext (id hwp.symm)
}
def CI_reduction : Reduction Knapsack2 CursiveWalk := {
  Map := CI
  Property := λ i ↦ by {
    constructor
    intro h; rcases h with ⟨p,hp⟩
    let CW := CS ⟨p,hp⟩; exact ⟨CW.1,CW.2⟩

    intro h; rcases h with ⟨w,hw⟩
    let KS := (KS ⟨w,hw⟩); exact ⟨KS.1,KS.2⟩
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

theorem KI_injective : Function.Injective KI := by {
  intro x y h
  have : CI (KI x) = CI (KI y) := congrArg CI h
  rw [inverses_CKI] at this
  rw [inverses_CKI] at this
  exact this
}
theorem CI_injective : Function.Injective CI := by {
  intro x y h
  exact congr_arg KI h
}



theorem KS_CS_inverses (j : Knapsack2.Instance) [Nonempty (Solution_of j)]:
  (λ s : Solution_of (CI j) ↦ KS s) = Function.invFun (λ sc : Solution_of j ↦ CS sc)
  :=
  by {
    unfold Function.invFun
    apply funext
    intro s
    have h : ∃ x, CS x = s := CS_surjective j s
    rw [dif_pos (CS_surjective j s)]
    let P := (λ x ↦ CS x = s)
    have : P (Exists.choose h) := Exists.choose_spec _
    have : CS (Exists.choose h) = s := this
    let H := inverses_KCS (Exists.choose h)
    rw [H]
    simp_rw [this]
  }


theorem K_of_C_jointly_inductive :
Function.Injective (
  λ (⟨i,s⟩ : Σ i' : CursiveWalk.Instance, Solution_of _)
  ↦ ((⟨KI i, KS s⟩) : Σ _ : Knapsack2.Instance, _)
) := jointly_inductive_decision_problem KI_injective KS_injective

theorem C_of_K_jointly_inductive :
Function.Injective (
  λ (⟨i,s⟩ : Σ i' : Knapsack2.Instance, Solution_of _)
  ↦ ((⟨CI i, CS s⟩) : Σ _ : CursiveWalk.Instance, _)
) := jointly_inductive_decision_problem CI_injective CS_injective


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
  }) (λ h ↦ ∅)
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
