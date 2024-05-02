-- import Mathlib.Algebra.IndicatorFunction
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.MetricSpace.Baire
import Mathlib.Init.Order.Defs
import Mathlib.Topology.Clopen
import Init.Prelude
import Mathlib.Dynamics.Ergodic.MeasurePreserving

set_option tactic.hygienic false
set_option maxHeartbeats 10000000

instance : BaireSpace (ℕ → Bool) := BaireSpace.of_t2Space_locallyCompactSpace

open Set

theorem empty_not_residual
: ∅ ∉ residual (ℕ → Bool) := by
  intro hc
  have : Dense ∅ := dense_of_mem_residual hc
  have : Set.Nonempty (∅:Set (ℕ→Bool)) := (Dense.nonempty_iff this).mpr (Pi.Nonempty)
  contrapose this
  exact not_nonempty_empty

theorem univ_not_meagre: ¬ IsMeagre (univ : Set (ℕ → Bool)) := by
  intro hc
  unfold IsMeagre at hc
  rw [compl_univ] at hc
  exact empty_not_residual hc

/-- This is the topological fact referenced in the proof of Theorem 15
  of E₀ paper.
  By the way, Theorem 15 on https://arxiv.org/pdf/1908.05381.pdf is wrong
  as stated, as it should be "between ≤ₜₜ and ≤T" (consider the complementation map)-/
theorem there_must_be_some (G : ℕ → Set (ℕ → Bool)) (h: ⋃ n, G n = Set.univ) :
  ∃ n, ¬ IsMeagre (G n) := by
    rw [← not_forall]
    intro hc
    have : IsMeagre (⋃ n, G n) := meagre_iUnion hc
    rw [h] at this
    exact univ_not_meagre this



/-- This is from the proof of Theorem 15, except we assume totality.-/
theorem ofbaire
{Ψ : ℕ → (ℕ → Bool) → (ℕ → Bool)}
{F : (ℕ → Bool) → (ℕ → Bool)}
(hcovered : ∀ X, ∃ n, F X = Ψ n X)
: ∃ n, ¬ IsMeagre ({X | F X = Ψ n X} ) :=
by
  apply there_must_be_some
  apply Set.ext
  have : ∀ X, X ∈ ⋃ n, {X | F X = Ψ n X} := λ X ↦ Set.mem_iUnion.mpr (hcovered X)
  tauto

/-- This is from the proof of Theorem 15, dealing with partial functions-/
theorem ofbairePart
{φ : ℕ → (ℕ → Bool) → (ℕ → Part Bool)}
{F : (ℕ → Bool) → (ℕ → Bool)}
{hcovered : ∀ X, ∃ e, ∀ n, ∃ (s : (φ e X n).Dom),   F X n = (φ e X n).get s}

: ∃ e, ¬ IsMeagre (
  {X | ∀ n, ∃ (s : (φ e X n).Dom), F X n = (φ e X n).get s}
) :=
by
  apply there_must_be_some
  apply Set.ext
  have : ∀ X,  X ∈ ⋃ n, {X | ∀ k, ∃ s, F X k = Part.get (φ n X k) s} :=
    λ X ↦ Set.mem_iUnion.mpr (hcovered X)
  tauto


def PartId (A : ℕ → Bool) : (ℕ → Part Bool) := λ n ↦ {
  Dom := true
  get := λ _ ↦ A n
}
def PartId' (A : ℕ → Bool) : (ℕ → Part Bool) := λ n ↦ A n

def PartID : Bool → Part Bool := Part.some

def PartId'' (A : ℕ → Bool) : (ℕ → Part Bool) := λ n ↦ PartID (A n)

-- #check Set.image some {({true}:Set Bool),{false},{true,false},∅}

-- #check Set.image some (Set.powerset ({true,false}:Set Bool))


instance : PartialOrder (Bool) := specializationOrder Bool
instance : Preorder (Part Bool) := PartialOrder.toPreorder
instance : PartialOrder (Part Bool) := Part.instPartialOrderPart


-- The following was intended for Bool but works for any type α.
-- it is a special case of the instance of TopologicalSpace (Option α)
-- below in which α has the discrete topology.
def singletonUnivOption {α : Type} :=  ({(Set.univ : Set (Option α))} : Set (Set (Option α)))
def singletonUnivPart {α : Type} :=  ({(Set.univ : Set (Part α))} : Set (Set (Part α)))


def topologySome {α : Type} [TopologicalSpace α] :=
  { U : Set (Option α) | ∃ V : Set α, IsOpen V ∧ U = some '' V}

def my {α:Type} (u:Part α) (h:u.Dom) := Part.get u h


def topologyGet {α : Type} [TopologicalSpace α] :=
  { U : Set (Part α) | ∃ V : Set α, IsOpen V ∧ U = Part.some '' V} -- don't write "some", write "Part.some"


open Classical
example {α : Type} (x y : α) (h: some x = some y) : x = y :=  Option.some_inj.mp h



/-- The coarsest topology on Part α such that a function f : β → Part α
  is continuous ↔ its restricted to "some" values is continuous.
  basically the same proof as for Option, with Part.some instead of some.-/
instance coolInst {α : Type} (inst : TopologicalSpace α) : TopologicalSpace (Part α) := {
  IsOpen := Set.union singletonUnivPart topologyGet

  isOpen_univ := by
    unfold singletonUnivPart Set.union setOf
    simp
  isOpen_inter := by
    unfold singletonUnivPart Set.union setOf
    simp
    intro A B hA hB
    cases hA
    subst h
    simp
    tauto

    cases hB
    subst h_1
    simp
    tauto
    obtain ⟨Va,hVa⟩ := h
    obtain ⟨Vb,hVb⟩ := h_1
    have : (Part.some '' Va) ∩ (Part.some '' Vb) = Part.some '' (Va ∩ Vb) := by
      apply (image_inter_on _).symm
      intros
      exact Part.some_inj.mp a_2
    have : A ∩ B = Part.some '' (Va ∩ Vb) := by
      rw [← hVa.2, ← hVb.2] at this
      exact this
    have: IsOpen (Va ∩ Vb) := inst.isOpen_inter Va Vb hVa.1 hVb.1
    right
    exists (Va ∩ Vb)

  isOpen_sUnion := by {
    intro U hU
    by_cases hsu : (Set.univ ∈ U)
    left
    unfold singletonUnivPart
    simp
    have : Set.univ ⊆ ⋃₀ U := by
      intro ob
      intro
      exists Set.univ
    exact Set.univ_subset_iff.mp this
    right
    have : ∀ (t : Set (Part α)), t ∈ U → topologyGet t := by
      intro t ht
      let g := hU t ht
      cases g
      unfold singletonUnivPart at h
      simp at h
      exfalso
      rw [h] at ht
      exact hsu ht
      exact h
    exists ⋃₀ {v | Part.some '' v ∈ U}
    constructor

    exact inst.isOpen_sUnion _ (by {
      intro W hW
      let g := this (Part.some '' W) hW
      unfold topologyGet at g
      obtain ⟨V,hV⟩ := g
      have hi: Function.Injective (λ a : α ↦ Part.some a)           := λ  a b h ↦ Part.some_inj.mp h
      have hii: ∀ W V : Set α, Part.some '' W = Part.some '' V → W = V := Set.image_injective.mpr hi
      have : W = V := hii W V hV.2
      subst this
      tauto
    })
    apply Set.ext
    intro ob
    constructor
    intro hoU
    obtain ⟨t,ht⟩ := hoU
    obtain ⟨V,hV⟩ := this t ht.1
    simp
    have : ob ∈ Part.some '' V := by {
      rw [← hV.2]
      exact ht.2
    }
    rcases this with ⟨a,ha⟩
    exists a
    constructor
    exists V
    rw [← hV.2]
    tauto
    tauto
    intro hob
    obtain ⟨v,hv⟩ := hob
    rw [← hv.2]
    obtain ⟨w,hw⟩ := hv.1
    exists (Part.some '' w)
    constructor
    tauto
    exists v
    tauto
  }
}

instance soCoolInst : TopologicalSpace (Part Bool) := coolInst instTopologicalSpaceBool

-- Preorder.topology (Part Bool)
-- is NOT what we want. The open sets should be
-- ∅, {true}, {false}, {true,false}, {true,false, none} only.

instance {α : Type} [t:TopologicalSpace α] :  ℕ → TopologicalSpace (Part α) := λ _ ↦ coolInst t
instance {α : Type} [TopologicalSpace (Part α)] : TopologicalSpace (ℕ → Part α) := Pi.topologicalSpace


instance : TopologicalSpace (ℕ → Part Bool) := Pi.topologicalSpace
example : Continuous PartID := continuous_bot
def myID : Bool → Part Bool := λ b ↦ Part.ofOption (some b)
example : Continuous myID := continuous_bot

example : Continuous PartId'' := by {
  refine continuous_pi ?h
  intro i
  unfold PartId''
  exact Continuous.comp continuous_bot (continuous_apply _)
  }

example : PartId' = PartId'' := rfl

example : PartId = PartId' := by
  repeat (apply funext;intro)
  unfold PartId PartId'
  apply Part.ext
  simp
  tauto


-- Now can we say that if X belongs to a nonmeager Gδ then that's forced?
-- wait... it being forced doesn't mean it holds for all extensions, only that it holds
-- generically... OK but we are using that latter fact to compute the truth tables for F!
-- this should be explained a lot more in the paper.




def E₀ {α:Type} (A B : ℕ → α) : Prop := ∃ a, ∀ n, a ≤ n → A n = B n

-- From Dougherty, Jackson, Kechris 1994:
def E₁ {α:Type} (A B : ℕ → α) : Prop := ∃ n m, ∀ k, A (n+k) = B (m+k)
-- preserving (E₀,E₁) enough for Aut D_T result to work?

def E0 {α: Type} (β : Type) (r : Preorder α) (A B : α → β) : Prop := ∃ a : α, ∀ n, r.le a n → A n = B n

instance myE0 {α β: Type} (h:Nonempty α) (r : Preorder α) (g:IsDirected α r.le): Equivalence (E0 β r) := {
  refl := by {
    intro A;let a := Classical.choice h;exists a;intro n;intro;rfl
  }
  symm := by {intro A B hAB;rcases hAB with ⟨a,ha⟩;exists a;intro n hn;exact (ha n hn).symm}
  trans := by {
    intro A B C hAB hBC;
    rcases hAB with ⟨nab,hnab⟩
    rcases hBC with ⟨nbc,hnbc⟩
    unfold E0
    rcases (g.directed nab nbc) with ⟨a,ha⟩
    exists a
    intro n habc
    exact Eq.trans (hnab n (le_trans ha.1 habc)) (hnbc n (le_trans ha.2 habc))

  }
}

instance NatPreorder : Preorder ℕ := {
  le := Nat.le
  lt := Nat.lt
  le_refl := by {
    intro a
    exact Nat.le_refl a
  }
  le_trans := λ a b c ↦ by {
    intro h₁ h₂
    exact Nat.le_trans h₁ h₂
  }
  lt_iff_le_not_le := by {
    intro a b
    exact Nat.lt_iff_le_not_le
  }
}

instance g:IsDirected ℕ NatPreorder.le := {
  directed := by {
    intro a b
    exists (max a b)
    constructor
    exact Nat.le_max_left a b
    exact Nat.le_max_right a b
  }
}

instance {α:Type}
  (g:IsDirected ℕ NatPreorder.le): Equivalence (@E₀ α) := -- :)
    myE0 instNonempty NatPreorder g

theorem what_is_E₀ {α:Type} : E0 α NatPreorder = E₀ := by {
  apply funext; intro A; unfold E0
  apply funext; intro B; unfold E₀; simp
}

def invariant {α : Type} (E : α → α → Prop) (F : α → α) : Prop :=
∀ A B : α, E A B → E (F A) (F B)

infix:50 " invariant_under " => invariant

def E₀invariant {α:Type} (F : (ℕ → α) → (ℕ → α)) : Prop :=
(E₀ invariant_under F)

-- ∀ A B, E₀ A B → E₀ (F A) (F B)



def uniformlyE₀invariant {α:Type} (F : (ℕ → α) → (ℕ → α)) : Prop :=
  ∀ a, ∃ b, ∀ A B : ℕ → α, (∀ n, a ≤ n → A n = B n) → (∀ n : ℕ, b ≤ n → F A n = F B n)

/- This condition can replace uniform E₀-invariance in `A tractable case`. -/
def uniformlyE₁invariant {α:Type} (F : (ℕ → α) → (ℕ → α)) : Prop :=
  ∀ a₀ a₁, ∃ b₀ b₁, ∀ A B : ℕ → α, (∀ n, A (a₀ + n) =   B (a₁ + n))
                           → (∀ n : ℕ, F A (b₀ + n) = F B (b₁ + n))


theorem uniformly_E₀_invariant_closed_under_composition {α:Type}
  (F G : (ℕ → α) → (ℕ → α)) (hF : uniformlyE₀invariant F) (hG: uniformlyE₀invariant G) :
  uniformlyE₀invariant (λ A ↦ F (G A)) := by
    /-
    If
    1 A=_a B implies G(A) =_g(a) G(B) and
    2 A =_a B implies F(A) =_f(a) F(B) for all A,B then

    A=_a B implies F(G(A)) =_fga F(G(B)) by applying 2 to g a and G A and G B
    -/
    intro a
    obtain ⟨ga, hga⟩  := hG  a -- first deal with F:
    obtain ⟨fga,hfga⟩ := hF ga
    exists fga
    intro A B hAB n hfgan
    exact hfga (G A) (G B) (hga A B hAB) n hfgan

-- #check nonempty_interior_of_iUnion_of_closed

def uniformlyE₀invariantWithBound {α:Type} (F : (ℕ → α) → (ℕ → α)) (g:ℕ→ℕ) : Prop :=
  ∀ a, ∀ A B : ℕ → α, (∀ n, a ≤ n → A n = B n) → (∀ n : ℕ, g a ≤ n → F A n = F B n)

-- can phrase this in terms of a function b=g(a)

/- To make sure that we have the right definitions,
let us check that uniformly E₀-invariant implies E₀-invariant. -/
theorem uniformly_implies {α:Type} (F : (ℕ → α) → (ℕ → α))
  (hu : uniformlyE₀invariant F)
  : E₀ invariant_under F := by
    intro A B hAB
    obtain ⟨n₀,hn₀⟩ := hAB
    obtain ⟨m₀,hm₀⟩ := hu n₀
    exists m₀
    exact hm₀ A B hn₀

/- So here it is: Lemma 11 from E₀ paper. -/
/- Note that we never used that f was surjective! -/

theorem nonempty_image {v:ℕ} {f:ℕ→ℕ} : Finset.Nonempty (Finset.image (Function.invFun f) (Finset.range v.succ))
  := (Finset.Nonempty.image_iff (Function.invFun f)).mpr
     Finset.nonempty_range_succ


def star_ {α:Type} : (ℕ→ℕ)→(ℕ → α)→(ℕ → α):= λ f A n ↦ A (f n)

theorem star_inj_uniformly_E₀_invariant {α:Type} (f : ℕ → ℕ) (hf : Function.Injective f) :
  uniformlyE₀invariant
  (@star_ α f) -- ((λ A : ℕ → Bool ↦ λ n : ℕ ↦ A (f n)))
  := by
    intro a
    rcases a with _ | v

    . exists 0
      intro A B hAB n
      intro
      exact hAB _ (by linarith)

    let S := Finset.image (Function.invFun f) (Finset.range v.succ)
    let b := (Finset.max' S) nonempty_image
    exists b.succ -- now really a = v.succ and we're taking the max of f^{-1} on [0,v]
    intro X Y hXY n hn
    let m := f n
    have h1 : v.succ ≤ m := by {
      by_contra hc
      have : n ∈ S := Finset.mem_image.mpr (by
        exists m
        constructor
        exact Finset.mem_range_succ_iff.mpr (by linarith)
        exact Function.leftInverse_invFun hf _
      )
      have : n ≤ b :=  Finset.le_max' S _ this
      linarith
    }
    exact hXY m h1

noncomputable def theBound (f : ℕ → ℕ) : ℕ → ℕ :=
-- The function a ↦ max {f⁻¹(n) | n < a} = max {m | f(m) < a} if f invertible, 0 ↦ 0
by {
  intro a
  rcases a with _ | v
  exact 0
  let S := Finset.image (Function.invFun f) (Finset.range v.succ)
  exact Nat.succ ((Finset.max' S) nonempty_image)
}

-- def getInverse (f:ℕ → ℕ) (h: Function.Surjective f) : ℕ → ℕ := fun a ↦ Nat.find (h a)
-- If f is only injective, we can still prove uniform E₀ invariance.
-- However, the uniform bound is easier to prove if f is also surjective, since then
-- we can form the finset  {f⁻¹(n) | n < a}
-- otherwise we need to realize {m | f(m) < a} as a finset using injectivity.




 def theBound' (f : ℕ → ℕ) (h: Function.Surjective f): ℕ → ℕ :=
-- The function a ↦ max {f⁻¹(n) | n < a} (= max {m | f(m) < a} if f invertible), 0 ↦ 0
by
  intro a
  cases a --rcases a with _ | v
  . exact 0

  . let finv := λ a : ℕ ↦ Nat.find (h a)
    let S := Finset.image (finv) (Finset.range n.succ)
    exact Nat.succ (Finset.max' S (
        (Finset.Nonempty.image_iff (finv)).mpr Finset.nonempty_range_succ
    )) -- is Nat.succ needed here?


-- example : MeasurableSet (∅ : Set (ℕ → Bool)) := by exact MeasurableSet.empty

-- instance : MeasureTheory.MeasurePreserving (id : (ℕ → Bool) → (ℕ → Bool)) (by
--   exact MeasureTheory.Measure.prod
--   ) (by
--     exact MeasureTheory.Measure.count
--   ) := by
--   exact MeasureTheory.MeasurePreserving.id MeasureTheory.Measure.count



theorem scott_E₀ {α : Type} (f : ℕ → ℕ) (hf : Function.Injective f)
  (p: ℕ → α → α) -- don't need to assume p is a bijection here, nor that f is surjective.
  : uniformlyE₀invariantWithBound (λ A n ↦ (p (f n)) (A (f n))) (theBound f)
   := by
    intro a
    rcases a with _ | v
    . intro A B hAB n
      intro
      simp
      let Q := hAB (f n) (Nat.zero_le _)
      rw [Q]

    . intro A B hAB n h
      have : v.succ ≤ f n := by {
        unfold theBound at h
        let S := Finset.image (Function.invFun f) (Finset.range v.succ)
        by_contra hc
        have hnS: n ∈ S := Finset.mem_image.mpr (by
          exists f n
          constructor
          . exact Finset.mem_range_succ_iff.mpr (Nat.not_lt.mp hc)
          . exact Function.leftInverse_invFun hf n
        )
        have : (Finset.max' S nonempty_image).succ
             ≤ (Finset.max' S nonempty_image) := calc
           _ ≤ n := h
           _ ≤ _ := Finset.le_max' S _ hnS
        linarith
      }
      simp
      let Q := hAB (f n) this
      rw [Q]


/-- Scott domain automorphisms are uniformly E₀-invariant. Apr 24, 2024. -/
theorem scott_auto_E₀ {α : Type} (f : ℕ → ℕ) (hf : Function.Injective f)
  (p: ℕ → { q : α → α // Function.Bijective q})
  : uniformlyE₀invariantWithBound (λ A n ↦ (p (f n)).1 (A (f n))) (theBound f)
   := scott_E₀ f hf (λ n ↦ (p n).1)


theorem unifE₀perm'' {α:Type} (f : ℕ → ℕ) (hf : Function.Injective f) :
  uniformlyE₀invariantWithBound (@star_ α f) (theBound f):= by
  let Q := scott_auto_E₀ f hf (by
    intro
    exact ⟨(id : α → α),Function.bijective_id⟩
  )
  simp at Q
  unfold star_
  exact Q


theorem getFind (f:ℕ → ℕ) (h: Function.Bijective f) (k:ℕ):
  Nat.find (h.2 (f k) : ∃ a, f a = f k) = k :=
  by {
    have : f (Nat.find (h.2 (f k)))
         = f                   k   := Nat.find_spec (h.2 (f k))
    exact h.1 this
  }

-- Now we go for a computable bound, theBound'
theorem unifE₀perm''' {α:Type} (f : ℕ → ℕ) (hf : Function.Bijective f) :
  uniformlyE₀invariantWithBound
  ((λ A : ℕ → α ↦ λ n : ℕ ↦ A (f n)))
  (theBound' f hf.2):=
  by {
    intro a
    rcases a with _ | v
    intro A B hAB n
    intro
    simp
    exact hAB (f n) (Nat.zero_le _)

    intro A B hAB n h
    simp
    have : v.succ ≤ f n := by {
      by_contra hc
      unfold theBound' at h
      let S := Finset.image (λ a : ℕ ↦ Nat.find (hf.2 a)) (Finset.range v.succ)
      have : n ∈ S := Finset.mem_image.mpr (by
        exists f n
        constructor
        . exact Finset.mem_range_succ_iff.mpr (Nat.not_lt.mp hc)
        . exact getFind _ hf _
      )
      have : (Finset.max' S _).succ ≤ (Finset.max' S _) := calc
        _ ≤ n := h
        _ ≤ _ := Finset.le_max' S _ this
      linarith
    }
    exact hAB (f n) this
  }

/-- Now we define and prove some parts of Lemma 12.
  The (questionable) convention is to
  name theorems after the words used in the paper when introducing them.
-/
def pi (n:ℕ) : ℕ → ℕ := λ _ ↦ n

def starpi {α:Type} (n:ℕ) : (ℕ → α)→(ℕ → α) := star_ (pi n)

theorem notethat {α:Type} (n u:ℕ) (A: ℕ → α) : starpi n A u = A n := rfl

theorem so (n:ℕ) (A:ℕ → Bool) :
  starpi n A = (λ _ ↦ true)
∨ starpi n A = (λ _ ↦ false) := by
  by_cases h : (A n = true)
  . left
    apply funext
    intro
    exact h
  . right
    apply funext
    intro
    simp at h
    exact h

def starS {α:Type} : (ℕ → α)→(ℕ → α) := star_ Nat.succ

theorem Notethat {α:Type} (n:ℕ) :
  (λ A ↦ (starpi n) (starS A) : (ℕ → α) → (ℕ → α))
  = starpi n.succ := rfl

theorem Also (n:ℕ) : (λ k ↦ Nat.succ ((pi n) k)) = (pi n.succ) := rfl

axiom Θ {α:Type} : (ℕ → α) → (ℕ → α)
axiom Θinv {α:Type} : (ℕ → α) → (ℕ → α)
axiom theta₁ {α:Type}: Function.LeftInverse (@Θinv α) Θ
axiom theta₂ {α:Type}: Function.RightInverse (@Θinv α) Θ

noncomputable def Φ {α:Type} : (ℕ → α) → (ℕ → α)  := λ A ↦ (Θinv) (starS (Θ A))

theorem hence {α:Type} (n:ℕ): (λ A ↦ ((@starpi α) n) (Θ (Φ A)))
                             = λ A ↦ (starpi n.succ) (Θ A) := by
  apply funext
  intro A
  unfold Φ
  rw [theta₂]
  have : (λ A ↦ (starpi n) (starS A) : (ℕ → α)→(ℕ → α)) (Θ A) = starpi n.succ (Θ A) := by
    rw[Notethat]
  exact this

/-- Example 16 from "A tractable case". Here we need α = Bool. -/
def Φ₁₆ : (ℕ → Bool) → (ℕ → Bool)  := λ A n ↦ (A (2*n)) && (A (2*n).succ)

/-- This is the general Θ_ind.
-/
def Θ_ind (Φ : (ℕ→Bool) → (ℕ→ Bool)) (φ : (ℕ→ Bool) → Bool): (ℕ → Bool) → (ℕ → Bool) := λ A n ↦ match n with
| 0          => φ A
| Nat.succ n => Θ_ind Φ φ (Φ A) n

def Θ₁₆ : (ℕ → Bool) → (ℕ → Bool) :=
  Θ_ind Φ₁₆ (λ A ↦ ((! (A 2)) || (A 3)))

-- λ A n ↦ match n with
-- | 0          => ((! (A 2)) || (A 3))
-- | Nat.succ n => Θ₁₆ (Φ₁₆ A) n


def cantor := ℕ → Bool
instance : TopologicalSpace cantor := by
  unfold cantor
  exact inferInstance

theorem as_in_Lemma_12
  (Φ : (ℕ→ Bool) → (ℕ→ Bool))
  (φ : cantor → Bool)
  : (Θ_ind Φ φ) ∘ Φ = starS ∘ (Θ_ind Φ φ)
  := by
  apply funext
  intro A
  rfl

theorem as_in_Lemma_12₀ : Θ₁₆ ∘ Φ₁₆ = starS ∘ Θ₁₆ := as_in_Lemma_12 _ _

/-- Definition 13 in `A tractable case`. Apr 11, 2024.-/
def searrow {α : Type} (σ : Σ n : ℕ, Fin n → α) (X : ℕ → α) : ℕ → α := by
  intro n
  by_cases h : (n < σ.1)
  exact σ.2 ⟨n,h⟩
  exact X n

/- Definition 3.2 in `Randomness extraction and asymptotic Hamming distance`.-/
def frown {α : Type} (σ : Σ n : ℕ, Fin n → α) (X : ℕ → α) : ℕ → α := by
  intro n
  by_cases h : (n < σ.1)
  exact σ.2 ⟨n,h⟩
  exact X (n - σ.1)

infix:50 " ↘ " => searrow
infix:50 " ⌢ " => frown

/-- From
  https://mathoverflow.net/questions/364808/homeomorphisms-and-mod-finite/364844#364844
-/
def ville_salo : cantor → cantor := λ x ↦
  ⟨1,λ n ↦ x n.1⟩ ⌢ (λ n ↦ xor (x n) (x n.succ))

/-- This can be used several places: -/
-- example {α β : Type} (f g : α → β) (h : f = g) :
--   ∀ x, f x = g x := by exact fun x ↦ congrFun h x

def iterated_xor (X : ℕ → Bool) : ℕ → Bool := by
  intro n
  induction n
  exact X 0
  exact xor n_ih (X n_1.succ)

def iteratedXor (X : ℕ → Bool) : ℕ → Bool := by
  intro n
  match n with
  | 0 => exact X 0
  | Nat.succ k => exact xor (X k.succ) (iteratedXor X k)

-- theorem iterated_xor_equal :
--   iterated_xor = iteratedXor := by
--     apply funext
--     intro A
--     apply funext
--     intro n
--     unfold iterated_xor iteratedXor
--     induction n
--     . simp
--     . simp
--       sorry

-- #eval iterated_xor (λ _ ↦ true) 0
-- #eval iterated_xor (λ _ ↦ true) 1
-- #eval iterated_xor (λ _ ↦ true) 2
-- #eval iterated_xor (λ _ ↦ true) 3
-- #eval iteratedXor (λ _ ↦ true) 0
-- #eval iteratedXor (λ _ ↦ true) 1
-- #eval iteratedXor (λ _ ↦ true) 2
-- #eval iteratedXor (λ _ ↦ true) 3


theorem ville_salo_iteratedXor_id :
  ville_salo ∘ iteratedXor = id := by
  apply funext
  intro Y
  apply funext
  intro n
  induction n
  . rfl
  . unfold ville_salo frown
    simp
    unfold ville_salo frown at n_ih
    simp at n_ih
    by_cases h : n_1 = 0
    . subst h
      simp at n_ih
      unfold iteratedXor
      rw [n_ih]
      cases Y 0
      repeat (cases Y 1;simp;simp)
    . suffices (iteratedXor Y (Nat.succ n_1)) = xor (Y (Nat.succ n_1)) (iteratedXor Y n_1) by
        rw [this]
        cases (iteratedXor Y (n_1))
        repeat simp
      rfl

theorem ville_salo_iterated_xor_id :
  ville_salo ∘ iterated_xor = id := by
  apply funext
  intro Y
  apply funext
  intro n
  induction n
  . rfl
  . unfold ville_salo frown
    simp
    unfold ville_salo frown at n_ih
    simp at n_ih
    by_cases h : (n_1 = 0)
    subst h
    unfold iterated_xor
    simp
    cases Y 0
    repeat simp
    rw [if_neg h] at n_ih
    have : iterated_xor Y (Nat.succ n_1)
    = xor (iterated_xor Y (n_1)) (Y n_1.succ) := rfl
    rw [this]
    cases (iterated_xor Y n_1)
    repeat simp

theorem ville_salo_surjective :
  Function.Surjective ville_salo := by
  intro Y
  exists (iterated_xor Y)
  exact congrFun ville_salo_iterated_xor_id Y

theorem ville_salo_injective :
  Function.Injective ville_salo := by
    intro x y hxy
    apply funext
    intro n
    unfold ville_salo at hxy
    induction n
    simp at hxy
    let Q := congrFun hxy 0
    unfold frown at Q
    simp at Q
    exact Q
    simp at hxy
    let Q := congrFun hxy n_1.succ
    unfold frown at Q
    simp at Q
    rw [n_ih] at Q
    have : ∀ a b₁ b₂ : Bool,
      xor a b₁ = xor a b₂ → b₁ = b₂ := by
        intro a b₁ b₂ h
        have : a = true ∨ a = false := Bool.eq_false_or_eq_true a
        cases this
        . subst h_1
          simp at h
          exact Bool.not_inj h
        . subst h_1
          simp at h
          exact h
    exact this (y n_1) _ _ Q



-- theorem clearly_this_map_is_continuous' :
--   Continuous ville_salo := by
--     refine OpenEmbedding.continuous ?hf
--     refine (openEmbedding_iff ville_salo).mpr ?hf.a
--     constructor
--     refine (embedding_iff ville_salo).mpr ?hf.a.left.a
--     constructor
--     -- apply?
--     sorry
--     . exact ville_salo_injective

--     . rw [range_iff_surjective.mpr ville_salo_surjective]
--       exact isOpen_univ


def is_prefix (σ τ  : Σ n, Fin n → Bool) : Prop :=
  ∃ (h : σ.1 ≤ τ.1), ∀ k : Fin σ.1, σ.2 k = τ.2 ⟨k.1,by
    let Q := k.2
    linarith
  ⟩

def is_prefix' (σ : Σ n, Fin n → Bool) (X : ℕ → Bool) : Prop :=
  ∀ k : Fin σ.1, σ.2 k = X k

/-- As in Lemma 14 of `A tractable case`. -/
def forced_equal_above (F : cantor → cantor) (Φ : cantor → ℕ → Part Bool)
  (σ : Σ n, Fin n → Bool) :=
    ∀ n,
    ∀ τ : Σ n, Fin n → Bool, is_prefix σ τ →
    ∃ ρ : Σ n, Fin n → Bool, is_prefix τ ρ ∧
    ∀ X, is_prefix' ρ X →
    F X n = Φ X n

/-- It is not clear what we gain by insisting that I is an initial segment of ℕ. -/
def condition {α : Type} := Σ I : Finset ℕ, I → Set α

-- def Condition := Σ I : Finset ℕ, I → { s : Set Bool // s ≠ ∅}

def extendedBy {α : Type} (σ τ : @condition α)
 : Prop :=
  ∃ (h : σ.1 ⊆ τ.1), ∀ i (g : i ∈ σ.1), τ.2 ⟨i,by tauto⟩ ⊆ σ.2 ⟨i,g⟩

infix:50 " ≼ " => extendedBy

theorem extendedBy_transitive {α : Type} : Transitive (@extendedBy α) := by
  intro a b c hab hbc
  unfold extendedBy at *
  obtain ⟨h₀,hh₀⟩ := hab
  obtain ⟨h₁,hh₁⟩ := hbc
  exists (by
    show a.1 ⊆ c.1
    calc
      a.1 ⊆ b.1 := h₀
      _ ⊆ c.1 := h₁
  )
  intro j hj
  show c.2 ⟨j,_⟩ ⊆ a.2 ⟨j,_⟩
  calc
    c.2 ⟨j,_⟩ ⊆ b.2 ⟨j,h₀ hj⟩ := hh₁ j _
    _         ⊆ a.2 ⟨j,_⟩ := hh₀ j hj

def extendedByℕ {α : Type}  (σ : @condition α) (X : ℕ → α)
 : Prop :=
  ∀ i (g : i ∈ σ.1), X i ∈ σ.2 ⟨i,g⟩

infix:50 " ≼ " => extendedByℕ


def scott_domain_automorphism_characterization {α : Type} (F : (ℕ → α) → (ℕ → α)) : Prop :=
  ∃ (f : { g : ℕ → ℕ // Function.Bijective g}) (p: ℕ → { q : α → α // Function.Bijective q}),
  F = (λ A n ↦ (p (f.1 n)).1 (A (f.1 n)))

def scott_domain_automorphism_characterization' {α : Type} (F : (ℕ → α) → (ℕ → α)) : Prop :=
  ∃ f : ℕ → ℕ, Function.Bijective f ∧
    ∃ p: ℕ → α → α, (∀ n, Function.Bijective (p n)) ∧
    F = (λ A n ↦ (p (f n)) (A (f n)))

def scott_domain_automorphism {α : Type} (F : (ℕ → α) → (ℕ → α)) : Prop :=
  ∃ G : @condition α → @condition α,
    Function.Bijective G ∧
    (∀ σ τ : @condition α, σ ≼ τ ↔ G σ ≼ G τ)
    ∧ ∀ X : ℕ → α, ∀ σ, σ ≼ X ↔ G σ ≼ F X
-- The conditions under ≼ form a Scott-Ershov domain
-- Really F ∪ G : @condition α ∪ (ℕ → α) is the domain.


theorem extendedBy_transitiveℕ {α : Type} {u v : @condition α}
  {X : ℕ → α} (h₀ : u ≼ v) (h₁ : v ≼ X): u ≼ X := by
    unfold extendedByℕ at *
    unfold extendedBy at h₀
    intro j hj
    obtain ⟨h,h₂⟩ := h₀
    let Q₁ := h₁ j (h hj)
    let Q₂ := h₂ j hj Q₁
    exact Q₂


instance {α : Type} : Trans (@extendedBy α) extendedBy extendedBy := {
  trans := λ h₀ h₁ ↦ extendedBy_transitive h₀ h₁
}




def forcedEqualAbove {α : Type} (F : (ℕ → α) → (ℕ → α)) (Φ : (ℕ → α) → ℕ → Part α)
  (σ : @condition α) :=
    ∀ n,
    ∀ τ : @condition α,  σ ≼ τ → (∃ X : ℕ → α,  τ ≼ X) →
    ∃ ρ : condition, τ ≼ ρ ∧
    (∃ X : ℕ → α, ρ ≼ X) ∧  -- need to add something to ensure the condition has nonempty extension!
    ∀ X : ℕ → α, ρ ≼ X →
    F X n = Φ X n

theorem open_point {α : Type} [TopologicalSpace α] [DiscreteTopology α] (n:ℕ) (b:α)
:
IsOpen {A : ℕ → α | A n = b} := by
  refine isOpen_pi_iff.mpr ?_
  intro A hA
  exists {n}
  exists (λ _ ↦ {b})
  constructor
  intro z hz
  simp at hz
  subst hz
  constructor
  exact isOpen_discrete _
  simp
  exact hA
  intro X hX
  show X n = b
  simp at hX
  tauto

-- instance {α : Type} : TopologicalSpace (ℕ → Part α) := Pi.topologicalSpace

-- This was already declared but it is *so important* to move it to over here:
instance soCoolInst' : TopologicalSpace (Part Bool) := coolInst instTopologicalSpaceBool

lemma open_point_part'
  (n:ℕ) (b:Bool) : IsOpen {A : ℕ → Part Bool | A n = b}
  := by
    -- there's a ℕ → TopologicalSpace (Part Bool) but no
    -- ℕ → TopologicalSpace (Part ℕ)

  refine isOpen_pi_iff.mpr ?h
  intro A hA
  exists {n}
  exists (λ _ ↦ {Part.some b})
  constructor
  intro z hz
  simp at hz
  subst hz
  constructor
  unfold IsOpen TopologicalSpace.IsOpen soCoolInst'
   coolInst
  simp
  right
  unfold topologyGet
  simp
  exists {b}
  . simp

  simp
  exact hA
  intro X hX
  show X n = b
  simp at hX
  tauto


-- #check isOpen_pi_iff

-- This was already declared but it is *so important* to move it to over here:
instance soCoolInst'' {α : Type} [inst: TopologicalSpace α] : TopologicalSpace (Part α) := coolInst inst

lemma open_point_part {α : Type}
  [t : TopologicalSpace α]
  -- [ TopologicalSpace (ℕ → Part α)]
  -- [TopologicalSpace α]
  [DiscreteTopology α]
  -- [ (i:ℕ) → TopologicalSpace (Part α)]
--[TopologicalSpace ((i:ℕ) → Part α)]

  (n:ℕ) (b:α) : IsOpen {A : ℕ → Part α | A n = b}
  := by

  let Q := @isOpen_pi_iff ℕ (λ _ ↦ Part α) (λ _ : ℕ ↦ soCoolInst'') {A : ℕ → Part α | A n = b}
  let R := Q.mpr
  apply R
  -- refine isOpen_pi_iff.mpr ?h
  intro A hA
  exists {n}
  exists (λ _ ↦ {Part.some b})
  constructor
  intro z hz
  simp at hz
  subst hz
  constructor
  unfold IsOpen TopologicalSpace.IsOpen soCoolInst'' coolInst
  simp
  right
  unfold topologyGet
  simp
  exists {b}
  simp

  simp
  exact hA
  intro X hX
  show X n = b
  simp at hX
  tauto

lemma open_value {α : Type} [TopologicalSpace α] [DiscreteTopology α]
  (n:ℕ) (b:α) {F : (ℕ → α) → (ℕ → α)} (h : Continuous F) : IsOpen { A | F A n = b}
  := by
  let Q := h.1 { A : ℕ → α | A n = b} (open_point _ _)
  tauto

lemma open_value_part {α : Type} (n:ℕ) (b:α) {Φ : (ℕ → α) → ℕ → Part α}
  [TopologicalSpace α]
  [DiscreteTopology α]
  --[ TopologicalSpace (ℕ → Part α)]
    (h : Continuous Φ) : IsOpen { A | Φ A n = b}
  := by
  let Q := h.1 { A : ℕ → Part α | A n = b} (open_point_part _ _)
  tauto

def common_extension {α : Type} (σ υ : @condition α) : @condition α := by
      unfold condition
      exact ⟨σ.1 ∪ υ.1, by
        intro k
        by_cases h₁ : (k.1 ∈ σ.fst)
        . by_cases h₂ : (k.1 ∈ υ.fst)
          . exact σ.2 ⟨k.1,h₁⟩ ∩ υ.2 ⟨k.1,h₂⟩
          . exact σ.2 ⟨k.1,h₁⟩
        . by_cases h₂ : (k.1 ∈ υ.fst)
          . exact υ.2 ⟨k.1,h₂⟩
          . exact Set.univ
      ⟩

infix:50 " ⊔ " => common_extension

-- lemma common_extension_symmetric (σ υ : condition) : (σ ⊔ υ) = (υ ⊔ σ) := by
--   unfold common_extension
--   simp
--   sorry

lemma common_extension_extends {α : Type} (σ υ : @condition α) : σ ≼ (σ ⊔ υ)
  := by
      let α := common_extension σ υ
      unfold extendedBy
      have h : σ.1 ⊆ α.1 := by
        intro i hi
        simp
        unfold common_extension
        simp
        left
        exact hi
      exists h
      intro k gk b hb
      unfold common_extension at hb
      simp at hb
      rw [dif_pos gk] at hb
      by_cases h₀ : k ∈ υ.fst
      . rw [dif_pos h₀] at hb
        simp at hb
        tauto
      . rw [dif_neg h₀] at hb
        tauto

lemma common_extension_extends' {α : Type}  (σ υ : @condition α) : υ ≼ (σ ⊔ υ)
  := by
      let α := common_extension σ υ
      unfold extendedBy
      have h : υ.1 ⊆ α.1 := by
        intro i hi
        simp
        unfold common_extension
        simp
        right
        exact hi
      exists h
      intro k gk b hb
      unfold common_extension at hb
      simp at hb
      rw [dif_pos gk] at hb
      by_cases h₀ : k ∈ σ.fst
      . rw [dif_pos h₀] at hb
        rw [dif_pos gk] at hb
        simp at hb
        tauto
      . rw [dif_neg h₀] at hb
        tauto

lemma open_variety (F G : (ℕ → Bool) → (ℕ → Bool)) (hF: Continuous F) (hG: Continuous G) (n:ℕ): IsOpen {A | F A n = G A n}
  := by
  have h₀ : IsOpen {A | F A n = true} := open_value n true hF
  have h₁ : IsOpen {A | G A n = true} := open_value n true hG
  have h₀₁ : IsOpen ({A | F A n = true} ∩ {A | G A n = true}) := IsOpen.inter h₀ h₁
  have h₂ : IsOpen {A | F A n = false} := open_value n false hF
  have h₃ : IsOpen {A | G A n = false} := open_value n false hG
  have h₂₃ : IsOpen ({A | F A n = false} ∩ {A | G A n = false}) := IsOpen.inter h₂ h₃
  have : {A | F A n = G A n} = ({A | F A n = true} ∩ {A | G A n = true})
    ∪ ({A | F A n = false} ∩ {A | G A n = false}) := by
      apply Set.ext;intro A;simp;constructor;intro h;by_cases hF: (F A n)
      left;constructor;tauto;symm;rw [hF] at h;tauto;right;constructor
      exact Bool.eq_false_iff.mpr hF;rw [h] at hF
      exact Bool.eq_false_iff.mpr hF;intro h;cases h;repeat rw [h_1.1,h_1.2]
  rw [this]
  exact IsOpen.union h₀₁ h₂₃

/-- Apr 11, 2024 : -/
lemma open_variety_part (F : (ℕ → Bool) → ℕ → Bool) (Φ : (ℕ → Bool) → ℕ → Part Bool) (hF: Continuous F) (hΦ: Continuous Φ) (n:ℕ):
  IsOpen {A | F A n = Φ A n} := by
  have h₀ : ∀ b, IsOpen {A | F A n = b} := λ b ↦ open_value n b hF
  have h₁ : IsOpen {A | Φ A n = true} := open_value_part n true hΦ
  have h₀₁ : IsOpen ({A | F A n = true} ∩ {A | Φ A n = true}) := IsOpen.inter (h₀ true) h₁
  have h₃ : IsOpen {A | Φ A n = false} := open_value_part n false hΦ
  have h₂₃ : IsOpen ({A | F A n = false} ∩ {A | Φ A n = false}) := IsOpen.inter (h₀ false) h₃
  have : {A | F A n = Φ A n} = ({A | F A n = true} ∩ {A | Φ A n = true})
    ∪ ({A | F A n = false} ∩ {A | Φ A n = false}) := by
      apply Set.ext;intro A;simp;constructor;intro h;by_cases hF: (F A n)
      left;constructor;tauto;symm;rw [hF] at h;tauto;right;constructor
      exact Bool.eq_false_iff.mpr hF;
      rw [← h]
      simp
      exact Bool.eq_false_iff.mpr hF;intro h;cases h;repeat rw [h_1.1,h_1.2]
  rw [this]
  exact IsOpen.union h₀₁ h₂₃

lemma extend_more (α β : condition) (X : ℕ → Bool)
  (hα : α ≼ X)
  (hβ : β ≼ X)
  :
  (α ⊔ β) ≼ X := by
    unfold extendedByℕ
    intro j hj
    unfold common_extension at *
    simp
    simp at hj
    cases hj
    . rw [dif_pos h]
      by_cases H : j ∈ β.1
      . rw [dif_pos H]
        simp
        constructor
        . exact hα j h
        . exact hβ j H
      . rw [dif_neg H]
        exact hα j h
    . by_cases H : j ∈ α.1
      . rw [dif_pos H]
        rw [dif_pos h]
        constructor
        . exact hα j H
        . exact hβ j h
      . rw [dif_neg H]
        rw [dif_pos h]
        exact hβ j h

lemma join_extendedBy {α : Type} (a b : @condition α) (X : ℕ → α) (ha : a ≼ X) (hb : b ≼ X)
: (a ⊔ b) ≼ X := by
  unfold extendedByℕ at *
  intro j hj
  unfold common_extension at hj
  simp at hj
  unfold common_extension

  simp
  cases hj
  . rw [dif_pos h]
    by_cases H : j ∈ b.1
    . rw [dif_pos H]
      simp
      constructor
      . exact ha j h
      . exact hb j H
    . rw [dif_neg H]
      exact ha j h
  . rw [dif_pos h]
    by_cases H : j ∈ a.1
    . rw [dif_pos H]
      rw [dif_pos h]
      simp
      constructor
      . exact ha j H
      . exact hb j h
    . rw [dif_neg H]
      exact hb j h

-- In the next three items we characterize extendable conditions.
noncomputable def extender {α : Type} [Inhabited α] (σ : @condition α) :
(∀ i, ∀ hi : i ∈ σ.1, σ.2 ⟨i,hi⟩ ≠ ∅) → (ℕ → α) := by
  intro h n
  by_cases hn : n ∈ σ.1
  . have : Nonempty (σ.2 ⟨n,hn⟩) := nonempty_iff_ne_empty'.mpr (h n hn)
    let p := Classical.choice this
    exact (p:α)
  . exact (Inhabited.default : α) -- or false, for that matter

theorem extending {α : Type} [Inhabited α] (σ : condition)
  (hσ : ∀ i, ∀ hi : i ∈ σ.1, σ.2 ⟨i,hi⟩ ≠ ∅)
  : σ ≼ (@extender α _ σ hσ) := by
    intro n hn
    unfold extender
    rw [dif_pos hn]
    simp

theorem extendibility₀ (σ : condition) :
(∃ X : ℕ → Bool, σ ≼ X) ↔ (∀ i, ∀ hi : i ∈ σ.1, σ.2 ⟨i,hi⟩ ≠ ∅) := by
  constructor
  . intro h
    obtain ⟨X,hX⟩ := h
    intro i
    intro hi
    let Q := nonempty_of_mem (hX i hi)
    exact Nonempty.ne_empty Q
  . intro hσ
    exists extender σ hσ
    exact extending _ _

theorem my_isCompact_iff_finite_subcover₀  {α : Type} [TopologicalSpace α] [DiscreteTopology α]
(F : (ℕ → α) → (ℕ → α)) (n:ℕ)
 {s : Set (ℕ → α)} :
IsCompact s → ∀ (U : { τ : condition // ∀ Y₁ Y₂ : (ℕ → α), τ ≼ Y₁ → τ ≼ Y₂ → F Y₁ n = F Y₂ n} → Set (ℕ → α)),
(∀ (i : { τ : condition // ∀ Y₁ Y₂ : (ℕ → α), τ ≼ Y₁ → τ ≼ Y₂ → F Y₁ n = F Y₂ n}), IsOpen (U i))
→ s ⊆ ⋃ (i : { τ : condition // ∀ Y₁ Y₂ : (ℕ → α), τ ≼ Y₁ → τ ≼ Y₂ → F Y₁ n = F Y₂ n}), U i
→ ∃ (t : Finset { τ : condition // ∀ Y₁ Y₂ : (ℕ → α), τ ≼ Y₁ → τ ≼ Y₂ → F Y₁ n = F Y₂ n}), s ⊆ ⋃ i ∈ t, U i
:= by
  let Q := (@isCompact_iff_finite_subcover (ℕ → α))
  intro hs
  apply Q.mp
  exact hs

def good_cond {α : Type} (F : (ℕ → α) → (ℕ → α)) (n: ℕ) := { τ : condition // ∀ Y₁ Y₂ : (ℕ → α), τ ≼ Y₁ → τ ≼ Y₂ → F Y₁ n = F Y₂ n}

theorem my_isCompact_iff_finite_subcover₁ {α : Type} [ TopologicalSpace α] [DiscreteTopology α]
  [CompactSpace (ℕ → α)]
  (F : (ℕ → α) → (ℕ → α)) (n:ℕ):
(∀ (σ : { τ : condition // ∀ Y₁ Y₂ : (ℕ → α), τ ≼ Y₁ → τ ≼ Y₂ → F Y₁ n = F Y₂ n}),
 IsOpen ({X : (ℕ → α) | σ ≼ X}))
→ (Set.univ : Set (ℕ → α)) ⊆ ⋃ (σ : { τ : condition // ∀ Y₁ Y₂ : (ℕ → α), τ ≼ Y₁ → τ ≼ Y₂ → F Y₁ n = F Y₂ n}),
{X : (ℕ → α) | σ ≼ X}
  → ∃ (t : Finset { τ : condition // ∀ Y₁ Y₂ : (ℕ → α), τ ≼ Y₁ → τ ≼ Y₂ → F Y₁ n = F Y₂ n}), (Set.univ : Set (ℕ → α))
  ⊆ ⋃ σ ∈ t, {X : (ℕ → α) | σ ≼ X}
:= by
    exact my_isCompact_iff_finite_subcover₀ F n isCompact_univ (λ σ ↦ {X : (ℕ → α) | σ ≼ X})


lemma cones_are_open  {α : Type} [TopologicalSpace α] [DiscreteTopology α]
  (σ : @condition α) : IsOpen {X : ℕ → α | σ ≼ X} := by
      apply isOpen_pi_iff.mpr
      intro Y hY
      exists σ.1
      exists (λ i : ℕ ↦ by
        by_cases H : i ∈ σ.1.1
        exact σ.2 ⟨i,H⟩
        exact Set.univ
      )
      constructor
      intro i hi
      constructor
      . simp
      simp
      rw [dif_pos hi]
      simp at hY
      unfold extendedByℕ at hY
      exact hY i hi

      simp
      intro Z hZ
      simp at hZ
      intro i hi
      let Q := hZ i hi
      rw [dif_pos hi] at Q
      exact Q

/-- This is the too-obvious version of the use principle, before using compactness
as in isCompact_iff_finite_subcover
. -/
theorem prep_for_compactness_and_use₀ {α : Type} [TopologicalSpace α] [DiscreteTopology α] (F : (ℕ → α) → (ℕ → α))
  (hF : Continuous F) (n:ℕ) (X : (ℕ → α)) :
  ∃ σ : condition, σ ≼ X ∧ ∀ Y : (ℕ → α), σ ≼ Y → F Y n = F X n := by
    obtain ⟨I,hI⟩ := isOpen_pi_iff.mp (open_value n (F X n) hF) X rfl
    obtain ⟨U,hU⟩ := hI
    let τ : condition := ⟨I,λ n ↦ U n.1⟩
    exists τ
    constructor
    unfold extendedByℕ
    intro i hi
    exact (hU.1 i hi).2
    intro Y hY

    apply hU.2
    exact hY

/-- This version makes it clear that the set of X for which σ exists is open: -/
theorem prep_for_compactness_and_use₁ {α : Type} [TopologicalSpace α] [DiscreteTopology α] (F : (ℕ → α) → (ℕ → α))
  (hF : Continuous F) (n:ℕ) (X : (ℕ → α)) :
  ∃ σ : condition, (∀ Y₁ Y₂ : (ℕ → α), σ ≼ Y₁ → σ ≼ Y₂ → F Y₁ n = F Y₂ n) ∧ σ ≼ X := by
  obtain ⟨σ,hσ⟩ := prep_for_compactness_and_use₀ F hF n X
  exists σ
  constructor
  intro Y₁ Y₂ hY₁ hY₂
  let Q₁ := hσ.2 Y₁ hY₁
  let Q₂ := hσ.2 Y₂ hY₂
  exact Eq.trans Q₁ Q₂.symm
  tauto


-- def get_bar (F : cantor → cantor) (hF : Continuous F) (n:ℕ)
--   :
--   Finset condition
--   :=
--   -- would require a functional version of my_isCompact_iff_finite_subcover₁
--   sorry

/-- Apr 14, 2024-/
theorem bounded_use_principle₀ {α : Type} [TopologicalSpace α] [DiscreteTopology α]
[CompactSpace (ℕ → α)] (F : (ℕ → α) → (ℕ → α)) (hF : Continuous F) (n:ℕ):
∃ (t : Finset { τ : condition // ∀ Y₁ Y₂ : (ℕ → α), τ ≼ Y₁ → τ ≼ Y₂ → F Y₁ n = F Y₂ n}), (Set.univ : Set (ℕ → α))
  ⊆ ⋃ σ ∈ t, {X : (ℕ → α) | σ ≼ X}
:= by
    have : (Set.univ : Set (ℕ → α)) ⊆
      ⋃ (σ : { τ : condition // ∀ Y₁ Y₂ : (ℕ → α), τ ≼ Y₁ → τ ≼ Y₂ → F Y₁ n = F Y₂ n}), {Y : (ℕ → α) | σ ≼ Y} := by
        intro Y
        intro
        simp
        exact prep_for_compactness_and_use₁ F hF n Y
    exact my_isCompact_iff_finite_subcover₁ _ _ (λ σ ↦ cones_are_open σ.1) this

def condition_of_fin {α : Type}  (σ : (Σ n, Fin n → α)) : @condition α
  := ⟨(Finset.range σ.1), λ i ↦ {σ.2 ⟨i.1, List.mem_range.mp i.2⟩}⟩

lemma sea_extends {α : Type} (σ : Σ n, Fin n → α) (X : ℕ → α) : (@condition_of_fin α σ) ≼ (σ ↘ X)
  := by
    intro j hj
    unfold condition_of_fin searrow
    simp
    rw [dif_pos _]


instance myt {α : Type} : Trans (@extendedBy α) extendedByℕ extendedByℕ := {
  trans := λ h₀ h₁ ↦ extendedBy_transitiveℕ h₀ h₁
}

/-- Completed Apr 15, 2024.-/
theorem condition_of_max {α : Type} (τ : condition) (X : (ℕ → α))
(σ : Σ k, Fin k → α)
(hN : Finset.Nonempty τ.fst)
(h : Finset.max' τ.1 hN < σ.1)
(hτ : τ ≼ (σ ↘ X)) : τ ≼ condition_of_fin σ := by

  unfold extendedByℕ at hτ
  unfold extendedBy
  have : τ.fst ⊆ (condition_of_fin σ).fst := by
    intro i hi
    unfold condition_of_fin
    simp
    suffices i ≤ Finset.max' τ.fst hN by
      calc
      _ ≤ Finset.max' τ.1 hN := this
      _ < _ := h
    apply Finset.le_max'
    exact hi
  exists this
  intro i hi
  intro b hb
  let Q := hτ i hi
  simp at Q
  unfold condition_of_fin at hb
  simp at hb
  subst hb
  unfold searrow at Q
  have : i < σ.1 := by
    suffices i ≤ Finset.max' τ.fst hN by
      calc
      _ ≤ Finset.max' τ.1 hN := this
      _ < _ := h
    apply Finset.le_max'
    exact hi
  rw [dif_pos this] at Q
  exact Q


theorem emp_extendedBy {α : Type} {σ : @condition α} (he : σ.1 = ∅) (X : (ℕ → α)) :
σ ≼ X := by
  unfold extendedByℕ
  intro i hi
  rw [he] at hi
  contrapose hi
  simp


-- def use_function (F : (ℕ → α) → (ℕ → α)) (hF : Continuous F) (n:ℕ) : ℕ := by
--   -- this requires a functional version of bounded_use_principle₀
--   sorry

/-- Main achievement of Apr 15, 2024. -/
theorem bounded_use_principle₁ {α : Type} [TopologicalSpace α] [DiscreteTopology α]
[CompactSpace (ℕ → α)] (F : (ℕ → α) → (ℕ → α)) (hF : Continuous F) (n:ℕ):
∃ u : ℕ, ∀ σ : Σ k, Fin k → α, σ.1 = u →
  ∀ X Y : ℕ → α, F (σ ↘ X) n = F (σ ↘ Y) n := by

    obtain : Trans (@extendedBy α) extendedByℕ extendedByℕ := {
      trans := λ h₀ h₁ ↦ extendedBy_transitiveℕ h₀ h₁
    }


    obtain ⟨t,ht⟩ := bounded_use_principle₀ F hF n
    let I := Finset.biUnion t (λ σ ↦ σ.1.1)
    by_cases hN : Finset.Nonempty I
    . let u := Finset.max' I hN
      exists u.succ
      intro σ hσu X Y
      suffices ∃ τ ∈ t, τ ≼ (σ ↘ X) ∧ τ ≼ (σ ↘ Y) by
        obtain ⟨τ,hτ⟩ := this
        exact τ.2 (σ ↘ X) (σ ↘ Y) hτ.2.1 hτ.2.2
      have : (σ ↘ X) ∈ Set.univ := trivial
      let Q := ht this
      simp at Q
      obtain ⟨τ₀,hτ₀⟩ := Q
      let hτt := hτ₀.1.2
      let ⟨τ₁,hτ₁⟩ := hτ₀

      exists ⟨τ₀,τ₁.1⟩
      constructor
      . exact hτt
      . constructor
        . exact hτ₁

        . simp
          by_cases H : Finset.Nonempty τ₀.fst
          . -- yes
            have : Finset.max' τ₀.fst H < σ.fst := by
              rw [hσu]
              suffices Finset.max' τ₀.1 H ≤ u by
                exact Nat.lt_succ.mpr this
              rw [Finset.max'_le_iff]
              intro i hi
              apply Finset.le_max'
              simp
              exists τ₀
            calc
            τ₀ ≼ condition_of_fin σ := condition_of_max τ₀ X σ H this hτ₁
            _  ≼ (σ ↘ Y)            := sea_extends _ _
          . -- no
            simp at H
            exact emp_extendedBy H _
    . -- since the biUnion is empty, the empty condition must force it
      exists 0
      intro σ; intro; intro X Y
      let hX := ht (show X ∈ Set.univ from trivial)
      simp at hX hN
      obtain ⟨σX, hσX⟩ := hX
      let emp_σX := hN σX hσX.1.1 hσX.1.2
      exact hσX.1.1 (σ ↘ X) (σ ↘ Y) (emp_extendedBy emp_σX _) (emp_extendedBy emp_σX _)

/-- We can pack a finite set of consistent conditions into one condition, although it may not be useful.-/
def pack_conditions {α : Type}: Finset (@condition α) → (@condition α) := by
  intro t
  unfold condition
  let I := Finset.biUnion t (λ σ ↦ σ.1)

  exact ⟨I,by
    intro i
    let Q := i.2
    simp at Q
    let ti := Finset.filter (λ σ ↦ i.1 ∈ σ.1) t -- the conditions that mention i
    exact ⋂ (σ ∈ ti), σ.2 ⟨i,by
      rename_i hh
      simp at hh
      exact hh.2
    ⟩
  ⟩


/-- The key part of Lemma 14 in `A tractable case`.
  F(X)(n) has a certain use τ, and for any Y ≽ any ρ ≽ τ, the value of Φ Y n is correct.
  So the statement of Lemma 14 is correct, even if the proof contains a misstatement.
  We don't need Φ continuous here but of course we do need that in Lemma 14.
  -/

theorem lemma_14 {α : Type}
  [TopologicalSpace α] [DiscreteTopology α] {F : (ℕ → α) → (ℕ → α)} (hF : Continuous F)
    {Φ : (ℕ → α) → ℕ → Part α} {σ : condition} (hforce : forcedEqualAbove F Φ σ)
    {X : ℕ → α} (hX : σ ≼ X) (n : ℕ)
    :
    ∃ τ, (∃ Y : ℕ → α, τ ≼ Y ∧ Φ Y n ≠ Part.none) ∧
          ∀ Y : ℕ → α, τ ≼ Y ∧ Φ Y n ≠ Part.none → F X n = Φ Y n := by
                       -- τ₀ ≼ Y is all we need here, where τ₀ is "where F X n converges",
                       -- which is something we can compute from X
                       -- if F has computably bounded use, or Φ is a tt-reduction, or X is generic...
                       -- need SOMETHING like that. If F is computable on the assumption that
                       -- its oracle X is generic, that's not so bad since S&W showed each automorphism
                       -- is determined by what they do on generics! So F still induces a trivial auto
                       -- and we get to cite S&W.

                       -- Also: we don't need E₀-invariance at all because it suffices to prove F
                       -- is decreasing on [σ], since every real is T-equivalent to one i [σ]!
                       -- Oh but we still need to check that if Θ⁻¹ S* Θ is computable on generics
                       -- above [σ] then Θ is compuble (on generics above [σ]) (Lemma 12)
                       -- A problem is that the fcn that is computable-on-generics is *ipso facto*
                       -- not a total continuous fcn, because we don't know how fast Φ will converge.
                       -- So we may have better hopes for: Homeo Aut D_{tt}, with no need for
                       -- generics
  obtain ⟨I,hI⟩ := isOpen_pi_iff.mp (open_value n (F X n) hF) X rfl
  obtain ⟨U,hU⟩ := hI
  let τ₀ : condition := ⟨I,λ n ↦ U n.1⟩
  obtain ⟨ρ,hρ⟩ := hforce n (σ ⊔ τ₀) (common_extension_extends _ _) (by
      exists X
      apply join_extendedBy
      . exact hX
      . intro j hj
        exact (hU.1 j hj).2
  )
  exists ρ
  constructor
  . obtain ⟨Y,hY⟩ := hρ.2.1
    exists Y
    constructor
    . exact hY
    . rw [← hρ.2.2 Y hY]
      simp
  . intro Y hY
    rw [← hρ.2.2 Y hY.1]
    simp
    symm
    apply hU.2
    calc
    τ₀ ≼ (σ ⊔ τ₀) := common_extension_extends' _ _
    _  ≼ ρ        := hρ.1
    _  ≼ Y        := hY.1



/-- Completed Apr 13, 2024, 7am. -/
theorem forcing_total {α : Type} [TopologicalSpace α] [DiscreteTopology α]
  -- [TopologicalSpace (ℕ → Part α)] -- for α  = Bool everything is fine
  (F : (ℕ → α) → (ℕ → α)) (hF : Continuous F)
    (Φ : (ℕ → α) → ℕ → Part α)
    (hΦ : Continuous Φ)
    (σ : condition) (hforce : forcedEqualAbove F Φ σ)
    (n : ℕ) (X : ℕ → α) (hX : σ ≼ X)
    (hXn : Φ X n ≠ Part.none) :
    F X n = Φ X n := by
      obtain ⟨c,hc⟩ := Part.ne_none_iff.mp hXn
      have hoc : IsOpen {A | Φ A n = c} := open_value_part _ _ hΦ
      obtain ⟨Ic,hcI⟩ := isOpen_pi_iff.mp hoc X hc
      obtain ⟨Uc,hUc⟩ := hcI
      let υc : condition := ⟨Ic,λ n ↦ Uc n.1⟩
      have hυc: υc ≼ X := λ j hj ↦ (hUc.1 j hj).2
      let b := F X n
      have hob: IsOpen { A | F A n = b} := open_value _ _ hF
      obtain ⟨Ib,hIb⟩ := isOpen_pi_iff.mp hob X rfl
      obtain ⟨Ub,hUb⟩ := hIb
      let υb : condition := ⟨Ib,λ n ↦ Ub n.1⟩
      have hυb: υb ≼ X := λ j hj ↦ (hUb.1 j hj).2
      let α₀ := υb ⊔ υc
      let α₁ := σ ⊔ α₀
      have : σ ≼ α₁ := common_extension_extends σ α₀
      have h_X: ∃ X : ℕ → α, α₁ ≼ X := by
        exists X
        apply join_extendedBy
        exact hX
        apply join_extendedBy
        exact hυb
        exact hυc
      let ⟨ρ,hρ⟩ := hforce n α₁ this h_X
      obtain ⟨Y,hY⟩ := hρ.2.1
      have hα₀ : α₀ ≼ Y := calc
                    α₀ ≼ α₁ := @common_extension_extends' α _ _
                    _  ≼ ρ := hρ.1
                    _  ≼ Y := hY
      have hΦ: Φ Y n = Part.some c := by
        have hυcY: υc ≼ Y := calc
                   υc ≼ α₀ := common_extension_extends' _ _
                   _  ≼ Y := hα₀
        exact hUc.2 hυcY
      have hF: F Y n = b := by
        have : υb ≼ Y := calc
               υb ≼ α₀ := common_extension_extends _ _
               _  ≼ Y := hα₀
        unfold extendedByℕ at this
        apply hUb.2
        exact this
      calc
        Part.some (F X n) = Part.some (F Y n) := by rw [hF]
        _                 = Φ Y n             := hρ.2.2 Y hY
        _                 = Part.some c       := hΦ
        _                 = Φ X n             := hc.symm
    /-
    Explanation:
    as soon as we are in νc, Φ=c.
    as soon as we are in νb, F=b.
    as soon as we are in σ, forcing happens
    And X is in all.
    Let α = common_extension νb νc σ.
    Then X is in α, so α≠∅, and moreover there's a ρ extending α
    STILL NONEMPTY forcing F=Φ. Then that Y shows b=c
    -/


lemma testing_searrow :
  ((⟨2, λ _ ↦ true⟩ : Σ n, Fin n → Bool) ↘
  (λ n : ℕ ↦ ite (n=0) false true)) = (λ _ ↦ true) := by
  apply funext;intro n;unfold searrow;simp;intro h h₀;subst h₀;linarith

/-- This verifies the first displayed equation in Example 16 in E₀ paper.-/
theorem theta₁₆' (A : ℕ → Bool) (n : ℕ) :
  (Θ₁₆ A) 1 = or (! ( A 4 && A 5)) ( A 6 && A 7) := by
    have hence₁₆ (n:ℕ): (λ A ↦ (starpi n) (Θ₁₆ (Φ₁₆ A)))
                      = λ A ↦ (starpi n.succ) (Θ₁₆ A) := by
      rfl
    have : starpi 0 (Θ₁₆ (Φ₁₆ A))
         = starpi 1 (Θ₁₆ A) := congrArg (λ F ↦ F A) (hence₁₆ 0)
    calc _ = (Θ₁₆ (Φ₁₆ A)) 0                    := congrArg (λ A ↦ A n) this.symm
         _ = (! (Φ₁₆ A 2) || Φ₁₆ A 3)           := rfl
         _ = ((! (A 4 && A 5)) || (A 6 && A 7)) := by unfold Φ₁₆; ring_nf


#check 0

def shift {α : Type}
 (X : ℕ → α) (n:ℕ) := X (n.succ)


def right_shift
 (X : ℕ → Bool) (n:ℕ) := (ite (n=0)) false (X (n.pred))

theorem continuous_shift : Continuous (@shift (Bool)) := by
  unfold shift
  exact Pi.continuous_precomp' fun j ↦ Nat.succ j

theorem continuous_right_shift : Continuous (right_shift) := by
  unfold right_shift
  refine continuous_pi ?h
  intro i
  by_cases h : (i=0)
  . subst h
    simp
    exact continuous_const
  exact {
    isOpen_preimage := by
      intro O hO
      show IsOpen ((fun a ↦ if i = 0 then false else a (Nat.pred i)) ⁻¹' O)
      have : (fun a : ℕ → Bool ↦ if i = 0 then false else a (Nat.pred i))
        = (fun a ↦ a (Nat.pred i)) := by
          apply funext
          intro A
          rw [if_neg h]
      rw [this]
      refine Continuous.isOpen_preimage ?_ O hO
      exact continuous_apply (Nat.pred i)
  }

example {α β γ : Type} [TopologicalSpace α] [TopologicalSpace β]
  [TopologicalSpace γ] {f : α → β} {g : β → γ} (hf : Continuous f)
  (hg : Continuous g) : Continuous (g ∘ f) := by
    exact Continuous.comp hg hf

-- example { α : Type} (f : α → α → α) : α × α → α :=


-- example {α β γ : Type} [TopologicalSpace α] [TopologicalSpace β]
--   [TopologicalSpace γ] {g : α → β → γ} (hg : Continuous g) (e : α × β → α)
--   (f : α × β → β) (he: Continuous e) (hf : Continuous f)
--   : Continuous (λ x ↦ g (e x) (f x)) := by
--   -- have : Continuous (λ x  ↦ g (e x, f x).1 (e x, f x).2 : α × β → γ) := sorry
--   -- apply?
--   have : Continuous fun x y ↦ g (e x) y := sorry
--   sorry

-- example {α β γ : Type} [TopologicalSpace α] [TopologicalSpace β]
--   [TopologicalSpace γ] {g : α → β → γ} (hf : Continuous g)
--   : Continuous (λ x : α × β ↦ g x.1 x.2)
--   := by
--     have c₁: Continuous (λ x : α × β ↦ x.1) := by exact continuous_fst
--     have c₂: Continuous (λ x : α × β ↦ x.2) := by exact continuous_snd

--     sorry

example {α β γ : Type} [TopologicalSpace α] [TopologicalSpace β]
  [TopologicalSpace γ] {f : α × β → γ} (hf : Continuous f)
  : Continuous (λ x : α ↦ λ y : β ↦ f ⟨x,y⟩)
  := by
    refine continuous_pi ?h
    intro y
    refine Continuous.comp' hf ?h.hf
    exact Continuous.Prod.mk_left y


theorem characterize_ville_salo :
  ville_salo = λ A ↦ (λ n ↦ xor (A n) (right_shift A n)) := by
    unfold ville_salo right_shift xor frown
    simp
    apply funext
    intro A
    apply funext
    intro n
    induction n
    . simp
    . simp
      exact Bool.xor_comm (A n_1) (A (Nat.succ n_1))


theorem xor_continuous_ville_salo₀₀ :
      ∀ p q : (ℕ → Bool) → Bool, Continuous p → Continuous q →
      Continuous (λ A ↦ xor (p A) (q A)) := by
      intro p q hp hq
      let Q := @Continuous.comp₂ Bool Bool Bool (ℕ → Bool) _ _ _ _
        (λ pair ↦ xor pair.1 pair.2) (by
          have : Continuous (λ b c : Bool ↦ xor b c) := by exact continuous_bot
          simp at this
          have : (fun x : Bool × Bool => if (fun pair : Bool × Bool => ¬pair.1 = pair.2) x then true else false)
           = (fun pair : Bool × Bool => xor pair.1 pair.2) := by
            apply funext;intro pair;cases pair;cases fst
            repeat (cases snd;repeat simp)
          simp at this
          rw [← this]
          apply continuous_of_discreteTopology
        )
        p hp q hq
      exact Q

theorem xor_continuous_ville_salo₀ (f g : (ℕ → Bool) → (Bool)) (hf : Continuous f)
  (hg : Continuous g) : Continuous (
    λ A ↦ (λ _ ↦ xor (f A) (g A))
    : (ℕ → Bool) → (ℕ → Bool)
  ) := by
    refine continuous_pi ?h
    intro
    exact xor_continuous_ville_salo₀₀ (λ A ↦ f A) (λ A ↦ g A) hf hg

theorem xor_continuous_ville_salo (f g : (ℕ → Bool) → (ℕ → Bool)) (hf : Continuous f)
  (hg : Continuous g) : Continuous (
    λ A ↦ (λ n ↦ xor (f A n) (g A n))
    : (ℕ → Bool) → (ℕ → Bool)
  ) := by
    refine continuous_pi ?h
    intro i
    have h_: Continuous fun a : ℕ → Bool ↦ a i := continuous_apply i
    have h_f: Continuous fun a ↦ f a i := Continuous.comp h_ hf
    have h_g: Continuous fun a ↦ g a i := Continuous.comp h_ hg
    exact xor_continuous_ville_salo₀₀ (λ A ↦ f A i) (λ A ↦ g A i) h_f h_g

/-- This follows from general theory as in https://math.stackexchange.com/questions/3042668/continuous-bijection-between-compact-and-hausdorff-spaces-is-a-homeomorphism
  but we can try a direct proof-/
theorem continuous_iteratedXor : Continuous iteratedXor := by
  refine continuous_pi ?h
  intro i
  induction i

  unfold iteratedXor
  exact continuous_apply 0
  unfold iteratedXor

  let Q := xor_continuous_ville_salo₀₀
    (λ A ↦ A n.succ) (λ A ↦ iteratedXor A n)
    (continuous_apply (Nat.succ n)) n_ih
  simp at Q
  exact Q

theorem continuous_ville_salo :
  Continuous ville_salo := by
    rw [characterize_ville_salo]
    apply xor_continuous_ville_salo
    exact Pi.continuous_precomp' fun j => j
    exact continuous_right_shift

def ville_salo_homeo : Homeomorph (ℕ → Bool) (ℕ → Bool) := {
  toFun := ville_salo
  invFun := iteratedXor
  continuous_toFun := continuous_ville_salo
  right_inv := by
    unfold Function.RightInverse
    intro A
    exact congrFun ville_salo_iteratedXor_id A
  left_inv := by
      intro A
      suffices ville_salo (iteratedXor (ville_salo A)) = ville_salo A by
        exact ville_salo_injective this
      let Q := congrFun ville_salo_iteratedXor_id (ville_salo A)
      simp at Q
      exact Q
  continuous_invFun :=  continuous_iteratedXor
}

theorem ville_salo_false : ville_salo (λ _ ↦ false) = λ _ ↦ false := by
  apply funext
  intro n
  unfold ville_salo frown
  simp

theorem ville_salo_false' : iteratedXor (λ _ ↦ false) = λ _ ↦ false := by
  suffices ville_salo (iteratedXor (λ _ ↦ false)) = ville_salo (λ _ ↦ false) by
    exact ville_salo_injective this
  let Q := congrFun ville_salo_iteratedXor_id (λ _ ↦ false)
  simp at Q
  rw [Q]
  exact ville_salo_false.symm

theorem ville_salo_1false : ville_salo (λ _ ↦ true) =  (⟨1,λ _ ↦ true⟩ ⌢ (λ _ ↦ false))
 := by
  apply funext
  intro n
  unfold ville_salo frown
  simp

theorem ville_salo_1false' : iteratedXor (⟨1,λ _ ↦ true⟩ ⌢ (λ _ ↦ false)) = (λ _ ↦ true) := by
  suffices ville_salo (iteratedXor (⟨1,λ _ ↦ true⟩ ⌢ (λ _ ↦ false))) = ville_salo (λ _ ↦ true) by
    exact ville_salo_injective this
  let Q := congrFun ville_salo_iteratedXor_id (⟨1,λ _ ↦ true⟩ ⌢ (λ _ ↦ false))
  simp at Q
  rw [Q]
  exact ville_salo_1false.symm

theorem not_iteratedXor_E₉ : ¬ E₀invariant iteratedXor := by
  unfold E₀invariant
  intro hc
  have : E₀ (λ _ ↦ false) (⟨1,λ _ ↦ true⟩ ⌢ (λ _ ↦ false)) := by
    unfold frown E₀
    exists 1
    intro n
    simp
    intro h
    have : ¬ n = 0 := by exact Nat.pos_iff_ne_zero.mp h
    rw [if_neg this]
  have : E₀ (iteratedXor (λ _ ↦ false)) (iteratedXor (⟨1,λ _ ↦ true⟩ ⌢ (λ _ ↦ false))) := by
    let Q := hc _ _ this
    exact Q
  rw [ville_salo_false'] at this
  rw [ville_salo_1false'] at this
  obtain ⟨a,ha⟩ := this
  let Q := ha a (le_refl _)
  simp at Q


theorem ville_salo_E₉ : E₀invariant ville_salo := by
  intro A B h
  unfold E₀ at *
  obtain ⟨a,ha⟩ := h
  exists a.succ
  intro n hn
  unfold ville_salo frown
  simp
  cases n
  . simp
    simp at hn
  . simp
    have : a ≤ n_1 := Nat.lt_succ.mp hn
    let Q := ha n_1 this
    let R := ha n_1.succ (Nat.le_step this)
    rw [Q,R]


example : @shift Bool = starS := rfl

def app{α : Type}
 (f : α → α) (X : ℕ → α) (n:ℕ) := f (X n)

-- def comp (X : ℕ → α) (n:ℕ) := ¬ (X n)
/-- Functions that commute with shift include any (app f) and of course shift itself. Moreover, they are closed under ∘.
But they are determined by their value at 0, λ A ↦ F A 0.-/




def shiftcommuter (G : (ℕ → Bool) → Bool) (A : ℕ → Bool) (n:ℕ) : Bool := match n with
| 0 => G A
| Nat.succ n => shiftcommuter G (shift A) n

def commuter {α : Type} (Φ : (ℕ → α) → (ℕ → α)) (G : (ℕ → α) → α) (A : ℕ → α) (n:ℕ) : α
  := match n with
| 0 => G A
| Nat.succ n => commuter Φ G (Φ A) n


theorem commuter_basic {α : Type} (Φ : (ℕ → α) → (ℕ → α))
  (G : (ℕ → α) → α) (A : ℕ → α) (n:ℕ) : commuter Φ G A n.succ
  = commuter Φ G (Φ A) n := rfl


theorem shiftcommuter_is_commuter_shift : shiftcommuter = commuter shift := by rfl

theorem shiftcommuter_commutes_with_shift (G : (ℕ → Bool) → Bool) :
(commuter shift G) ∘ shift = shift ∘ (commuter shift) G := by
  apply funext
  intro X
  apply funext
  intro n
  unfold shift
  simp
  unfold commuter
  match n with
  |0 =>
    simp
    unfold commuter
    simp
  |Nat.succ n =>
    simp
    rfl

theorem app_commute{α : Type}
 (f : α → α) : (app f) ∘ shift = shift ∘ (app f) := by
  apply funext
  intro X
  apply funext
  intro n
  -- unfold Function.comp
  unfold shift app
  simp



-- then generalize from shift to anything. Apr 16, 2024
theorem only_commuter_commutes {α : Type} (F Φ : (ℕ → α) → ℕ → α)
  (hF₂ : F ∘ Φ = shift ∘ F)
  : F = commuter Φ (λ A ↦ F A 0) := by
    apply funext
    suffices ∀ n : ℕ, ∀ A : ℕ → α, F A n = commuter Φ (λ A ↦ F A 0) A n by
      intro A;apply funext;intro n;exact this _ _
    intro n
    induction n
    . intro A
      rfl
    intro A
    let Q := n_ih (shift A)
    simp at Q
    have h: (F ∘ shift) A n_1 = F (shift (A)) n_1 := rfl
    rw [← h] at Q
    rw [Q] at h
    have : F A n_1.succ = (shift ∘ F) A n_1 := rfl
    rw [this]
    rw [← hF₂]
    simp
    symm
    let R := commuter_basic Φ (λ A ↦ F A 0) A n_1
    rw [R]
    let S := n_ih (Φ A)
    tauto

/-
The shift moves us away from [σ]... means we should
bring back E₀-invariance.
Actually the original paper cleverly avoids this problem by using Θ⁻¹,
so that
  - the computability claim using nonmeagerness and
  - the computability claim using recursion
are kept separate.
So... the original paper claim with `T` replaced by `tt` holds.
-/

open Function

/--
  This suggests that if Θ⁻¹ shift Θ is computable then so is Θ
  (Lemma 12 of `A tractable case`).
  We only need Θ surjective for the statement to hold, but
  surjInv uses Classical.choose .
-/
theorem only_commuter_commutes_inv {α : Type}
  (F : (ℕ → α) → ℕ → α) (hF : Function.Surjective F) :
  F = commuter
    ((surjInv hF) ∘ shift ∘ F) (λ A ↦ F (A) 0)
  := by
  suffices F ∘ ((surjInv hF) ∘ shift ∘ F) = shift ∘ F by
    exact only_commuter_commutes F ((surjInv hF) ∘ shift ∘ F) this
  have : F ∘ (surjInv hF) = id := by
    apply funext; apply surjInv_eq
  show (F ∘ surjInv hF) ∘ shift ∘ F = shift ∘ F
  rw [this];simp





-- Can we prove that commuter Φ G A n = G (Φ^n A)?
-- There is something called iterate: f^[n]

def powers {α : Type} (Φ : (α) → (α)) (n : ℕ) :
(α) → (α) := by
  intro A
  match n with
  |0 => exact A
  |Nat.succ n => exact Φ (powers Φ n A)

instance {α : Type} : Pow (α → α) ℕ := {
  pow := powers
}


-- example {α β : Type} (x y : α) (h : x = y) (f : α → β):
--   f x = f y := by exact congrArg f h

theorem powers_basic {α : Type} (Φ : (ℕ → α) → ℕ → α) (n_1 : ℕ):
(λ A ↦ (Φ ^ n_1) (Φ A)) = λ A ↦ Φ  ((Φ ^ n_1) A) := by
  induction n_1
  . rfl
  . exact funext (λ A ↦ congrArg Φ (congrFun n_ih A))


/-
  Notice that no continuity assumption is here.
The argument goes:
A = S^* B ≤ₜₜ B
So Θ A ≤ₜₜ Θ B,
Θ A = Φ Θ B,
Θ S^* B = Φ Θ B,
which makes Θ a "discrete orbit", hence computable, on [σ].
Thus no function (homeomorphism or not, continuity or not)
can induce a nontrivial Dₜₜ automorphism.
Perhaps Slaman-Woodin reasoning shows that any auto
would have to be induced by a function.

Apr 19
Well, we need {A | F(A)(0)=true} to be computable, preferably clopen.
Suppose π is an any automorphism of Dₜₜ. Using Axiom of Choice let
p : Dₜₜ → cantor pick an element A of each degree such that A(0)=true.
Let F(X) = p π [X]ₜₜ. Then F is computable by the argument above and
{A | F(A)(0)=true} = cantor.

`A contradiction in mathematics`:
Using Axiom of Choice let
`p : Dₜₜ → cantor` map each tt-degree to one of its elements, with `p(d)(0)=true ∀ d`, and let
`Θ : cantor → cantor`, `Θ X = p [X]`. So `(Θ X)(0)=true`.
Then `Θ` preserves tt-reducibility, if if `A = shift B`, `Θ A ≤ₜₜ Θ B`, so
`∀ B ∃ e,  Θ A = Φₑ (Θ B)`. Now `Θ` is not constructive at all, but nevertheless we can apply
Baire category theory to the sets

`Sₑ = {B | Θ (shift B) = Φₑ (Θ B)}`

and conclude that they cannot all be nowhere dense.
So one of them is somewhere dense, i.e., `∃ σ Φ, ∀ B ∈ [σ], Θ (shift B) = Φ (Θ B)`.

Then we argue that `Θ` is computable, which makes tt-reducibility `Π⁰₁`:
`X ≃ₜₜ Y ↔ ∀ n, (Θ X) n = (Θ Y) n`. But it is known not to be.

Perhaps the problem is that Baire category theorem only applies to "nice" sets?
If so, we could rule out non-nice functions for `Aut(Dₜₜ)`.

Perhaps the problem is that `∀ B ∈ [σ], Θ (shift B) = Φ (Θ B)` does not allow us to compute
`Θ` unless `Θ` is simple on all of `[0,|σ|)`? And we can't assume that because `σ` depends on `Θ`.
But if `Θ` is continuous it's not a problem.




If Θ is measure-preserving (as permutations of ℕ are)
and A is random then it stands to reason that Φ be measure-preserving,
as a kind of inverse ergodic property:
If an orbit {T^n x}_{n ∈ ℕ} is ergodic then T must be measure-preserving?

THE CONVERSE OF THE INDIVIDUAL
ERGODIC THEOREM
FRED B. WRIGHT

is every permutation of ℕ basically a "commuter"?
is every function a commuter?
∀ F, ∃ G Φ, ∀ n, F A n = G ((Φ ^ n) A) ?

Is the identity function F A n = A n?
  Yes, let Φ be shift and G(X)=X(0).
Is a constant function (F(A)(n)=true ∀ A) a commuter?
  Yes, let G(X)=true ∀ X
Is a constant function (F(A)(n)=B(n) ∀ A) a commuter?
  Probably not, but how to prove?

  -/




/-- Apr 16, 2024-/
theorem characterize_commuter {α : Type} (Φ : (ℕ → α) → (ℕ → α)) (G : (ℕ → α) → α)
 (n : ℕ) : -- it's not so much a "commuter" as a "discrete orbit", "dynamical system/iterator/ergodic..."
∀ (A : ℕ → α), commuter Φ G A n = G ((Φ ^ n) A) := by
  induction n
  . intro A
    rfl
  . intro A
    have h₀ : (Φ ^ (n_1.succ)) A = Φ ((Φ ^ n_1) A) := rfl
    rw [h₀,commuter_basic,n_ih (Φ A)]
    congr
    exact congrFun (powers_basic Φ n_1) A

theorem characterize_commuter' {α : Type}:
  @commuter α = λ Φ G A n  ↦ G ((Φ ^ n) A) := by
  repeat (apply funext;intro)
  apply characterize_commuter

theorem commuter_commutes {α : Type} (Φ : (ℕ → α) → (ℕ → α)) (G : (ℕ → α) → α):
(commuter Φ G) ∘ Φ = shift ∘ (commuter Φ G) := by
  let Q := @characterize_commuter' α
  rw [Q]
  simp
  unfold shift
  apply funext
  intro A
  simp
  apply funext
  intro n
  have h₁: (Φ ^ (n.succ))  = Φ ∘ (Φ ^ n) := rfl

  have : (Φ ^ n.succ) A = (Φ ^ n) (Φ A) := by
    rw [h₁]
    simp
    let Q := powers_basic Φ n
    simp at Q
    have : (fun A ↦ (Φ ^ n) (Φ A)) A = (fun A ↦ Φ ((Φ ^ n) A)) A := by
      rw [Q]
    simp at this
    rw [← this]
  rw [this]



noncomputable def choice_function {α : Type} (P : α → α → Prop) (h: ∀ x, ∃ y, P x y)
: (x:α) → {y : α // P x y} := by
  intro x
  have : Nonempty {y : α // P x y} := by
    exact nonempty_subtype.mpr (h x)
  exact Classical.choice this

noncomputable def pure_choice_function
  {α : Type} (P : α → α → Prop) (h: ∀ x, ∃ y, P x y)
  : α → α := λ x ↦ choice_function P h x


/-- To be a commuter it is enough that
  range (shift ∘ F) ⊆ range (F).
  This would cover the constant example too,
  and is an ↔ by `only_commuter_commutes`.
  It shows that some F such as "constant 1_{0}(n)"
  are not commuters.
-/

lemma range_inclusion {α : Type} (F G : (ℕ → α) → (ℕ → α)):
  (∀ A, ∃ B, F B = G A) ↔
  Set.range G ⊆ Set.range F
  := by
  constructor
  intro hs C hC
  simp
  simp at hC
  obtain ⟨A,hA⟩ := hC
  let Q := hs A
  rw [hA] at Q
  exact Q

  intro hs A
  have : G A ∈ range G := by simp
  let Q := hs this
  simp at Q
  exact Q


theorem commuter_of_surjective' {α : Type} (F : (ℕ → α) → (ℕ → α))
(hs : ∀ A, ∃ B, shift (F A) = F B)
-- (shift ∘ F) '' univ ⊆ F '' univ
-- Set.range (shift ∘ F) ⊆ Set.range F
:
∃ G Φ , F = commuter Φ G := by

  exists (λ A ↦ F A 0)
  have : ∃ Φ, F ∘ Φ = shift ∘ F := by
    let φ := choice_function (λ A B ↦ shift (F A) = F B) hs
    exists (λ A ↦ (φ A).1)
    apply funext
    intro A
    let Q := (φ A).2
    simp
    simp at Q
    symm
    exact Q
  obtain ⟨Φ,hF⟩ := this
  exists Φ
  let Q := only_commuter_commutes F Φ
  tauto

theorem commuter_of_surjective'' {α : Type} (F : (ℕ → α) → (ℕ → α))
  (hs₀ : Set.range (shift ∘ F) ⊆ Set.range F)
  :
  ∃ G Φ , F = commuter Φ G := by
    let Q := (range_inclusion F (shift ∘ F)).mpr hs₀
    have hs : ∀ A, ∃ B, shift (F A) = F B := by
      intro A
      let R := Q A
      simp at R
      tauto
    exact commuter_of_surjective' F hs

/-- Apr 18, 2024.-/
theorem commuter_iff_surjective {α : Type} (F : (ℕ → α) → (ℕ → α)):
  Set.range (shift ∘ F) ⊆ Set.range F ↔
  ∃ G Φ , F = commuter Φ G := by
    constructor
    intro hs₀
    exact commuter_of_surjective'' F hs₀
    intro hcommuter
    obtain ⟨G,hG⟩ := hcommuter
    obtain ⟨Φ,hΦ⟩ := hG
    subst hΦ

    let Q := commuter_commutes Φ G
    rw [← Q]

    intro A hA
    simp at hA
    simp
    obtain ⟨B,hB⟩ := hA
    exists Φ B

theorem why_the_commuter_characterization_is_not_so_surprising {α : Type} (k : ℕ):
  ∀ (A : ℕ → α), A k = (((@shift α) ^ k) A) 0
  := by
    unfold shift
    induction k
    . simp
      intro A
      rfl
    . intro A
      let Φ := (λ B : ℕ → α ↦ shift B)
      have h₁: (Φ ^ (n.succ))  = Φ ∘ (Φ ^ n) := rfl
      show A (Nat.succ n) = (Φ ^ Nat.succ n) A 0
      rw [h₁]
      have nih:  (Φ A) n = (Φ ^ n) (Φ A) 0 := n_ih (Φ A)
      let Q := powers_basic Φ n
      have : ((Φ ^ n) (Φ A)) = Φ ((Φ ^ n) A) := by
          apply funext
          intro l
          show (fun A ↦ (Φ ^ n) (Φ A)) A l = (fun A ↦ Φ ((Φ ^ n) A))  A l
          rw [Q]
      show  A (Nat.succ n) = (Φ  ((Φ ^ n) A)) 0
      rw [← this]
      rw [← nih]
      rfl

/-- Apr 18, 2024.-/
theorem not_all_commuter : ∃ F, ¬ ∃ G Φ, F = @commuter Bool Φ G := by
  exists (λ _ n ↦ (n=0))
  intro hc
  let Q := (commuter_iff_surjective (λ _ n ↦ decide (n=0))).mpr hc
  simp at Q
  let R := congrFun Q 0
  unfold shift at R
  simp at R

theorem commuter_of_surjective (F : (ℕ → Bool) → (ℕ → Bool))
(hs : Function.Surjective F)
:
∃ (G : (ℕ → Bool) → Bool) (Φ : (ℕ → Bool) → (ℕ → Bool)) ,
F = commuter Φ G := by
  exists (λ A ↦ F A 0)
  have : ∃ Φ, F ∘ Φ = shift ∘ F := by
    exists (Function.invFun F) ∘ shift ∘ F
    have hs': F ∘ Function.invFun F = id := by
      suffices Function.LeftInverse F (Function.invFun F) by
        apply funext;exact this
      exact Function.rightInverse_invFun hs
    apply funext
    intro A
    have : F ∘ Function.invFun F ∘ shift ∘ F
     = (F ∘ Function.invFun F) ∘ shift ∘ F := by exact rfl
    rw [this,hs']
    simp
  obtain ⟨Φ,hΦ⟩ := this
  let Q := only_commuter_commutes F Φ hΦ
  exists Φ

/-- A non-surjective commuter. `characterize_commuter` is useful here.-/
theorem commuter_of_constant (b: Bool) :
∃ (G : (ℕ → Bool) → Bool) (Φ : (ℕ → Bool) → (ℕ → Bool)) ,
  commuter Φ G = (λ A _ ↦ b) := by
  exists (λ _ ↦ b)
  exists (λ _ _ ↦ b)
  apply funext
  intro A
  apply funext
  intro n
  exact characterize_commuter (fun _ _ ↦ b) (fun _ ↦ b) n A


theorem only_shiftcommuter_commutes_with_shift (F : (ℕ → Bool) → ℕ → Bool)
  (hF : F ∘ shift = shift ∘ F) : F = commuter shift (λ A ↦ F A 0)
    := only_commuter_commutes _ _ hF


/-- Slightly closer to the real Lemma 14 than `lemma_14`: -/
theorem lemma_14' {α : Type} [TopologicalSpace α] [DiscreteTopology α] {F : (ℕ → α) → (ℕ → α)} (hF : Continuous F)
    {Φ : (ℕ → α) → ℕ → Part α} {σ : Σ n, Fin n → α}
    (hforce : forcedEqualAbove F Φ (condition_of_fin σ))
    (X : ℕ → α)  (n : ℕ)
    :
    ∃ τ, (∃ Y : ℕ → α, τ ≼ Y ∧ Φ Y n ≠ Part.none) ∧
          ∀ Y : ℕ → α, τ ≼ Y ∧ Φ Y n ≠ Part.none → F (σ ↘ X) n = Φ Y n := by
  have hX : condition_of_fin σ ≼ (σ ↘ X) := sea_extends _ _
  obtain ⟨τ,hτ⟩ := lemma_14 hF hforce hX n
  exists τ
/-- if now F is uniformly E₀-invariant then we can assert that ∀ n ≥ b, F X n = Φ Y n,
for a yet slightly closer approximation to Lemma 14.
Would something similar hold for E₁ in place of E₀?
 -/
theorem lemma_14'' {α : Type} [TopologicalSpace α] [DiscreteTopology α] {F : (ℕ → α) → (ℕ → α)} (hF : Continuous F)
    (hui: uniformlyE₀invariant F)
    {Φ : (ℕ → α) → ℕ → Part α} {σ : Σ n, Fin n → α}
    (hforce : forcedEqualAbove F Φ (condition_of_fin σ))
    {X : ℕ → α}
    :
    ∃ b, ∀ n, n ≥ b → -- make it all τ?
    ∃ τ, (∃ Y : ℕ → α, τ ≼ Y ∧ Φ Y n ≠ Part.none) ∧
          ∀ Y : ℕ → α, τ ≼ Y ∧ Φ Y n ≠ Part.none → F X n = Φ Y n := by
  unfold uniformlyE₀invariant at hui
  obtain ⟨b,hb⟩ := hui σ.1
  exists b
  intro n hnb
  obtain ⟨τ,hτ⟩ := lemma_14' hF hforce X n
  obtain ⟨Y,hY⟩ := hτ.1
  exists τ
  constructor
  . exists Y
  . intro Y h_Y
    let R := hτ.2 Y h_Y
    have : F (σ ↘ X) n = F X n := by
      exact hb (σ ↘ X) X (by
        intro k hk
        unfold searrow
        rw [dif_neg (Nat.not_lt.mpr hk)]
      ) n hnb
    rw [this] at R
    exact R


def all_extensions_agree (F : (ℕ → Bool) → (ℕ → Bool)) (σ : Σ n : ℕ, Fin n → Bool)
  (n:ℕ) (b : Bool) -- is F σ n = b ?
  : Prop
  := ∀ X : ℕ → Bool, (condition_of_fin σ) ≼ X → F X n = b

noncomputable def stringFcn (F : (ℕ → Bool) → (ℕ → Bool)) (σ : Σ n : ℕ, Fin n → Bool)
  (n:ℕ) : Part Bool := ite
    (all_extensions_agree F σ n true)   true ( ite
    (all_extensions_agree F σ n false) false
    Part.none
  )
-- can make this take a value in Σ n : ℕ, Fin n → Bool as well


theorem star_invariant {α:Type} : uniformlyE₀invariant (@starS α) := by {
  unfold uniformlyE₀invariant
  intro a
  exists a
  intro A B hAB n hn
  have han : a ≤ n.succ := Nat.le_step hn
  exact hAB n.succ han
}

/-      T O P O L O G Y     -/



def continuousIdentity : ContinuousMap (ℕ → Bool) (ℕ → Bool) := {
  toFun := λ x ↦ x
  continuous_toFun := {
    isOpen_preimage := λ S hoS ↦ by {
      exact hoS
    }
  }
}

def homeomorphicIdentity : Homeomorph (ℕ → Bool) (ℕ → Bool) := {
  toFun := λ x ↦ x
  continuous_toFun := {
    isOpen_preimage := λ S hoS ↦ by {
      exact hoS
    }
  }
  -- continuous_invFun := sorry -- not required since invFun = toFun ?
  invFun := λ x ↦ x
  left_inv := by {intro _;simp}
  right_inv := by {intro _;simp}
}



def complement : (ℕ → Bool) → (ℕ → Bool) := λ x ↦ (λ n ↦ ! (x n) )




-- def cpl : Bool → Bool := λ b ↦ ! b
-- example : Continuous cpl := continuous_bot



theorem continuous_bool_func (cp : Bool → Bool ) : Continuous cp := continuous_bot


theorem continuous_apply_bool_func (cp : Bool → Bool):
  Continuous (λ x : ℕ → Bool ↦ (λ n ↦ cp (x n) ))
  :=
  continuous_pi (λ i ↦  Continuous.comp'
  (continuous_bool_func _)
  (continuous_apply i)
 )

-- Check that the topology on Bool is the discrete one:
example : IsOpen ({true} : Set Bool) := trivial


theorem continuous_const_cantor (y : ℕ → Bool) : Continuous (λ _ : ℕ → Bool ↦ y)
  := continuous_const

example : Continuous (λ x : ℕ → Bool ↦ x) := Pi.continuous_precomp' fun j ↦ j

example (f g : (ℕ → Bool) → (ℕ → Bool)) (hf: Continuous f) (hg: Continuous g) :
  Continuous (λ x ↦ f (g x)) := Continuous.comp' hf hg

example : Continuous (λ x : ℕ → Bool ↦ λ n : ℕ ↦ ite (n=0) true (x n)) := by {
  refine Pi.continuous_postcomp' ?hg
  intro i
  exact continuous_bot
}


def join : (ℕ → Bool) → (ℕ → Bool) → (ℕ → Bool) := λ X Y n ↦ ite (Even n) (X n) (Y n)

infix:50 " ⊕ " => join

-- The operator ⊕ preserves continuity:
theorem join_continuous (F G : (ℕ → Bool) → (ℕ → Bool)) (hF : Continuous F) (hG: Continuous G) :
  Continuous (λ x ↦ (F x) ⊕ (G x)) := by {
  apply continuous_pi
  intro i
  have h2F : Continuous (fun X  ↦ F X i) :=
    Continuous.comp' (continuous_apply i) hF
  have h2G : Continuous (fun X  ↦ G X i) :=
    Continuous.comp' (continuous_apply i) hG
  by_cases h : (Even i)
  have h1 : (fun X ↦ ((F X) ⊕ (G X)) i) =
            (fun X ↦   F X           i) := funext (λ X ↦ if_pos h)
  rw [h1]
  tauto

  have h1 : (fun X ↦ ((F X) ⊕ (G X)) i) =
            (fun X ↦           G X   i) := funext (λ X ↦ if_neg h)
  rw [h1]
  tauto

}


-- The function "complement" is continuous:
theorem cont_compl : Continuous complement := by {
  unfold complement
  apply continuous_pi
  intro i
  exact Continuous.comp' (continuous_bool_func not) (continuous_apply i)
}

def homeomorphicComplement : Homeomorph (ℕ → Bool) (ℕ → Bool) := {
  toFun             := complement
  continuous_toFun  := cont_compl
  invFun            := complement
  left_inv          := by intro x;unfold complement;simp
  right_inv         := by intro x;unfold complement;simp
}

/-- Trivially, permutations of ℕ are homeomorphisms of ℕ.-/
theorem perm_homeo_ℕ (f : ℕ → ℕ) (hf : Function.Bijective f) : Homeomorph ℕ ℕ := {
  toFun     := f
  invFun    := Function.invFun f
  left_inv  := Function.leftInverse_invFun hf.1
  right_inv := Function.rightInverse_invFun hf.2
  continuous_toFun := continuous_bot
  continuous_invFun := continuous_bot
}
