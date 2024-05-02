import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector.Basic
import MyProject.MonoPred
import MyProject.BacktrackingVerification


import Mathlib.Computability.NFA
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Std.Data.Nat.Lemmas
import Mathlib.Data.Matrix.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Digits


set_option tactic.hygienic false
set_option maxHeartbeats 3000000

/- We formalize the non-monotonicity of the objective function in the hydrophobic-polar protein folding model,
refuting an unpublished conjecture of Stecher. -/

-- Encoding the allowed moves for the rectangular lattice structure on ℤ × ℤ using Fin 4:

inductive r2 where
| A : r2
| S : r2
| D : r2
| W : r2
  deriving Fintype


open r2
def go₂ : r2 →ℤ×ℤ → ℤ×ℤ
/-
  to use this, make those_with_suffix work with any β, Fintype β instead of Fin b
  However, then we cannot use List.ofFn.
-/
| D => (. + ( 1,  0))
| A => (. + (-1,  0))
| W => (. + ( 0,  1))
| S => (. + ( 0, -1))


structure wasd where
  a : ℤ×ℤ → ℤ×ℤ := go₂ A
  s : ℤ×ℤ → ℤ×ℤ := go₂ S
  d : ℤ×ℤ → ℤ×ℤ := go₂ D
  w : ℤ×ℤ → ℤ×ℤ := go₂ W
-- open R2
def R2 :wasd := {
}


example : (go₂ D) ∘ (go₂ A) = (go₂ A) ∘ (go₂ D) := by unfold go₂; simp

example : R2.d ∘ R2.a = R2.a ∘ R2.d := by
  unfold R2
  simp
  unfold go₂; simp


theorem finfin {l : ℕ} {k: Fin l} (i : Fin k): i.1 < l := calc
  _ < k.1 := i.isLt
  _ < l   := k.isLt

def F : Bool → ℕ := λ b ↦ ite (b=true) 1 0

/- Start of unused, other lattice structures. -/

def quad₃ : Fin 6 → ℤ×ℤ×ℤ → ℤ×ℤ×ℤ
| 0 => (. + ( 1, 0, 0))
| 1 => (. + (-1, 0, 0))
| 2 => (. + ( 0, 1, 0))
| 3 => (. + ( 0,-1, 0))
| 4 => (. + ( 0, 0, 1))
| 5 => (. + ( 0, 0,-1))

def pp : ℤ×ℤ → ℤ×ℤ := (. + ( 1, 1))
def go_D : ℤ×ℤ → ℤ×ℤ := (. + ( 1, 0))
def sp : ℤ×ℤ → ℤ×ℤ := (. + ( 0, 1))

def mm : ℤ×ℤ → ℤ×ℤ := (. + (-1,-1))
def go_A : ℤ×ℤ → ℤ×ℤ := (. + (-1, 0))
def sm : ℤ×ℤ → ℤ×ℤ := (. + ( 0,-1))

def pm : ℤ×ℤ → ℤ×ℤ := (. + ( 1,-1))
def mp : ℤ×ℤ → ℤ×ℤ := (. + (-1, 1))

def go_X : ℤ×ℤ → ℤ×ℤ := λ x ↦ ite (Even x.2) (sp x) (pp x)
def go_W : ℤ×ℤ → ℤ×ℤ := λ x ↦ ite (Even x.2) (mm x) (sm x)

def go_Z : ℤ×ℤ → ℤ×ℤ := λ x ↦ ite (Even x.2) (mp x) (sp x)
def go_E : ℤ×ℤ → ℤ×ℤ := λ x ↦ ite (Even x.2) (sm x) (pm x)

def quad : Fin 4 → ℤ×ℤ → ℤ×ℤ
| 0 => go_D
| 1 => go_A
| 2 => sp
| 3 => sm

-- move_hex represents the degree-6 hexagonal/triangular lattice, although that in itself requires checking.
-- This representation was designed to make the y-axis vertical to fit with a computer game.
def move_hex : Fin 6 → ℤ×ℤ → ℤ×ℤ
| 0 => go_D
| 1 => go_A
| 2 => go_X
| 3 => go_W
| 4 => go_E
| 5 => go_Z
#eval move_hex 0 (0,0)
#eval move_hex 5 (1,0)

-- If computer games are not to be used we can use a simpler implementation:
def goX : ℤ×ℤ → ℤ×ℤ := (. + (1,1))
def goW : ℤ×ℤ → ℤ×ℤ := (. + (-1,-1))
def goZ : ℤ×ℤ → ℤ×ℤ := (. + (0,-1))
def goE : ℤ×ℤ → ℤ×ℤ := (. + (0,1))
def goA := go_A
def goD := go_D
def move_hex' : Fin 6 → ℤ×ℤ → ℤ×ℤ
| 0 => goD
| 1 => goA
| 2 => goE
| 3 => goZ
| 4 => goX
| 5 => goW
-- Using move_hex' we have that each entry in quad is in move_hex':
theorem embed_models : ∀ i : Fin 4, ∃ j : Fin 6, quad i = move_hex' j
| 0 => by exists 0
| 1 => by exists 1
| 2 => by exists 2
| 3 => by exists 3

example : go_X ∘ go_W = id := by
  apply funext; intro x; unfold go_X go_W mm sp pp sm; simp; have h₁: x.2 - 1 = x.2 + -1 := rfl
  by_cases h : (Even x.2); rw [if_pos h]
  simp; simp_rw [← h₁];
  rw [if_neg (Int.odd_iff_not_even.mp (Even.sub_odd h (Int.odd_iff.mpr (by exact rfl))))]
  . exact add_eq_of_eq_sub rfl
  rw [if_neg h]
  simp; simp_rw [← h₁];
  rw [if_pos (Odd.sub_odd (Int.odd_iff_not_even.mpr h) (Int.odd_iff.mpr (by exact rfl)))]
  . exact add_eq_of_eq_sub rfl

example : go_Z ∘ go_E = id := by
  apply funext; intro x; unfold go_E go_Z sp sm pm; simp; have h₁: x.2 - 1 = x.2 + -1 := rfl
  by_cases h : (Even x.2); rw [if_pos h]
  simp; simp_rw [← h₁];
  rw [if_neg (Int.odd_iff_not_even.mp (Even.sub_odd h (Int.odd_iff.mpr (by exact rfl))))]
  . exact add_eq_of_eq_sub rfl
  rw [if_neg h]
  simp;simp_rw [← h₁];
  rw [if_pos (Odd.sub_odd (Int.odd_iff_not_even.mpr h) (Int.odd_iff.mpr (by exact rfl)))]
  . exact add_eq_of_eq_sub rfl

  -- If these have been labeled correctly then we should have DWZ=id and EAX=id:
  example: go_Z ∘ go_W ∘ go_D = id := by
    apply funext; intro x; unfold go_Z go_W go_D mm sm sp mp;
    simp; have h₁: x.2 - 1 = x.2 + -1 := rfl
    by_cases h : (Even x.2); rw [if_pos h]
    simp; simp_rw [← h₁];
    rw [if_neg (Int.odd_iff_not_even.mp (Even.sub_odd h (Int.odd_iff.mpr (by exact rfl))))]
    cases x
    . simp

    rw [if_neg h]
    simp;simp_rw [← h₁];
    rw [if_pos (Odd.sub_odd (Int.odd_iff_not_even.mpr h) (Int.odd_iff.mpr (by exact rfl)))]
    cases x
    . simp

example: go_X ∘ go_A ∘ go_E = id := by
    apply funext; intro x; unfold go_X go_A go_E sm sp pp pm;
    simp; have h₁: x.2 - 1 = x.2 + -1 := rfl
    by_cases h : (Even x.2); rw [if_pos h]
    simp; simp_rw [← h₁];
    rw [if_neg (Int.odd_iff_not_even.mp (Even.sub_odd h (Int.odd_iff.mpr (by exact rfl))))]
    cases x
    . simp

    rw [if_neg h]
    simp;simp_rw [← h₁];
    rw [if_pos (Odd.sub_odd (Int.odd_iff_not_even.mpr h) (Int.odd_iff.mpr (by exact rfl)))]
    cases x
    . simp


example : go_D ∘ go_A = id := by
  apply funext
  intro x
  unfold go_D
  unfold go_A
  simp
  exact add_eq_of_eq_sub rfl

example : go_E ∘ go_Z = id := by
  apply funext; intro x; unfold go_E go_Z pm sm mp sp; simp;
  by_cases h : (Even x.2); rw [if_pos h]; simp;

  cases x; simp; simp at h; have : Odd (snd + 1) := Even.add_one h
  . exact Int.odd_iff_not_even.mp this
  rw [if_neg h]; simp;

  cases x; simp; simp at h; have : Odd snd := Int.odd_iff_not_even.mpr h
  . exact Int.even_add_one.mpr h

example : go_W ∘ go_X = id := by
  apply funext; intro x; unfold go_W go_X sm mm sp pp; simp;
  by_cases h : (Even x.2); rw [if_pos h]; simp;

  cases x; simp; simp at h; have : Odd (snd + 1) := Even.add_one h
  . exact Int.odd_iff_not_even.mp this
  rw [if_neg h];

  cases x;  simp at h; have : Odd snd := Int.odd_iff_not_even.mpr h
  simp
  . exact Int.even_add_one.mpr h

-- Is this group presentation characterized by : abelian; three pairs of inverses; and DWZ=EAX=id?
-- yes, because given D and E,
-- W = (ZD).inv = D.inv Z.inv = D.inv E
-- A =                          D.inv
-- Z =                          E.inv
-- X = W.inv =                  E.inv D
-- and all powers D^m E^n are distinct.
-- so this means we could have done R2 with (1,-1) and (-1,1) added instead of the "Even" conditions.
-- This way P_{2D} ≤ P_{hex} can be proven "by inclusion".
-- Analogously for tri:

-- tri represents the degree-3 hexagonal/triangular lattice, although that in itself requires checking

def go_WS : ℤ×ℤ → ℤ×ℤ := λ x ↦ ite (Even (x.1+x.2)) (sp x) (sm x)

-- To show P_tri ≤ P_2D this is handy:
example : ∀ x, go_WS x = sp x
             ∨ go_WS x = sm x := by
  intro x
  unfold go_WS sp sm
  simp
  exact em (Even (x.1 + x.2))

-- What is less clear is P_hex < > P_3D

def tri : Fin 3 → ℤ×ℤ → ℤ×ℤ
| 0 => go_D
| 1 => go_A
| 2 => go_WS


lemma go_WS_eval:  (match (motive := Fin 3 → ℤ × ℤ → ℤ × ℤ) 2 with
  | 0 => go_D
  | 1 => go_A
  | 2 => fun x => if Even (x.1 + x.2) then sp x else sm x)
  x =  if Even (x.1 + x.2) then sp x else sm x := rfl


def embeds_in {α:Type} {b₀ b₁ : ℕ} (go₀ : Fin b₀ → α → α)
(go₁ : Fin b₁ → α → α) :=
∀ i : Fin b₀, ∀ x : α, ∃ j : Fin b₁, go₀ i x = go₁ j x

def is_embedding  {α:Type} {b₀ b₁ : ℕ} (go₀ : Fin b₀ → α → α)
(go₁ : Fin b₁ → α → α) (f : Fin b₀ → α → Fin b₁) :=
∀ i : Fin b₀, ∀ x : α, go₀ i x = go₁ (f i x) x



def embeds_in_strongly {α:Type} {b₀ b₁ : ℕ} (go₀ : Fin b₀ → α → α)
(go₁ : Fin b₁ → α → α) :=
∃ f : Fin b₀ → α → Fin b₁, is_embedding go₀ go₁ f

theorem remove_strongly  {α:Type} {b₀ b₁ : ℕ} {go₀ : Fin b₀ → α → α}
{go₁ : Fin b₁ → α → α} (h_embed: embeds_in_strongly go₀ go₁):
embeds_in go₀ go₁ := by
  rcases h_embed with ⟨f,hf⟩; intro i x; exists f i x; exact hf i x

-- For tri we can only assert a pointwise version of embed_models:
def tri_quad_embedding : Fin 3 → ℤ×ℤ → Fin 4
| 0 => λ _ ↦ 0
| 1 => λ _ ↦ 1
| 2 => λ x ↦ ite (Even (x.1 + x.2)) 2 3

def quad_hex_embedding : Fin 4 → ℤ×ℤ → Fin 6
| 0 => λ _ ↦ 0
| 1 => λ _ ↦ 1
| 2 => λ _ ↦ 2
| 3 => λ _ ↦ 3

theorem quad_hex_embedding_is_embedding :
  ∀ i : Fin 4, ∀ x : ℤ×ℤ, quad i x = move_hex' (quad_hex_embedding i x) x
  | 0 => λ _ ↦ rfl
  | 1 => λ _ ↦ rfl
  | 2 => λ _ ↦ rfl
  | 3 => λ _ ↦ rfl


theorem tri_quad_embedding_is_embedding :
  ∀ i : Fin 3, ∀ x : ℤ×ℤ, tri i x = quad (tri_quad_embedding i x) x
  | 0 => λ x ↦ rfl
  | 1 => λ x ↦ rfl
  | 2 => λ x ↦ by
    by_cases h: Even (x.1+x.2)
    unfold tri go_WS; rw [go_WS_eval,if_pos h];
    have : tri_quad_embedding 2 x = 2 := by
      unfold tri_quad_embedding
      have : (match (motive := Fin 3 → ℤ × ℤ → Fin 4) 2 with
        | 0 => fun _ => 0
        | 1 => fun _ => 1
        | 2 => fun x => if Even (x.1 + x.2) then 2 else 3)
        = (fun x => if Even (x.1 + x.2) then 2 else 3) := rfl
      . rw [this]; simp; tauto
    . rw [this]; rfl

    have : tri_quad_embedding 2 x = 3 := by
      unfold tri_quad_embedding
      have : (match (motive := Fin 3 → ℤ × ℤ → Fin 4) 2 with
        | 0 => fun _ => 0
        | 1 => fun _ => 1
        | 2 => fun x => if Even (x.1 + x.2) then 2 else 3) = fun x => if Even (x.1 + x.2) then 2 else 3
          := rfl
      rw [this]; simp; tauto
    rw [this]; unfold quad
    have : (match (motive := Fin 4 → ℤ × ℤ → ℤ × ℤ) 3 with
      | 0 => go_D
      | 1 => go_A
      | 2 => sp
      | 3 => sm) x = sm x := by rfl
    rw [this]
    unfold tri go_WS
    have : (match (motive := Fin 3 → ℤ × ℤ → ℤ × ℤ) 2 with
    | 0 => go_D
    | 1 => go_A
    | 2 => fun x => if Even (x.1 + x.2) then sp x else sm x)
    = (fun x => if Even (x.1 + x.2) then sp x else sm x) := rfl
    rw [this]; simp; tauto

theorem embeds_strongly_tri_quad : embeds_in_strongly tri quad := by
  exists tri_quad_embedding
  exact tri_quad_embedding_is_embedding

theorem embeds_strongly_quad_hex : embeds_in_strongly quad move_hex' := by
  exists quad_hex_embedding
  exact quad_hex_embedding_is_embedding


theorem embeds_tri_quad : embeds_in tri quad
| 0 => λ x ↦ by exists 0;
| 1 => λ x ↦ by exists 1;
| 2 => λ x ↦ by
  exact dite (Even (x.1 + x.2))
    (by intro h; exists 2; unfold tri go_WS; rw [go_WS_eval,if_pos h]; rfl)
    (by intro h; exists 3; unfold tri go_WS; rw [go_WS_eval,if_neg h]; rfl)

theorem embeds_quad_hex : embeds_in quad move_hex'
| 0 => λ x ↦ by exists 0;
| 1 => λ x ↦ by exists 1;
| 2 => λ x ↦ by exists 2;
| 3 => λ x ↦ by exists 3;


-- A fundamental relation for tri:
example: go_D ∘ go_WS ∘ go_A ∘ go_A ∘ go_WS ∘ go_D = id := by
  apply funext; intro x; unfold go_D go_WS go_A sp sm; simp
  by_cases h : (Even (x.1 + 1 + x.2))
  rw [if_pos h]
  have h₀ : Even (x.1 + x.2 + 1) := by rw [add_assoc,add_comm 1] at h; rw [add_assoc]; exact h
  simp; have : ¬ Even (x.1 + -1 + (x.2+1)) := by ring_nf; exact Int.even_add_one.mp h₀
  rw [if_neg this]
  have : (((1:ℤ), (0:ℤ)) + ((0, 1) + ((-1, 0) + ((-1, 0) + ((0, -1) + (1, 0)))))) = (0,0) := by decide
  repeat (rw [add_assoc]);
  . rw [this]; simp

  rw [if_neg h]; simp
  rw [add_assoc,add_comm,add_assoc,add_comm] at h
  have : Odd (x.2 + x.1 + 1) := Int.odd_iff_not_even.mpr h
  have : Even (x.2 + x.1)    := by rcases this with ⟨k,hk⟩; simp at hk; exists k; rw [hk]; ring
  rw [add_comm] at this
  have : Even (x.1 + -1 + (x.2 + -1)) := by
    ring_nf; rw [add_assoc,add_comm]; exact Even.add this (Int.even_iff.mpr rfl)
  rw [if_pos this]; repeat (rw [add_assoc])
  have : (((1:ℤ), (0:ℤ)) + ((0, -1) + ((-1, 0) + ((-1, 0) + ((0, 1) + (1, 0)))))) = (0,0) := by decide
  . rw [this]; simp

/- End of unused, other lattice structures. -/


def nearby_with  {α:Type} [OfNat α 0]
{β : Type} [Fintype β]
(go : β → α → α)
[DecidableEq α]
[DecidablePred (λ (i,v,w) ↦ go i v = w)]
[∀ i v w, Decidable (go i v = w)]
(p q : α) : Bool :=
∃ a : β, q = go a p

instance   {α:Type} [OfNat α 0]
{β : Type} [Fintype β]
(go : β → α → α)
[DecidableEq α]
[DecidablePred (λ (i,v,w) ↦ go i v = w)]
[∀ i v w, Decidable (go i v = w)] (p q : α) : Decidable (nearby_with go p q) := inferInstance

def point_achieved_with  {α:Type} [OfNat α 0]
{β : Type} [Fintype β]
(go : β → α → α)
[DecidableEq α]
[DecidablePred (λ (i,v,w) ↦ go i v = w)] {l : ℕ}
  (fold : Vector (α) l) (a b : Fin l) (phobic : Vector Bool l) : Bool
:= by {
  exact phobic.get a && phobic.get b && a.1.succ < b.1 && nearby_with go (fold.get a) (fold.get b)
}

instance   {α:Type} [OfNat α 0]
{β : Type} [Fintype β]
(go : β → α → α)
[DecidableEq α]
[DecidablePred (λ (i,v,w) ↦ go i v = w)] {l : ℕ}
  (fold : Vector (α) l) (a b : Fin l) (phobic : Vector Bool l) :
  Decidable (point_achieved_with go fold a b phobic) := inferInstance

def pts_at_with_modern {α:Type} [OfNat α 0]
{β : Type} [Fintype β]
(go : β → α → α)
[DecidableEq α]
[DecidablePred (λ (i,v,w) ↦ go i v = w)]  {l:ℕ}
(k : Fin l) (ph : Vector Bool l)
  (fold : Vector α l) :=
  List.sum (
    List.map F (
      List.ofFn (λ i : Fin k ↦ point_achieved_with (go : β → α → α) fold ⟨i.1,finfin i⟩ k ph)
    )
  )

instance  {α:Type} [OfNat α 0]
{β : Type} [Fintype β]
(go : β → α → α)
[DecidableEq α]
[DecidablePred (λ (i,v,w) ↦ go i v = w)]  {l:ℕ}
(k : Fin l) (ph : Vector Bool l)
  (fold : Vector α l) : DecidablePred (λ a ↦ pts_at_with_modern go k ph fold = a) :=
  inferInstance

def points_obtained {α:Type} [OfNat α 0]
{β : Type} [Fintype β]
(go : β → α → α)
[DecidableEq α]
[DecidablePred (λ (i,v,w) ↦ go i v = w)]  {l:ℕ} (ph : Vector Bool l)
  (fold : Vector α l) := List.sum (List.ofFn (λ i : Fin l ↦ pts_at_with_modern go i ph (fold)))

instance {α:Type} [OfNat α 0]
{β : Type} [Fintype β]
(go : β → α → α)
[DecidableEq α]
[DecidablePred (λ (i,v,w) ↦ go i v = w)]  {l:ℕ} (ph : Vector Bool l)
  (fold : Vector α l) : DecidablePred (λ a ↦ points_obtained go ph fold = a) :=
  inferInstance

/- The use of OfNat here is a clever(?) way of indicating that all folds should start at the origin,
and we only try to do protein folding in lattices that have a natural notion of base point or zero.
-/
def wk {α:Type} [OfNat α 0]
{β : Type} [Fintype β]
(go : β → α → α)
  (l : List β) :  {l : List α // l ≠ List.nil} := by {
  induction l
  . exact ⟨[0], List.cons_ne_nil _ _⟩
  . exact ⟨(go head (List.head tail_ih.1 tail_ih.2)) :: tail_ih.1, List.cons_ne_nil _ _⟩
}

-- Make everything work with wk_vec instead of wk as it's stronger and needed
def wk_vec {α:Type} [OfNat α 0]
{β : Type} [Fintype β]
(go : β → α → α)
  (l : List β) : Vector α l.length.succ := by {
  induction l
  . exact ⟨[0], rfl⟩
  have : tail_ih.1 ≠ [] := by
    have : tail_ih.1.length = tail.length.succ := tail_ih.2
    intro hc
    rw [hc] at this
    contrapose this
    simp
  exact ⟨(go head (List.head tail_ih.1 this)) :: tail_ih.1, by simp⟩
}



/- Since "code generator does not support recursor 'List.rec' yet,
consider using 'match ... with' and/or structural recursion"
we write this:
-/
def vector_succ_ne_nil {α :Type} {k:ℕ}
(tail_ih: Vector α k.succ)
: tail_ih.1 ≠ [] := by
    have : tail_ih.1.length = k.succ := tail_ih.2
    intro hc
    rw [hc] at this
    contrapose this
    simp

def path_recursion {α β: Type} {tail_length: ℕ}
(go: β → α → α) (head: β) (tail_ih: Vector α (Nat.succ (tail_length)))
: Vector α (Nat.succ (tail_length.succ))
:= ⟨(go head (List.head tail_ih.1 (vector_succ_ne_nil tail_ih))) :: tail_ih.1, by simp⟩

instance  {α β: Type} [DecidableEq α] {tail_length: ℕ} (go: β → α → α) (head: β)
(tail_ih: Vector α (Nat.succ (tail_length))) : DecidablePred (λ x ↦ path_recursion go head tail_ih = x) := inferInstance

-- Here we avoid List.rec and use structural induction.
-- Adding [DecidableEq α] removes the noncomputable property.
def path {α:Type} [OfNat α 0]
{β : Type} [Fintype β]
(go : β → α → α) :
  (l : List β) → Vector α l.length.succ
| [] => ⟨[0], rfl⟩
| head :: tail => path_recursion go head (path go tail)



-- now need a function transforming a sequence
def morph  {α:Type} [OfNat α 0] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
(go₀ : Fin b₀ → α → α)
 (l : List (Fin b₀)) : List (Fin b₁) := by
  induction l
  . exact []
  let Q := path go₀ tail
  . exact (f head Q.head) :: tail_ih

-- need to prove that the morph has certain properties if f is an embedding
-- namely that path is the same
-- first prove morph is length-preserving:
theorem  morph_is_length_preserving  {α:Type} [OfNat α 0] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
(go₀ : Fin b₀ → α → α) (l : List (Fin b₀)) :
(morph f go₀ l).length = l.length := by
  induction l
  unfold morph
  rfl
  unfold morph
  repeat (rw [List.length_cons])
  simp
  rw [← tail_ih]
  congr






instance  {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α)
  (l : List β) : DecidablePred (λ a ↦ path go l = a) :=
  inferInstance

instance  {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α)
  (l : List β) : DecidablePred (λ a ↦ wk_vec go l = a) :=
  inferInstance


def walk_vec {α:Type} [OfNat α 0]
{β : Type} [Fintype β]
(go : β → α → α)
(l : List β) : List α :=
  (wk_vec go l.reverse).1

def walk {α:Type} [OfNat α 0]
{β : Type} [Fintype β]
(go : β → α → α)
(l : List β) : List α :=
  (wk go l.reverse).1


theorem moves_len'_vec
  {α:Type} [OfNat α 0]
  {β : Type} [Fintype β]
  (go : β → α → α) (l : List β) :
  (wk_vec go l).1.length = l.length.succ := (wk_vec go l).2

theorem moves_len'_vec'
  {α:Type} [OfNat α 0]
  {β : Type} [Fintype β]
  (go : β → α → α) (l : List β) :
  (path go l).1.length = l.length.succ := (path go l).2

theorem moves_len'
  {α:Type} [OfNat α 0]
  {β : Type} [Fintype β]
  (go : β → α → α) (l : List β) :
  (wk go l).1.length = l.length.succ := by {
  induction l
  . unfold wk; rw [List.length_cons]; rfl
  . unfold wk; simp; rw [← Nat.succ_eq_add_one,← tail_ih]; unfold wk; simp
}

-- def wkVec {α:Type} [OfNat α 0]
-- {β : Type} [Fintype β]
-- (go : β → α → α) {lh:ℕ}
--   (l : Vector β lh) : Vector α lh.succ := by
--     exact ⟨(wk_vec go l.1).1,by
--       let R := moves_len'_vec go l.1
--       rw [R]
--       simp
--     ⟩


theorem moves_len
  {α:Type} [OfNat α 0]
  {β : Type} [Fintype β]
  (go : β → α → α) (l : List β) :
  (walk go l).length = l.length.succ := by {
    unfold walk; rw [moves_len']; simp
}

/- It follows from embeds_tri_quad that any sequence of moves under tri generates a sequence in ℤ×ℤ
  that can also be generated using quad:
-/

theorem walk_not_nil
{b: ℕ}
{α: Type}
[OfNat α 0]
(tail: List (Fin b))
(go: Fin b → α → α)
: walk go tail ≠ []
:= by
    intro hc
    apply congrArg List.length at hc
    rw [moves_len go tail] at hc
    simp at hc



theorem zero_list_not_nil₀
{α: Type}
[OfNat α 0]
: [(0:α)] ≠ [] := by
  intro hc
  apply congrArg List.length at hc
  simp at hc

theorem zero_list_not_nil
(α: Type)
[OfNat α 0]
: { l : List α // l ≠ []} :=
⟨[0],zero_list_not_nil₀⟩



-- #eval wk quad (0 :: [1,2,0,2])
-- #eval (
--   quad 0 (List.getLast (wk quad [1,2,0,2]).1.reverse (List_reverse_ne_nil (wk _ _).2))
-- )
-- #eval wk quad [1,2,0,2]
-- The above is evidence for the below.

def anchor {α:Type} (l : { l : List α // l ≠ []}) : α
:= l.1.head l.2

def anchor_vec {α:Type} {n:ℕ} (l: Vector α n.succ) : α
:= l.1.head (by
  intro hc
  apply congrArg List.length at hc
  simp at hc
)

theorem eq_anchor_vec {b:ℕ} {α:Type} [OfNat α 0] (hd: Fin b) (tl: List (Fin b))
            (go: Fin b → α → α)        : (wk_vec go (hd :: tl)).1
= (go hd (anchor_vec (wk_vec go tl))) :: (wk_vec go tl).1
:= by
  rfl

theorem eq_anchor {b:ℕ} {α:Type} [OfNat α 0] (hd: Fin b) (tl: List (Fin b))
            (go: Fin b → α → α)
                                : wk go (hd :: tl)
= (go hd (anchor (wk go tl))) :: wk go tl
:= by
  rfl




theorem _is_ {α:Type} [OfNat α 0] {b₀ b₁ : ℕ} (go₀ : Fin b₀ → α → α)
(go₁ : Fin b₁ → α → α) (h_embed : embeds_in go₀ go₁):
  ∀ l : List (Fin b₀), ∃ v : List (Fin b₁), (wk go₀ l).1 = (wk go₁ v).1 := by
  intro l
  induction l
  . exists []
  rcases tail_ih with ⟨u,hu⟩
  rcases (h_embed head (anchor (wk go₀ tail))) with ⟨j,hj⟩
  exists j :: u
  . rw [eq_anchor head tail go₀, hu, hj, eq_anchor j u go₁, SetCoe.ext hu]

-- theorem _is_vec {α:Type} [OfNat α 0] {b₀ b₁ : ℕ} (go₀ : Fin b₀ → α → α)
-- (go₁ : Fin b₁ → α → α) (h_embed : embeds_in go₀ go₁) {lh:ℕ}:
--   ∀ l : Vector (Fin b₀) lh, ∃ v : Vector (Fin b₁) lh,
--   (wkVec go₀ l) = (wkVec go₁ v) := by
--   intro l
--   let Q := _is_ go₀ go₁ h_embed l.1
--   rcases Q with ⟨l1,hl1⟩
--   have hl_1 :  List.length l1 = lh := sorry
--   exists ⟨l1,hl_1⟩
--   unfold wkVec
--   simp
--   sorry


theorem tri_is_quad:
  ∀ l : List (Fin 3), ∃ v : List (Fin 4), (wk tri l).1 = (wk quad v).1 :=
  _is_ tri quad embeds_tri_quad

-- example (P:Bool) [Decidable P] (h : decide P = True) : P := of_eq_true h

theorem _is_'  {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
 {x y : α} (hn : nearby_with go₀ x y):
nearby_with go₁ x y := by
  unfold nearby_with at hn
  simp at hn
  rcases hn with ⟨a,ha⟩
  let Q := h_embed a x
  unfold nearby_with
  simp
  rw [ha]
  tauto

theorem tri_is_quad' (x y : ℤ×ℤ) (hn : nearby_with tri x y):
nearby_with quad x y := _is_' (embeds_tri_quad) hn

theorem point_achieved_with_embeds
  {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
 {l:ℕ}
  (fold : Vector α l) (a b : Fin l) (phobic : Vector Bool l)
  (htri: point_achieved_with go₀ fold a b phobic) :
         point_achieved_with go₁ fold a b phobic := by
  unfold point_achieved_with
  unfold point_achieved_with at htri
  simp
  simp at htri
  constructor
  tauto
  exact _is_' h_embed htri.2

theorem point_achieved_with_tri_quad {l:ℕ}
  (fold : Vector (ℤ×ℤ) l) (a b : Fin l) (phobic : Vector Bool l)
  (htri: point_achieved_with tri      fold a b phobic) :
         point_achieved_with quad fold a b phobic :=
point_achieved_with_embeds (embeds_tri_quad) _ _ _ _ htri

theorem F_monotone {P Q : Bool}
(h : P ≤ Q) : F P ≤ F Q := by
  unfold F; by_cases h₀: (P = true); rw [if_pos h₀]; by_cases h₁: (Q = true)
  . rw [if_pos h₁]
  rw [if_neg h₁]; exfalso; tauto; rw [if_neg h₀]
  . exact zero_le _

theorem F_
  {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
 {l:ℕ}
  (fold : Vector α l) (a b : Fin l) (phobic : Vector Bool l):
   F (point_achieved_with go₀      fold a b phobic) ≤
   F (point_achieved_with go₁ fold a b phobic) := by
  exact F_monotone (point_achieved_with_embeds h_embed fold a b phobic)


theorem F_tri_quad
 {l:ℕ}
  (fold : Vector (ℤ×ℤ) l) (a b : Fin l) (phobic : Vector Bool l):
   F (point_achieved_with tri      fold a b phobic) ≤
   F (point_achieved_with quad fold a b phobic) := by
  -- exact F_monotone (point_achieved_with_tri_quad fold a b phobic)
  exact F_ (embeds_tri_quad) _ _ _ _


theorem pts_at_embeds
  {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)

{l:ℕ} (k:Fin l) (ph : Vector Bool l) (fold : Vector α l):
pts_at_with_modern go₀ k ph fold ≤
pts_at_with_modern go₁ k ph fold := by
  unfold pts_at_with_modern
  apply List.Forall₂.sum_le_sum
  refine List.forall₂_iff_zip.mpr ?h.a
  constructor
  simp
  intro a b hab
  simp at hab

  let Q := List.get_of_mem hab
  rcases Q with ⟨i,hi⟩
  simp at hi
  cases hi
  rw [← left]
  rw [← right]
  exact F_ (h_embed) _ _ _ _


theorem pts_at_tri_quad {l:ℕ} (k:Fin l) (ph : Vector Bool l) (fold : Vector (ℤ×ℤ) l):
pts_at_with_modern      tri k ph fold ≤
pts_at_with_modern quad k ph fold :=
pts_at_embeds embeds_tri_quad _ _ _


theorem pts_embeds
  {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
{l:ℕ} (ph : Vector Bool l) (fold : Vector α l):
points_obtained go₀ ph fold ≤
points_obtained go₁ ph fold := by
  unfold points_obtained
  apply List.Forall₂.sum_le_sum
  refine List.forall₂_iff_zip.mpr ?h.a
  constructor
  simp
  intro a b hab

  let Q := List.get_of_mem hab
  rcases Q with ⟨i,hi⟩
  simp at hi
  cases hi
  rw [← left]
  rw [← right]
  exact pts_at_embeds h_embed _ _ _


theorem pts_tri_quad {l:ℕ} (ph : Vector Bool l) (fold : Vector (ℤ×ℤ) l):
points_obtained  tri  ph fold ≤
points_obtained quad  ph fold :=
pts_embeds embeds_tri_quad _ _




-- We now seek an upper bound for the objective function in protein folding.
-- We seek any bound, no matter how unsharp for now.
theorem getTrivBound {α:Type} {l:ℕ} (f : (Fin l) → α) (F₀ : α → ℕ)
  (h : ∀ a, F₀ a ≤ 1) :
  List.sum (List.map F₀ (List.ofFn f)) ≤ List.length (List.map F₀ (List.ofFn f)) * 1 --l • 1
  := by
    exact List.sum_le_card_nsmul _ _ (by {
      intro x hx
      simp at hx
      rw [List.mem_ofFn] at hx
      simp at hx
      rcases hx with ⟨y,hy⟩
      rw [← hy]
      exact h (f y)
    })

theorem F_bound : ∀ a : Bool, F a ≤ 1 := by
  intro a; unfold F; cases a; simp; simp

theorem quad_bound₀  {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α)
{l:ℕ} (ph : Vector Bool l) (fold : Vector α l) (i:Fin l):
pts_at_with_modern go i ph fold ≤ i := by
  unfold pts_at_with_modern
  let Q := getTrivBound (
    fun i_1 : Fin i => point_achieved_with go fold ⟨i_1.1,finfin i_1⟩ i ph
  ) F F_bound
  simp at Q
  simp
  exact Q


theorem quad_bound₂   {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α)
{l:ℕ} (ph : Vector Bool l) (fold : Vector α l):
points_obtained go ph fold ≤ l * l := by
  unfold points_obtained
  have hl: List.length (List.ofFn fun i => pts_at_with_modern go i ph fold) = l
  := by
    let Q := List.length_ofFn (fun i => pts_at_with_modern go i ph fold)
    exact Q
  have : (∀ x ∈ List.ofFn fun i => pts_at_with_modern go i ph fold, x ≤ l)
  := by
    intro x hx
    rw [List.mem_ofFn] at hx
    simp at hx
    rcases hx with ⟨y,hy⟩
    rw [← hy]
    calc
    _ ≤ y.1 := quad_bound₀ go ph fold y
    _ ≤ _   := Fin.is_le'
  let Q := List.sum_le_card_nsmul (
    (List.ofFn fun i => pts_at_with_modern go i ph fold)
  ) l this
  rw [hl] at Q
  exact Q

def P_bound   {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α) {l:ℕ} (ph : Vector Bool l) (q : ℕ) :=
∀ fold : Vector α l, points_obtained go ph fold ≤ q

-- P_bound should only quantify over valid foldings:
-- Here is maybe a quick fix for how to do so:
theorem wk_vec_len {α: Type} [OfNat α 0] [DecidableEq α] {β: Type} [Fintype β]
{go: β → α → α} {l: ℕ} {moves: Vector β l}
: List.length (wk_vec go moves.1).1 = Nat.succ l
:= by
    rw [moves_len'_vec go moves.1]
    simp

theorem path_len {α: Type} [OfNat α 0] [DecidableEq α] {β: Type} [Fintype β]
(go: β → α → α) {l: ℕ} (moves: Vector β l)
: List.length (path go moves.1).1 = Nat.succ l
:= by
    rw [moves_len'_vec' go moves.1]
    simp

theorem two_heads {α : Type} {k :ℕ} (v: Vector α k.succ) (w : List α) (hw : w ≠ [])
(h : v.1 = w) : Vector.head v = List.head w hw := by
  symm at h; cases w; tauto; simp
  have : v = head ::ᵥ ⟨tail,by let v2 := v.2; rw [← h] at v2; simp at v2; tauto⟩ := by
    apply Vector.eq; simp; rw [h]; rfl
  rw [this]; simp

theorem path_cons {α:Type} [OfNat α 0] [DecidableEq α] {b₀ : ℕ}
(go₀ : Fin b₀ → α → α)
(head : Fin b₀) (tail : List (Fin b₀))
   : (path go₀ (head ::        tail)).1 =
             ((go₀  head (path go₀ tail).head) :: (path go₀ tail).1) := by
    have : path go₀ (head :: tail) = path_recursion go₀ head (path go₀ tail) := rfl
    rw [this]; let tail_ih := path go₀ tail
    have : path_recursion go₀ head (path go₀ tail) =
    ⟨(go₀ head (List.head tail_ih.1 (vector_succ_ne_nil tail_ih))) :: tail_ih.1, by simp⟩
      := rfl
    rw [this]; simp; rw [two_heads]; rfl

-- Finished February 10, 2024:
theorem transform  {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
(go₀ : Fin b₀ → α → α) (go₁ : Fin b₁ → α → α)
 (l : List (Fin b₀)) (h_embed: is_embedding go₀ go₁ f): by
  let Q := (
    ⟨(path go₁ (morph f go₀ l)).1,by
      rw [path_len go₁ ⟨(morph f go₀ l),(morph_is_length_preserving f go₀ l)⟩]
    ⟩
    : Vector (α) l.length.succ)
  let R := path go₀ l
  exact Q = R
:= by
  apply SetCoe.ext; simp; unfold is_embedding at h_embed; induction l; simp; unfold morph; simp
  . rfl
  have : (morph f go₀ (head :: tail)) = (f head ((path go₀ tail).head)) :: (morph f go₀ (tail)) := rfl
  rw [this];

  have : (path go₀ (head ::        tail)).1 =
             ((go₀  head (path go₀ tail).head) :: (path go₀ tail).1) :=
    path_cons _ _ _

  rw [this]
  let a := (Vector.head (path go₀ tail))

  have : (path go₁ ((f head (Vector.head (path go₀ tail))) :: (morph f go₀ tail))).1
  =         (( go₁  (f head (Vector.head (path go₀ tail))) (path go₁ (morph f go₀ tail)).head) ::ᵥ (path go₁ (morph f go₀ tail))).1
    := path_cons _ _ _

  rw [this]
  simp
  constructor
  rw [h_embed head a]
  simp
  have :  (path go₁ (morph f go₀ tail)) = ⟨(path go₀ tail).1,(by
    rw [morph_is_length_preserving]
    exact (path go₀ tail).2
  )⟩ := Vector.eq _ _ (by unfold Vector.toList; rw [← tail_ih])
  rw [this]
  have hn: (path go₀ tail).1 ≠ [] := by
    intro hc; apply congrArg List.length at hc; simp at hc
  have hnz: ∃ a u, (path go₀ tail).1 = a :: u := by
    exact List.exists_cons_of_ne_nil hn
  have : Vector.head ⟨
        (path go₀ tail).1,
        ((by rw [morph_is_length_preserving]; exact (path go₀ tail).2)
        : List.length (path go₀ tail).1 = Nat.succ (List.length (morph f go₀ tail))
        )⟩ = Vector.head (path go₀ tail)
  := by
    rcases hnz with ⟨a,ha⟩; rcases ha with ⟨u,hu⟩; simp_rw [hu]
    have : Vector.head {
        val := a :: u,
        property := ((by rw [morph_is_length_preserving]; rw [← (path go₀ tail).2,hu]) : List.length (a :: u) = Nat.succ (List.length (morph f go₀ tail))) }
    = a := rfl
    rw [this,two_heads (path go₀ tail) ((path go₀ tail)).1 hn rfl]
    . simp_rw [hu]; simp
  . exact congr_arg _ this
  . rw [tail_ih]


def P_bound'   {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) (q : ℕ) :=
∀ moves : Vector β l,
points_obtained go ph (⟨(path go moves.1).1,path_len _ _⟩) ≤ q


instance    {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) (q : ℕ): DecidablePred (P_bound' go moves)
:= by
  unfold P_bound'
  unfold points_obtained
  exact inferInstance

instance   {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α) : DecidablePred fun n => P_bound' go ph n :=
  by
  unfold P_bound'
  unfold points_obtained
  exact inferInstance

#eval points_obtained tri ⟨[false],rfl⟩ ⟨[(0,0)],rfl⟩ ≤ 5


theorem P_bound_exists {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β] (go : β → α → α) {l:ℕ} (ph : Vector Bool l) :
∃ q, P_bound go ph q := by exists l*l; exact quad_bound₂ go ph

theorem P_bound'_exists {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β] (go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) :
∃ q, P_bound' go ph q := by
  exists l.succ*l.succ;
  unfold P_bound'
  intro moves
  let Q := quad_bound₂ go ph (⟨(path go moves.1).1,path_len _ _⟩)
  tauto

noncomputable instance   {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α) : DecidablePred fun n => P_bound go ph n :=
  by exact Classical.decPred fun n => P_bound go ph n



noncomputable def P_   {α:Type} [OfNat α 0] [DecidableEq α] {β : Type} [Fintype β]
(go : β → α → α) {l:ℕ} (ph : Vector Bool l) :ℕ := Nat.find (P_bound_exists go ph)

def P_'  {α:Type} [OfNat α 0] [DecidableEq α] {β : Type} [Fintype β]
(go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) :ℕ := Nat.find (P_bound'_exists go ph)

def P_tri'  {l:ℕ} := λ ph : Vector Bool l.succ ↦ P_' tri ph
def P_quad' {l:ℕ} := λ ph : Vector Bool l.succ ↦ P_' quad ph
def P_hex' {l:ℕ} := λ ph : Vector Bool l.succ ↦ P_' move_hex' ph


-- noncomputable def P_tri  {l:ℕ} := λ ph : Vector Bool l ↦ P_ tri ph
-- noncomputable def P_quad {l:ℕ} := λ ph : Vector Bool l ↦ P_ quad ph
-- noncomputable def P_hex {l:ℕ} := λ ph : Vector Bool l ↦ P_ move_hex' ph

#eval P_tri' ⟨[false],rfl⟩
-- #synth Decidable (P_bound' tri { val := [false], property := (_ : List.length [false] = List.length [false]) } 5)
-- #eval P_bound' tri ⟨[false],rfl⟩ 5


theorem p_embeds   {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
-- SHOULD MAYBE MAKE THIS β₀ and β₁?

{l:ℕ} (ph : Vector Bool l) : P_ go₀ ph ≤ P_ go₁ ph := by
  have : ∀  q, P_bound go₁ ph q → P_bound go₀ ph q := by
    intro _ hq fold
    calc
    _ ≤ points_obtained go₁ ph fold := pts_embeds h_embed _ _
    _ ≤ _                          := hq fold
  exact Nat.find_mono this

theorem p_embeds'   {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in_strongly go₀ go₁)
{l:ℕ} (ph : Vector Bool l.succ) : P_' go₀ ph ≤ P_' go₁ ph := by
  have : ∀  q, P_bound' go₁ ph q → P_bound' go₀ ph q := by
    intro _ hq moves
    let Q := pts_embeds (remove_strongly h_embed) ph (⟨(path go₀ moves.1).1,path_len _ _⟩)
    rcases h_embed with ⟨f,hf⟩
    let fold1 := (path go₀ moves.1).1
    let fold := ((⟨(path go₀ moves.1).1,path_len _ _⟩) : Vector α l.succ)
    let moves' := (⟨morph f go₀ moves.1,sorry⟩ : Vector (Fin b₁) l)
    -- need to let moves' be the embedded version. but there is no uniqueness
    -- in embeds_in
    let R := hq moves'
    -- calc
    -- _ ≤ points_obtained go₁ ph (⟨(wk_vec go fold.1).1,wk_vec_len⟩) := Q
    -- _ ≤ _                          := R
    have : points_obtained go₀ ph ⟨(path go₀ moves.1).1, path_len _ _⟩
         ≤ points_obtained go₁ ph ⟨(path go₀ moves.1).1, path_len _ _⟩    := Q
    -- have : points_obtained go₁ ph ⟨(path go₁ moves.1).1, path_len _ _⟩ ≤ q := R
    have : points_obtained go₁ ph ⟨(path go₁ moves'.1).1, path_len _ _⟩ ≤ q :=   sorry
    unfold is_embedding at hf


    sorry
  exact Nat.find_mono this

  -- February 8, 2024. This was surprisingly long and also surprisingly easy.
  -- The degree 3 "hexagonal lattice" protein folding model has an objective function
  -- P_tri that is bounded by that of the usual HP 2D model.
theorem ptriquad {l:ℕ} (ph : Vector Bool l) : P_ tri ph ≤ P_ quad ph :=
p_embeds embeds_tri_quad _

theorem pquadhex {l:ℕ} (ph : Vector Bool l) : P_ quad ph ≤ P_ move_hex' ph :=
p_embeds embeds_quad_hex _

/-
The analogous statement for P_quad and P_hex is even easier.
-/


-- example: P_tri ⟨[],rfl⟩ = 0 := by
--   unfold P_tri P_
--   unfold P_bound
--   simp
--   have : P_bound tri ⟨[],rfl⟩ 0 := by
--     unfold P_bound
--     intro fold
--     have : points_obtained tri ⟨[],rfl⟩ fold = 0 := by
--       unfold points_obtained pts_at_with_modern
--       -- TEDIOUS
--       sorry
--     exact Nat.le_zero.mpr this
--   exact (Nat.find_eq_zero (P_.proof_1 tri { val := [], property := rfl })).mpr this








example (a  : List (Fin 2)) (h₀ h₁ : a ≠ []):
a.getLast h₀ = a.getLast h₁ := by exact rfl




def first_nonzero_entry (w : List (Fin 4)) : Option (Fin 4) := by {
  induction w
  .  exact none
  .  exact ite (tail_ih ≠ none) tail_ih (ite (head = 0) none head)
}

-- By symmetry we may assume that all walks (folds) are orderly, although that in itself could deserve a proof.
def orderly (w: List (Fin 4)) := w.reverse.getLast? = some (0:Fin 4)
      ∧ first_nonzero_entry w = some 2

instance (w : List (Fin 4)) : Decidable (orderly w) := by unfold orderly; exact And.decidable


def stecher (x : List Bool) (w: List (Fin 4)): ℕ :=
  dite (w.length.succ = x.length)
    (λ h ↦ points_obtained
      quad
      (⟨x, rfl⟩ : Vector Bool x.length) -- no longer reverse somehow
      (⟨walk quad w,by {rw [moves_len quad w]; tauto}⟩ : Vector (ℤ×ℤ) x.length)
    )
    (λ _ ↦ 0)

def x : List Bool := [true,false,true,false,true,false, true,true]
#eval stecher x [0, 3, 1, 1, 2, 2, 0]
-- #eval stecher x [r2.D, r2.S, r2.A, r2.A, r2.W, r2.W, r2.D]
-- #eval stecher (x ++ [false]) [0, 3, 1, 1, 2, 2, 0].reverse

def stecher1 : Prop :=
  those_with_suffix'
    (λ w ↦ Function.Injective (λ i ↦ (walk quad w).get i))
    (λ w ↦ stecher x w > 2 ∧ orderly w)
    (Gap_nil' 4 7)
  = {⟨[0, 3, 1, 1, 2, 2, 0],rfl⟩}
instance : Decidable stecher1 := by {
  unfold stecher1
  apply decEq
}
-- #eval (myvec 4 7).length
-- #eval stecher1

def stecher2 : Prop :=
those_with_suffix'
    (λ w ↦ Function.Injective (λ i ↦ (walk quad w).get i))
    (
      λ w ↦ stecher (x ++ [false]) w > 2
        ∧ orderly w
    )
    (Gap_nil' 4 8) = ∅

def stecher_conjecture_counterexample : Prop := stecher1  ∧ stecher2


instance : Decidable stecher2 := by unfold stecher2; apply decEq
instance : Decidable stecher_conjecture_counterexample := by {
  unfold stecher_conjecture_counterexample
  unfold stecher1
  unfold stecher2
  exact And.decidable
}

-- #eval stecher2
-- #eval stecher_conjecture_counterexample
