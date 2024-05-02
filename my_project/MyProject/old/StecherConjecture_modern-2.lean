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



theorem finfin {l : ℕ} {k: Fin l} (i : Fin k): i.1 < l := calc
  _ < k.1 := i.isLt
  _ < l   := k.isLt


def nat_of_bool : Bool → ℕ := λ b ↦ ite (b=true) 1 0

theorem nat_of_bool_bound : ∀ a : Bool, nat_of_bool a ≤ 1 := by intro a; unfold nat_of_bool; cases a; simp; simp

theorem nat_of_bool_monotone {P Q : Bool}
(h : P ≤ Q) : nat_of_bool P ≤ nat_of_bool Q := by
  unfold nat_of_bool; by_cases h₀: (P = true); rw [if_pos h₀]; by_cases h₁: (Q = true)
  . rw [if_pos h₁]
  rw [if_neg h₁]; exfalso; tauto; rw [if_neg h₀]
  . exact zero_le _

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
def hex : Fin 6 → ℤ×ℤ → ℤ×ℤ
| 0 => goD
| 1 => goA
| 2 => goE
| 3 => goZ
| 4 => goX
| 5 => goW
-- Using hex we have that each entry in quad is in hex:
theorem embed_models : ∀ i : Fin 4, ∃ j : Fin 6, quad i = hex j
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
  apply funext; intro x; unfold go_D; unfold go_A; simp; exact add_eq_of_eq_sub rfl

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
  intro x; unfold go_WS sp sm; simp; exact em (Even (x.1 + x.2))

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

theorem embeds_of_strongly_embeds  {α:Type} {b₀ b₁ : ℕ} {go₀ : Fin b₀ → α → α}
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
  ∀ i : Fin 4, ∀ x : ℤ×ℤ, quad i x = hex (quad_hex_embedding i x) x
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

theorem embeds_strongly_quad_hex : embeds_in_strongly quad hex := by
  exists quad_hex_embedding
  exact quad_hex_embedding_is_embedding


theorem embeds_tri_quad : embeds_in tri quad
| 0 => λ x ↦ by exists 0;
| 1 => λ x ↦ by exists 1;
| 2 => λ x ↦ by
  exact dite (Even (x.1 + x.2))
    (by intro h; exists 2; unfold tri go_WS; rw [go_WS_eval,if_pos h]; rfl)
    (by intro h; exists 3; unfold tri go_WS; rw [go_WS_eval,if_neg h]; rfl)

theorem embeds_quad_hex : embeds_in quad hex
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

def pts_at_with {α:Type} [OfNat α 0]
{β : Type} [Fintype β]
(go : β → α → α)
[DecidableEq α]
[DecidablePred (λ (i,v,w) ↦ go i v = w)]  {l:ℕ}
(k : Fin l) (ph : Vector Bool l)
  (fold : Vector α l) :=
  List.sum (
    List.map nat_of_bool (
      List.ofFn (λ i : Fin k ↦ point_achieved_with (go : β → α → α) fold ⟨i.1,finfin i⟩ k ph)
    )
  )

instance  {α:Type} [OfNat α 0] {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
[DecidablePred (λ (i,v,w) ↦ go i v = w)] {l:ℕ} (k : Fin l) (ph : Vector Bool l)
  (fold : Vector α l) : DecidablePred (λ a ↦ pts_at_with go k ph fold = a) :=
  inferInstance

def pts_tot {α:Type} [OfNat α 0] {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
[DecidablePred (λ (i,v,w) ↦ go i v = w)]  {l:ℕ} (ph : Vector Bool l)
  (fold : Vector α l) := List.sum (List.ofFn (λ i : Fin l ↦ pts_at_with go i ph (fold)))

instance {α:Type} [OfNat α 0] {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
  [DecidablePred (λ (i,v,w) ↦ go i v = w)]  {l:ℕ} (ph : Vector Bool l)
  (fold : Vector α l) : DecidablePred (λ a ↦ pts_tot go ph fold = a) :=
  inferInstance

/- The use of OfNat here is a clever(?) way of indicating that all folds should start at the origin,
and we only try to do protein folding in lattices that have a natural notion of base point or zero.
-/

def vector_succ_ne_nil {α :Type} {k:ℕ}
(tail_ih: Vector α k.succ)
: tail_ih.1 ≠ [] := by
    have : tail_ih.1.length = k.succ := tail_ih.2
    intro hc; rw [hc] at this; contrapose this; simp

def path_recursion {α β: Type} {tail_length: ℕ}
(go: β → α → α) (head: β) (tail_ih: Vector α (Nat.succ (tail_length)))
: Vector α (Nat.succ (tail_length.succ))
:= ⟨(go head (List.head tail_ih.1 (vector_succ_ne_nil tail_ih))) :: tail_ih.1, by simp⟩

instance  {α β: Type} [DecidableEq α] {tail_length: ℕ} (go: β → α → α) (head: β)
(tail_ih: Vector α (Nat.succ (tail_length))) : DecidablePred (λ x ↦ path_recursion go head tail_ih = x) := inferInstance

-- Here we avoid List.rec and use structural induction.
-- Adding [DecidableEq α] removes the noncomputable property.
def path {α:Type} [OfNat α 0] {β : Type} [Fintype β] (go : β → α → α) :
(l : List β) → Vector α l.length.succ
| [] => ⟨[0], rfl⟩
| head :: tail => path_recursion go head (path go tail)


-- now need a function transform_of_embeding a sequence
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
  induction l; unfold morph; rfl; unfold morph; repeat (rw [List.length_cons])
  simp; rw [← tail_ih]; congr


theorem moves_len'_vec' {α:Type} [OfNat α 0] {β : Type} [Fintype β] (go : β → α → α) (l : List β) :
  (path go l).1.length = l.length.succ := (path go l).2


/- It follows from embeds_tri_quad that any sequence of moves under tri generates a sequence in ℤ×ℤ
  that can also be generated using quad:
-/


theorem zero_list_not_nil₀ {α: Type} [OfNat α 0] : [(0:α)] ≠ [] := by
  intro hc; apply congrArg List.length at hc; simp at hc

theorem zero_list_not_nil (α: Type) [OfNat α 0] : { l : List α // l ≠ []}
  := ⟨[0],zero_list_not_nil₀⟩

def anchor {α:Type} (l : { l : List α // l ≠ []}) : α := l.1.head l.2

def anchor_vec {α:Type} {n:ℕ} (l: Vector α n.succ) : α
:= l.1.head (by intro hc; apply congrArg List.length at hc; simp at hc)


theorem nearby_of_embeds  {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
 {x y : α} (hn : nearby_with go₀ x y):
nearby_with go₁ x y := by
  unfold nearby_with at hn; simp at hn; rcases hn with ⟨a,ha⟩; let Q := h_embed a x
  unfold nearby_with; simp; rw [ha]; tauto

theorem tri_is_quad' (x y : ℤ×ℤ) (hn : nearby_with tri x y):
nearby_with quad x y := nearby_of_embeds (embeds_tri_quad) hn

theorem point_achieved_with_of_embeds
  {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
 {l:ℕ}
  (fold : Vector α l) (a b : Fin l) (phobic : Vector Bool l)
  (htri: point_achieved_with go₀ fold a b phobic) :
         point_achieved_with go₁ fold a b phobic := by
  unfold point_achieved_with
  unfold point_achieved_with at htri
  simp; simp at htri; constructor; tauto; exact nearby_of_embeds h_embed htri.2

theorem point_achieved_with_tri_quad {l:ℕ}
  (fold : Vector (ℤ×ℤ) l) (a b : Fin l) (phobic : Vector Bool l)
  (htri: point_achieved_with tri      fold a b phobic) :
         point_achieved_with quad fold a b phobic :=
point_achieved_with_of_embeds (embeds_tri_quad) _ _ _ _ htri


theorem nat_of_bool_ {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁) {l:ℕ}
  (fold : Vector α l) (a b : Fin l) (phobic : Vector Bool l):
   nat_of_bool (point_achieved_with go₀      fold a b phobic) ≤
   nat_of_bool (point_achieved_with go₁ fold a b phobic) := by
  exact nat_of_bool_monotone (point_achieved_with_of_embeds h_embed fold a b phobic)

theorem pts_at_of_embeds {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
{l:ℕ} (k:Fin l) (ph : Vector Bool l) (fold : Vector α l):
pts_at_with go₀ k ph fold ≤
pts_at_with go₁ k ph fold := by
  unfold pts_at_with; apply List.Forall₂.sum_le_sum
  refine List.forall₂_iff_zip.mpr ?h.a; constructor; simp; intro a b hab; simp at hab
  let Q := List.get_of_mem hab
  rcases Q with ⟨i,hi⟩; simp at hi; cases hi; rw [← left,← right]; exact nat_of_bool_ (h_embed) _ _ _ _


theorem pts_at_tri_quad {l:ℕ} (k:Fin l) (ph : Vector Bool l) (fold : Vector (ℤ×ℤ) l):
pts_at_with      tri k ph fold ≤
pts_at_with quad k ph fold :=
pts_at_of_embeds embeds_tri_quad _ _ _


theorem pts_bound_of_embeds {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
{l:ℕ} (ph : Vector Bool l) (fold : Vector α l):
pts_tot go₀ ph fold ≤
pts_tot go₁ ph fold := by
  unfold pts_tot; apply List.Forall₂.sum_le_sum
  refine List.forall₂_iff_zip.mpr ?h.a; constructor; simp; intro a b hab
  let Q := List.get_of_mem hab; rcases Q with ⟨i,hi⟩; simp at hi
  cases hi; rw [← left,← right]; exact pts_at_of_embeds h_embed _ _ _

theorem pts_tri_quad {l:ℕ} (ph : Vector Bool l) (fold : Vector (ℤ×ℤ) l):
pts_tot  tri  ph fold ≤
pts_tot quad  ph fold :=
pts_bound_of_embeds embeds_tri_quad _ _

theorem pts_quad_hex {l:ℕ} (ph : Vector Bool l) (fold : Vector (ℤ×ℤ) l):
pts_tot quad ph fold ≤
pts_tot  hex ph fold :=
pts_bound_of_embeds embeds_quad_hex _ _

-- We now seek an upper bound for the objective function in protein folding.
-- We seek any bound, no matter how unsharp for now.
theorem List_sum_map_bound {α:Type} {l:ℕ} (f : (Fin l) → α) {F₀ : α → ℕ} {c:ℕ}
  (h : ∀ a,          F₀ a              ≤                                           c) :
  List.sum (List.map F₀ (List.ofFn f)) ≤ List.length (List.map F₀ (List.ofFn f)) * c
  := List.sum_le_card_nsmul _ _ (by {
      intro x hx
      simp at hx
      rw [List.mem_ofFn] at hx
      simp at hx
      rcases hx with ⟨y,hy⟩
      rw [← hy]
      exact h (f y)
    })


lemma quad_bound₀  {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α)
{l:ℕ} (ph : Vector Bool l) (fold : Vector α l) (i:Fin l):
pts_at_with go i ph fold ≤ i := by
  unfold pts_at_with
  let Q := List_sum_map_bound (
    fun i_1 : Fin i => point_achieved_with go fold ⟨i_1.1,finfin i_1⟩ i ph
  ) nat_of_bool_bound
  simp at Q
  simp
  exact Q


theorem quad_bound₂   {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α)
{l:ℕ} (ph : Vector Bool l) (fold : Vector α l):
pts_tot go ph fold ≤ l * l := by
  unfold pts_tot
  have hl: List.length (List.ofFn fun i => pts_at_with go i ph fold) = l
  := by
    let Q := List.length_ofFn (fun i => pts_at_with go i ph fold)
    exact Q
  have : (∀ x ∈ List.ofFn fun i => pts_at_with go i ph fold, x ≤ l)
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
    (List.ofFn fun i => pts_at_with go i ph fold)
  ) l this
  rw [hl] at Q
  exact Q


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

theorem path_len' {α: Type} [OfNat α 0] [DecidableEq α] {β: Type} [Fintype β]
(go: β → α → α) (l: ℕ) (moves: List β) (hm: moves.length = l)
: List.length (path go moves).1 = Nat.succ l
:= by
    rw [moves_len'_vec' go moves]
    simp
    exact hm

lemma property_of_morph   {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
(go₀ : Fin b₀ → α → α) (go₁ : Fin b₁ → α → α)
(g : is_embedding go₀ go₁ f)
(moves : List (Fin b₀)):
  (path go₀ moves).1 = (path go₁ (morph f go₀ moves)).1 := by
    induction moves
    unfold morph
    simp
    have : (path go₀ []).1 = [0] := rfl
    rw [this]
    have : (path go₁ []).1 = [0] := rfl
    . rw [this]
    rw [path_cons]
    let Q := g head (Vector.head (path go₀ tail))
    rw [Q]
    rw [tail_ih ]
    unfold morph
    simp
    rw [path_cons]
    simp
    have : (Vector.head (path go₀ tail))
    = (Vector.head (path go₁ (List.rec [] (fun head tail tail_ih => f head (Vector.head (path go₀ tail)) :: tail_ih) tail)))
    := by
      rw [two_heads (path go₀ tail) (path go₀ tail).1 (by
        have hn: (path go₀ tail).1 ≠ [] := by
          intro hc; apply congrArg List.length at hc; simp at hc
        exact hn
      ) rfl]
      simp_rw [tail_ih]
      rw [two_heads]
      unfold morph
      simp
    exact congrArg _ this


def path_transformed {α: Type} [OfNat α 0] [DecidableEq α] {b₀ b₁: ℕ}
(f: Fin b₀ → α → Fin b₁) (go₀: Fin b₀ → α → α) (go₁: Fin b₁ → α → α)
(l: List (Fin b₀)) : Vector α l.length.succ :=
  ⟨
    (path go₁ (morph f go₀ l)).1,
    by rw [path_len go₁ ⟨(morph f go₀ l),(morph_is_length_preserving f go₀ l)⟩]
  ⟩


-- Finished February 10, 2024:
theorem transform_of_embed  {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
(go₀ : Fin b₀ → α → α) (go₁ : Fin b₁ → α → α)
 (l : List (Fin b₀)) (h_embed: is_embedding go₀ go₁ f):
 path_transformed f go₀ go₁ l = path go₀ l
:= by
  apply SetCoe.ext; unfold path_transformed; simp; unfold is_embedding at h_embed; induction l; simp; unfold morph; simp
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


def pts_tot_bound   {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) (q : ℕ) :=
∀ moves : Vector β l,
pts_tot go ph (⟨(path go moves.1).1,path_len _ _⟩) ≤ q


instance    {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) (q : ℕ):
DecidablePred (pts_tot_bound go moves)
:= by
  unfold pts_tot_bound
  unfold pts_tot
  exact inferInstance

instance   {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α) : DecidablePred fun n => pts_tot_bound go ph n :=
  by
  unfold pts_tot_bound
  unfold pts_tot
  exact inferInstance

#eval pts_tot tri ⟨[false],rfl⟩ ⟨[(0,0)],rfl⟩ ≤ 5


theorem pts_tot_bound_exists {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β] (go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) :
∃ q, pts_tot_bound go ph q := by
  exists l.succ*l.succ;
  unfold pts_tot_bound
  intro moves
  let Q := quad_bound₂ go ph (⟨(path go moves.1).1,path_len _ _⟩)
  tauto


/- ph has to be of succ type because there will at least be an amino acid at the origin. -/

/- HP is the HP protein folding model "objective function" or "value function": -/
def HP  {α:Type} [OfNat α 0] [DecidableEq α] {β : Type} [Fintype β]
(go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) :ℕ := Nat.find (pts_tot_bound_exists go ph)

def P_tri'  {l:ℕ} := λ ph : Vector Bool l.succ ↦ HP tri ph
def P_quad' {l:ℕ} := λ ph : Vector Bool l.succ ↦ HP quad ph
def P_hex' {l:ℕ} := λ ph : Vector Bool l.succ ↦ HP hex ph

-- #eval P_tri' ⟨[false],rfl⟩
-- #synth Decidable (pts_tot_bound tri { val := [false], property := (_ : List.length [false] = List.length [false]) } 5)
-- #eval pts_tot_bound tri ⟨[false],rfl⟩ 5


theorem value_bound_of_embeds_strongly {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in_strongly go₀ go₁)
{l:ℕ} (ph : Vector Bool l.succ) : HP go₀ ph ≤ HP go₁ ph := by
  apply Nat.find_mono
  intro q hq moves
  let he := embeds_of_strongly_embeds h_embed
  let Q := pts_bound_of_embeds he ph (⟨(path go₀ moves.1).1,path_len _ _⟩)
  rcases h_embed with ⟨f,hf⟩
  let moves' := (
    ⟨
      morph f go₀ moves.1,
      (by rw [morph_is_length_preserving]; exact moves.2)
    ⟩ : Vector (Fin b₁) l)
  have : (path go₀ moves.1).1 = (path go₁ (morph f go₀ moves.1)).1 :=
    property_of_morph f go₀ go₁ hf moves.1
  calc
  _ ≤ pts_tot go₁ ph ⟨(path go₀  moves.1).1, path_len _ _⟩ := Q
  _ = pts_tot go₁ ph ⟨(path go₁ moves'.1).1, path_len _ _⟩ := by simp_rw [this]
  _ ≤ q                                                    := hq moves'

  -- The degree 3 "hexagonal lattice" protein folding model has an objective function
  -- P_tri that is bounded by that of the usual HP 2D model.

-- #eval HP quad ⟨[true,false,false,true],rfl⟩

theorem ptriquad' {l:ℕ} (ph : Vector Bool l.succ) : HP tri ph ≤ HP quad ph :=
value_bound_of_embeds_strongly embeds_strongly_tri_quad _

theorem pquadhex' {l:ℕ} (ph : Vector Bool l.succ) : HP quad ph ≤ HP hex ph :=
value_bound_of_embeds_strongly embeds_strongly_quad_hex _

def first_nonzero_entry (w : List (Fin 4)) : Option (Fin 4) := by {
  induction w
  .  exact none
  .  exact ite (tail_ih ≠ none) tail_ih (ite (head = 0) none head)
}

-- By symmetry we may assume that all walks (folds) are orderly, although that in itself could deserve a proof.
def orderly (w: List (Fin 4)) := w.reverse.getLast? = some (0:Fin 4)
      ∧ first_nonzero_entry w = some 2

instance (w : List (Fin 4)) : Decidable (orderly w) := by unfold orderly; exact And.decidable



def stecher (x : List Bool) (w: List (Fin 4)): ℕ := dite (w.length.succ = x.length)
    (λ h ↦ pts_tot
      quad
      (⟨x, rfl⟩ : Vector Bool x.length)
      ⟨(path quad w).1,(by rw [← h,path_len'];rfl)⟩
    )
    (λ _ ↦ 0)

def x : List Bool := [true,false,true,false,true,false, true,true]
#eval stecher x [0, 3, 1, 1, 2, 2, 0]
-- #eval stecher x [r2.D, r2.S, r2.A, r2.A, r2.W, r2.W, r2.D]
-- #eval stecher (x ++ [false]) [0, 3, 1, 1, 2, 2, 0].reverse


def stecher1 : Prop :=
  those_with_suffix'
    (λ w ↦ Function.Injective (λ i ↦ (path quad w).get i))
    (λ w ↦ stecher x w > 2 ∧ orderly w)
    (Gap_nil' 4 7)
  = {⟨[0, 3, 3, 1, 1, 2, 0],rfl⟩} --{⟨[0, 3, 1, 1, 2, 2, 0],rfl⟩}
instance : Decidable stecher1 := by {
  unfold stecher1
  apply decEq
}

-- #eval (myvec 4 7).length
-- #eval stecher1


def stecher2 : Prop :=
those_with_suffix'
    (λ w ↦ Function.Injective (λ i ↦ (path quad w).get i))
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

-- #eval stecher1
-- #eval stecher2
-- #eval stecher_conjecture_counterexample
