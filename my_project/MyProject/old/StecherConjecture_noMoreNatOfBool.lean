import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Data.Vector.Basic
import MyProject.MonoPred
import MyProject.BacktrackingVerification

set_option tactic.hygienic false
set_option maxHeartbeats 3000000

/-
A treatment of the hydrophobic-polar protein folding model in a generality
that covers rectangular, triangular and hexagonal lattices: P_rect, P_tri, P_hex.

We formalize the non-monotonicity of the objective function,
refuting an unpublished conjecture of Stecher.

We prove objective function bounds:
P_tri ≤ P_rect ≤ P_hex (using a theory of embeddings)
and for any model, P ≤ b * l and P ≤ l * l
where b is the number of moves and l is the word length.
-/

section Defining_the_protein_folding_moves

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
-- #eval move_hex 0 (0,0)
-- #eval move_hex 5 (1,0)

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

def go_WS : ℤ×ℤ → ℤ×ℤ := λ x ↦ ite (Even (x.1+x.2)) (sp x) (sm x)

def tri : Fin 3 → ℤ×ℤ → ℤ×ℤ
| 0 => go_D
| 1 => go_A
| 2 => go_WS

end Defining_the_protein_folding_moves


section Embedding_one_protein_folding_model_into_another

def embeds_in {α:Type} {b₀ b₁ : ℕ} (go₀ : Fin b₀ → α → α)
(go₁ : Fin b₁ → α → α) :=
∀ i : Fin b₀, ∀ x : α, ∃ j : Fin b₁, go₀ i x = go₁ j x

def is_embedding {α:Type} {b₀ b₁ : ℕ} (go₀ : Fin b₀ → α → α)
(go₁ : Fin b₁ → α → α) (f : Fin b₀ → α → Fin b₁) :=
∀ i : Fin b₀, ∀ x : α, go₀ i x = go₁ (f i x) x

def embeds_in_strongly {α:Type} {b₀ b₁ : ℕ} (go₀ : Fin b₀ → α → α)
(go₁ : Fin b₁ → α → α) :=
∃ f : Fin b₀ → α → Fin b₁, is_embedding go₀ go₁ f

theorem embeds_of_strongly_embeds {α:Type} {b₀ b₁ : ℕ} {go₀ : Fin b₀ → α → α}
{go₁ : Fin b₁ → α → α} (h_embed: embeds_in_strongly go₀ go₁):
embeds_in go₀ go₁ := by
  rcases h_embed with ⟨f,hf⟩; intro i x; exists f i x; exact hf i x

-- For tri we can only assert a pointwise version of embed_models:
/- It follows from tri_quad_embedding that any sequence of moves under tri generates a sequence in ℤ×ℤ
  that can also be generated using quad:
-/

def tri_quad_embedding : Fin 3 → ℤ×ℤ → Fin 4
| 0 => λ _ ↦ 0
| 1 => λ _ ↦ 1
| 2 => λ x ↦ ite (Even (x.1 + x.2)) 2 3
/-
This is almost an embedding of presented group actions
sending generators to generators, but not quite.
In fact, the map φ that transports a point vertically
across the triple point in the brick wall lattice
is not a translation! But there are two translations (up and down) such that
φ always agree with one or the other.

The map φ has order two and all its orbits have cardinality two.
-/

-- Using hex we have that each entry in quad is in hex:
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
    by_cases h: Even (x.1+x.2)-- "show" thanks to Johan Commelin
    show (if Even (x.1 + x.2) then sp x else sm x)  = quad (tri_quad_embedding 2 x) x
    rw [if_pos h];
    have : tri_quad_embedding 2 x = 2 := by
      show (if Even (x.1 + x.2) then 2 else 3) = 2; simp; tauto
    . rw [this]; rfl
    have : tri_quad_embedding 2 x = 3 := by
      show (if Even (x.1 + x.2) then 2 else 3) = 3; simp; tauto
    rw [this];
    show (if Even (x.1 + x.2) then sp x else sm x) = sm x
    . simp; tauto

end Embedding_one_protein_folding_model_into_another

section Left_and_right_injectivity

def left_injective {α:Type} {β : Type} [Fintype β] (go : β → α → α)
[DecidableEq α] := ∀ a, Function.Injective (λ b ↦ go b a)

def right_injective {α:Type} {β : Type} [Fintype β] (go : β → α → α)
[DecidableEq α] := ∀ b, Function.Injective (λ a ↦ go b a)

theorem left_injective_tri : left_injective tri := by
intro x a b hab; simp at hab; contrapose hab; unfold tri;
exact match a with
| 0 => match b with
  | 0 => by tauto
  | 1 => by
      conv => rhs;lhs;whnf
      conv => rhs;rhs;whnf
      simp
  | 2 => by
    show go_D x ≠ go_WS x;
    unfold go_D go_WS sp sm;
    by_cases h:(Even (x.1 + x.2)); rw [if_pos h]; simp; rw [if_neg h]; simp
| 1 => match b with
  | 0 => by
      conv => rhs;lhs;whnf
      conv => rhs;rhs;whnf
      simp
  | 1 => by tauto
  | 2 => by
    show go_A x ≠ go_WS x;
    unfold go_A go_WS sp sm;
    by_cases h:(Even (x.1 + x.2)); rw [if_pos h]; simp; rw [if_neg h]; simp
| 2 => match b with
  | 0 => by
    show go_WS x   ≠ go_D x; unfold go_WS go_D sp sm;
    by_cases h:(Even (x.1 + x.2)); rw [if_pos h]; simp; rw [if_neg h]; simp
  | 1 => by
    show go_WS x   ≠ go_A x; unfold go_WS go_A sm sp;
    by_cases h:(Even (x.1 + x.2)); rw [if_pos h]; simp; rw [if_neg h]; simp
  | 2 => by tauto

theorem left_injective_quad : left_injective quad := by
intro x a b hab; simp at hab; contrapose hab; unfold quad;
exact match a with
| 0 => by
  conv => rhs;lhs;whnf
  exact match b with
  | 0 => by tauto
  | 1 => by (conv => rhs;rhs;whnf); simp
  | 2 => by (conv => rhs;rhs;whnf); simp
  | 3 => by (conv => rhs;rhs;whnf); simp
| 1 => by
  conv => rhs;lhs;whnf
  exact match b with
  | 0 => by (conv => rhs;rhs;whnf); simp
  | 1 => by tauto
  | 2 => by (conv => rhs;rhs;whnf); simp
  | 3 => by (conv => rhs;rhs;whnf); simp
| 2 => by
  conv => rhs;lhs;whnf
  exact match b with
  | 0 => by (conv => rhs;rhs;whnf); simp
  | 1 => by (conv => rhs;rhs;whnf); simp
  | 2 => by tauto
  | 3 => by (conv => rhs;rhs;whnf); simp
| 3 => by
  conv => rhs;lhs;whnf
  exact match b with
  | 0 => by (conv => rhs;rhs;whnf); simp
  | 1 => by (conv => rhs;rhs;whnf); simp
  | 2 => by (conv => rhs;rhs;whnf); simp
  | 3 => by tauto

theorem right_injective_quad : right_injective quad := by
intro a; match a with
| 0 =>
  intro x y hxy; contrapose hxy;
  show go_D x ≠ go_D y; unfold go_D; simp; tauto
| 1 =>
  intro x y hxy; contrapose hxy;
  show go_A x ≠ go_A y; unfold go_A; simp; tauto
| 2 =>
  intro x y hxy; contrapose hxy;
  show sp x ≠ sp y; unfold sp; simp; tauto
| 3 =>
  intro x y hxy; contrapose hxy;
  show sm x ≠ sm y; unfold sm; simp; tauto
end Left_and_right_injectivity

section Setting_up_point_achieved
theorem finfin {l : ℕ} {k: Fin l} (i : Fin k): i.1 < l := calc
  _ < k.1 := i.isLt
  _ < l   := k.isLt

def nearby {α β : Type} [DecidableEq α] [Fintype β] (go : β → α → α)
(p q : α) : Bool := ∃ a : β, q = go a p

def point_achieved {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
 {l : ℕ} (fold : Vector α l) (i j : Fin l) (phobic : Vector Bool l) : Bool
:=  phobic.get i && phobic.get j && i.1.succ < j.1 && nearby go (fold.get i) (fold.get j)

def point_property {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
 {l : ℕ} (fold : Vector α l) (i j : Fin l) (phobic : Vector Bool l) (a:β)
:=
phobic.get i && phobic.get j && i.1.succ < j.1 && fold.get j = go a (fold.get i)


theorem characterize_point_achieved_existentially
 {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
 {l : ℕ} (fold : Vector α l.succ) (i j : Fin l.succ) (phobic : Vector Bool l.succ)
 : point_achieved go fold i j phobic
 ↔
∃ a, point_property go fold i j phobic a := by
  unfold point_property;
  constructor;intro h;unfold point_achieved at h;unfold nearby at h;simp at h
  rcases h.2 with ⟨a,ha⟩;exists a;simp;tauto;intro h;unfold point_achieved
  rcases h with ⟨a,ha⟩;unfold nearby;simp;simp at ha;constructor;tauto;exists a;tauto

-- Now we can use characterize_point_achieved_existentially with our ∃ a, ∃ i theorem.

def pts_at {α:Type} {β : Type} [Fintype β] (go : β → α → α)
[DecidableEq α] {l:ℕ} (k : Fin l) (ph : Vector Bool l) (fold : Vector α l) : ℕ :=
  Finset.card (
    Finset.filter (λ i : Fin k ↦ (point_achieved go fold ⟨i.1,finfin i⟩ k ph))
    Finset.univ
  )

def path_recursion {α β: Type} {tail_length: ℕ}
(go: β → α → α) (head: β) (tail_ih: Vector α (Nat.succ (tail_length)))
: Vector α (Nat.succ (tail_length.succ)) := ⟨(go head tail_ih.head) :: tail_ih.1, by simp⟩

/- Using OfNat here since ℤ×ℤ and ℤ×ℤ×ℤ that have a natural notion of base point or zero.-/
def path {α:Type} [OfNat α 0] {β : Type} (go : β → α → α) :
(moves : List β) → Vector α moves.length.succ
| [] => ⟨[0], rfl⟩
| head :: tail => path_recursion go head (path go tail)


end Setting_up_point_achieved


section Equivalent_existential_definitions_of_point_achieved


def choice_pack {β:Type} [Fintype β] {l : ℕ} (P : β → Fin l → Prop)
[DecidablePred fun a => ∃ i, P a i]
[DecidablePred fun i => ∃ a, P a i]
[∀ a, DecidablePred fun n => ∃ (hq : n < l), P a { val := n, isLt := hq }]
:
    (Finset.filter (λ a ↦ ∃ i, P a i) (Finset.univ : Finset β))
 →  (Finset.filter (λ i ↦ ∃ a, P a i) (Finset.univ : Finset (Fin l)))
:= by
  intro a; let a₂ := a.2; simp at a₂
  have h₀: ∃ (i : ℕ), ∃ (hi : i < l), P a ⟨i,hi⟩ := by
    rcases a₂ with ⟨i,hi⟩; exists i.1; exists i.2
  let i₁₁ := Nat.find h₀
  have i₁₂: i₁₁ < l := (Nat.find_spec h₀).1
  let i₁ := (⟨i₁₁,i₁₂⟩ : Fin l)
  have i₂: i₁ ∈ Finset.filter (fun i => ∃ a, P a i) Finset.univ := by
    simp; exists a; exact (Nat.find_spec h₀).2
  let i := (⟨i₁,i₂⟩ : { x // x ∈ Finset.filter (fun i => ∃ a, P a i) Finset.univ })
  exact i

lemma choice_pack_injective {β:Type} [Fintype β] {l : ℕ} {P : β → Fin l.succ → Prop}
[DecidablePred fun a => ∃ i, P a i]
[DecidablePred fun i => ∃ a, P a i]
[ (a : β) → DecidablePred fun n => ∃ (hq : n < l.succ), P a { val := n, isLt := hq }]
(h_unique_dir : ∀ i a₀ a₁, P a₀ i → P a₁ i → a₀ = a₁)
:
Function.Injective (choice_pack P) := by
  intro a b hab
  unfold choice_pack at hab
  simp at hab

  let a₂ := a.2; let b₂ := b.2
  simp at a₂; simp at b₂
  rw [Fin.exists_iff] at a₂
  rw [Fin.exists_iff] at b₂
  let ia := (⟨Nat.find a₂, (Nat.find_spec a₂).1⟩ : Fin l.succ)
  let ib := (⟨Nat.find b₂, (Nat.find_spec b₂).1⟩ : Fin l.succ)
  have : ia = ib := Fin.mk_eq_mk.mpr hab

  let hia := Nat.find_spec a₂
  let hib := Nat.find_spec b₂
  have hib₂: P b ib := hib.2

  rw [← this] at hib₂
  exact Subtype.ext (h_unique_dir ia a b hia.2 hib₂)

lemma apply_choice_pack {β:Type} [Fintype β] {l : ℕ} {P: β → Fin l → Prop}
[DecidablePred fun i => ∃ a, P a i] [DecidablePred fun a => ∃ i, P a i]
[(a : β) → DecidablePred fun n => ∃ (hq : n < l), P a { val := n, isLt := hq }]
{i: { x // x ∈ Finset.filter (fun i => ∃ a, P a i) Finset.univ }}
{a: β} (ha : P a i)
: P a ((
  choice_pack P ⟨
    a,
    (by simp; exists i : a ∈ Finset.filter (fun a : β => ∃ i : Fin l, P a i) Finset.univ)
  ⟩
) : Fin l)
:= by
    have witness:  ∃ j, ∃ (h : j < l), P a ⟨j,h⟩
      := by exists i; exists i.1.2;
    exact (Nat.find_spec witness).2

lemma choice_pack_surjective {β:Type} [Fintype β] {l : ℕ} {P : β → Fin l.succ → Prop}
[DecidablePred fun a => ∃ i, P a i]
[DecidablePred fun i => ∃ a, P a i]
[ (a : β) → DecidablePred fun n => ∃ (hq : n < l.succ), P a { val := n, isLt := hq }]
(h_unique_loc : ∀ a i₀ i₁, P a i₀ → P a i₁ → i₀ = i₁)
:
Function.Surjective (choice_pack P) := by
  intro i; let i₂ := i.2; simp at i₂;
  rcases i₂ with ⟨a,ha⟩
  exists ⟨a,by simp; exists i⟩
  let j := choice_pack P ⟨
    a,
    (by simp; exists i : a ∈ Finset.filter (fun a => ∃ i, P a i) Finset.univ)
  ⟩
  show j = i
  have : P a (choice_pack P ⟨a, (by simp; exists i)⟩) := apply_choice_pack ha
  let Q := h_unique_loc a i j ha this
  exact Subtype.ext Q.symm

lemma choice_pack_bijective {β:Type} [Fintype β] {l : ℕ} {P : β → Fin l.succ → Prop}
  [DecidablePred fun a => ∃ i, P a i]
  [DecidablePred fun i => ∃ a, P a i]
  [ (a : β) → DecidablePred fun n => ∃ (hq : n < l.succ), P a { val := n, isLt := hq }]
  (h_unique_loc : ∀ a i₀ i₁, P a i₀ → P a i₁ → i₀ = i₁)
  (h_unique_dir : ∀ i a₀ a₁, P a₀ i → P a₁ i → a₀ = a₁)
  : Function.Bijective (choice_pack P) := And.intro
    (choice_pack_injective  h_unique_dir)
    (choice_pack_surjective h_unique_loc)

lemma choice_pack_fintype_card {β:Type} [Fintype β] {l : ℕ} (P : β → Fin l.succ → Prop)
-- Completed Februaary 15, 2024
[DecidablePred fun a => ∃ i, P a i]
[DecidablePred fun i => ∃ a, P a i]
[(a : β) → DecidablePred fun n => ∃ (hq : n < l.succ), P a     ⟨n,hq⟩]
(h_unique_loc : ∀ a i₀ i₁, P a i₀ → P a i₁ → i₀ = i₁)
(h_unique_dir : ∀ i a₀ a₁, P a₀ i → P a₁ i → a₀ = a₁):
Fintype.card (Finset.filter (λ a ↦ ∃ i, P a i) (Finset.univ : Finset (β)))
=
Fintype.card (Finset.filter (λ i ↦ ∃ a, P a i) (Finset.univ : Finset (Fin l.succ)))
:= Fintype.card_of_bijective (choice_pack_bijective h_unique_loc h_unique_dir)

theorem choice_pack_finset_card {β:Type} [Fintype β] {l : ℕ} {P : β → Fin l.succ → Prop}
-- Completed February 16, 2024
[DecidablePred fun a => ∃ i, P a i]
[DecidablePred fun i => ∃ a, P a i]
[(a : β) → DecidablePred fun n => ∃ (hq : n < l.succ), P a     ⟨n,hq⟩]
(h_unique_loc : ∀ a i₀ i₁, P a i₀ → P a i₁ → i₀ = i₁)
(h_unique_dir : ∀ i a₀ a₁, P a₀ i → P a₁ i → a₀ = a₁):
Finset.card (Finset.filter (λ a ↦ ∃ i, P a i) Finset.univ) =
Finset.card (Finset.filter (λ i ↦ ∃ a, P a i) Finset.univ)
:= by
  repeat (rw [← Fintype.card_coe])
  exact choice_pack_fintype_card P h_unique_loc h_unique_dir
end Equivalent_existential_definitions_of_point_achieved

-- def QuadP {l:ℕ} (j : Fin l.succ) (moves: Vector (Fin 4) l) (ph : Vector Bool l.succ) : Fin 4 → Fin l.succ → Prop
--   := λ a i ↦
--   ph.get i ∧ ph.get j ∧ i.1.succ < j ∧ (path quad moves.1).get j = quad a ((path quad moves.1).get i)


-- theorem unique_loc_quad' {l:ℕ} (j: Fin l.succ)
--   (moves: Vector (Fin 4) l) (ph : Vector Bool l.succ)
--   (path_inj: Function.Injective (λ k : Fin l.succ ↦ (path quad moves.1).get k)):
--   ∀ (a : Fin 4) (i₀ i₁ : Fin l.succ) (_ : QuadP j moves ph a i₀) (_ : QuadP j moves ph a i₁),
--   i₀ = i₁
--   := λ a _ _ hai₀ hai₁ ↦ path_inj (right_injective_quad a (Eq.trans hai₀.2.2.2.symm hai₁.2.2.2))

-- theorem unique_dir_quad' {l:ℕ} (j: Fin l.succ)
--   (moves: Vector (Fin 4) l) (ph : Vector Bool l.succ):
--   ∀ (i : Fin l.succ) (a₀ a₁ : Fin 4)
--   (_ : QuadP j moves ph a₀ i)
--   (_ : QuadP j moves ph a₁ i),
--   a₀ = a₁
--   := λ i _ _ hai₀ hai₁ ↦ left_injective_quad ((path quad moves.1).get i) ((Eq.trans hai₀.2.2.2.symm hai₁.2.2.2))

-- theorem towards_unifying_linear_quadratic_bounds
-- {l:ℕ} (j: Fin l.succ) (moves: Vector (Fin 4) l) (ph : Vector Bool l.succ)
-- [DecidablePred fun a => ∃ i, QuadP j moves ph a i]
-- [DecidablePred fun i => ∃ a, QuadP j moves ph a i]
-- [(a : Fin 4) → DecidablePred fun n => ∃ (hq : n < Nat.succ l), QuadP j moves ph a { val := n, isLt := hq }]
-- (path_inj: Function.Injective (λ k : Fin l.succ ↦ (path quad moves.1).get k))
-- : Finset.card (Finset.filter (λ a ↦ ∃ i, QuadP j moves ph a i) Finset.univ) =
--   Finset.card (Finset.filter (λ i ↦ ∃ a, QuadP j moves ph a i) Finset.univ)
-- := choice_pack_finset_card (unique_loc_quad' j moves ph path_inj)
--                            (unique_dir_quad' j moves ph)
-- Next QuadP should be connected to the main definition.
-- def point_property {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
--  {l : ℕ} (fold : Vector α l) (i j : Fin l) (phobic : Vector Bool l) (a:β)
-- :=
-- phobic.get i && phobic.get j && i.1.succ < j.1 && fold.get j = go a (fold.get i)
-- the problem is point_property is in terms of fold instead of path go moves






section Main_theoretical_development

-- Extend a map on moves to lists:
def morph {α:Type} [OfNat α 0] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
(go₀ : Fin b₀ → α → α) (l : List (Fin b₀)) : List (Fin b₁) := by
induction l; exact []; exact (f head (path go₀ tail).head) :: tail_ih

-- morph is length-preserving:
theorem morph_len {α:Type} [OfNat α 0] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
(go₀ : Fin b₀ → α → α) (l : List (Fin b₀)) :
(morph f go₀ l).length = l.length := by
  induction l; unfold morph; rfl; unfold morph; repeat (rw [List.length_cons])
  simp; rw [← tail_ih]; congr

theorem nearby_of_embeds {α:Type} [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
 {x y : α} (hn : nearby go₀ x y):
nearby go₁ x y := by
  unfold nearby at hn; simp at hn; rcases hn with ⟨a,ha⟩; let Q := h_embed a x
  unfold nearby; simp; rw [ha]; tauto


theorem point_achieved_of_embeds
 {α:Type} [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
 {l:ℕ}
  (fold : Vector α l) (a b : Fin l) (phobic : Vector Bool l)
  (htri: point_achieved go₀ fold a b phobic) :
         point_achieved go₁ fold a b phobic := by
  unfold point_achieved
  unfold point_achieved at htri
  simp; simp at htri; constructor; tauto; exact nearby_of_embeds h_embed htri.2

theorem pts_at_of_embeds {α:Type} [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
{l:ℕ} (k:Fin l) (ph : Vector Bool l) (fold : Vector α l):
pts_at go₀ k ph fold ≤
pts_at go₁ k ph fold := by
  unfold pts_at;
  apply Finset.card_le_card
  intro a ha
  simp
  simp at ha
  exact point_achieved_of_embeds h_embed fold ⟨a,finfin a⟩ k ph ha

open BigOperators

def pts_tot {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
 {l:ℕ} (ph : Vector Bool l)(fold : Vector α l)
  := ∑ i : Fin l, pts_at go i ph (fold)

-- #eval ∑ i : Fin 5, i.1

theorem pts_bound_of_embeds {α:Type} [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
{l:ℕ} (ph : Vector Bool l) (fold : Vector α l):
pts_tot go₀ ph fold ≤
pts_tot go₁ ph fold := by
  unfold pts_tot;
  apply Finset.sum_le_sum;
  intros; exact pts_at_of_embeds h_embed _ _ _

-- We now seek an upper bound for the objective function in protein folding.
-- We seek any bound, no matter how unsharp for now.

lemma pts_at_bound {α:Type} [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α)
{l:ℕ} (ph : Vector Bool l) (fold : Vector α l) (i:Fin l):
pts_at go i ph fold ≤ i := by
  unfold pts_at
  simp_rw [← Finset.card_fin i.1]
  apply Finset.card_le_card
  apply Finset.filter_subset

theorem pts_achieved_bound {α:Type} [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α)
{l:ℕ} (ph : Vector Bool l.succ) (fold : Vector α l.succ):
pts_tot go ph fold ≤ ∑ j : Fin l.succ, j.1 := by
  unfold pts_tot
  apply Finset.sum_le_sum
  intro i; intro
  exact pts_at_bound go ph fold i -- So much easier! February 12

lemma Fin_sum_range (i : ℕ)  :
-- This can be used to get a better upper bound.
∑ j : Fin (i+1), j.1 = i.succ * i / 2
 := by
  let Q := Finset.sum_range_id i.succ
  simp at Q
  rw [← Q]
  exact (Finset.sum_range fun i => i).symm

theorem pts_achieved_quadratic_bound {α:Type} [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α)
{l:ℕ} (ph : Vector Bool l.succ) (fold : Vector α l.succ):
pts_tot go ph fold ≤ l.succ * l / 2 :=
/- For [true] the bound is 0 (which is sharp);
   for [true,true] the bound is 1 (not sharp as we're not using everything)-/
  calc
  _ ≤ ∑ j : Fin l.succ, j.1 := pts_achieved_bound _ _ _
  _ = _                     := Fin_sum_range _

lemma path_len {α: Type} [OfNat α 0] [DecidableEq α] {β: Type}
(go: β → α → α) {l: ℕ} (moves: Vector β l)
: (path go moves.1).1.length = l.succ
:= by rw [(path go moves.1).2]; simp

def pathVec {l:ℕ}{α:Type} [OfNat α 0] [DecidableEq α] {β : Type} (go : β → α → α)
(moves : Vector β l) : Vector α l.succ := ⟨(path go moves.1).1,path_len _ _⟩

def QuadPvec {l:ℕ} (j : Fin l.succ) (moves: Vector (Fin 4) l) (ph : Vector Bool l.succ) : Fin 4 → Fin l.succ → Prop
  := λ a i ↦
  ph.get i ∧ ph.get j ∧ i.1.succ < j ∧ (pathVec quad moves).get j = quad a ((pathVec quad moves).get i)

theorem point_achieved_iff_QuadP {l:ℕ} (j: Fin l.succ) (moves: Vector (Fin 4) l)
(ph : Vector Bool l.succ)
(i: Fin l.succ):
(∃ a, QuadPvec j moves ph a i)
↔
point_achieved quad (pathVec quad moves) i j ph
:= by
  rw [characterize_point_achieved_existentially]
  unfold point_property QuadPvec
  constructor
  intro h; rcases h with ⟨a,ha⟩; exists a; simp;       tauto
  intro h; rcases h with ⟨a,ha⟩; exists a; simp at ha; tauto
-- Now we need the unique_loc etc. for QuadPvec instead of QuadP
theorem unique_loc_quad {l:ℕ} (j: Fin l.succ)
  (moves: Vector (Fin 4) l) (ph : Vector Bool l.succ)
  (path_inj: Function.Injective (λ k : Fin l.succ ↦ (pathVec quad moves).get k)):
  ∀ (a : Fin 4) (i₀ i₁ : Fin l.succ) (_ : QuadPvec j moves ph a i₀) (_ : QuadPvec j moves ph a i₁),
  i₀ = i₁
  := λ a _ _ hai₀ hai₁ ↦ path_inj (right_injective_quad a (Eq.trans hai₀.2.2.2.symm hai₁.2.2.2))
theorem unique_dir_quad {l:ℕ} (j: Fin l.succ)
  (moves: Vector (Fin 4) l) (ph : Vector Bool l.succ):
  ∀ (i : Fin l.succ) (a₀ a₁ : Fin 4)
  (_ : QuadPvec j moves ph a₀ i)
  (_ : QuadPvec j moves ph a₁ i),
  a₀ = a₁
  := λ i _ _ hai₀ hai₁ ↦ left_injective_quad ((pathVec quad moves).get i) ((Eq.trans hai₀.2.2.2.symm hai₁.2.2.2))
theorem towards_unifying_linear_quadratic_boundsVec
{l:ℕ} (j: Fin l.succ) (moves: Vector (Fin 4) l) (ph : Vector Bool l.succ)
[DecidablePred fun a => ∃ i, QuadPvec j moves ph a i]
[DecidablePred fun i => ∃ a, QuadPvec j moves ph a i]
[(a : Fin 4) → DecidablePred fun n => ∃ (hq : n < Nat.succ l), QuadPvec j moves ph a { val := n, isLt := hq }]
(path_inj: Function.Injective (λ k : Fin l.succ ↦ (pathVec quad moves).get k))
: Finset.card (Finset.filter (λ a ↦ ∃ i, QuadPvec j moves ph a i) Finset.univ) =
  Finset.card (Finset.filter (λ i ↦ ∃ a, QuadPvec j moves ph a i) Finset.univ)
:= choice_pack_finset_card (unique_loc_quad j moves ph path_inj)
                           (unique_dir_quad j moves ph)


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
             ((go₀  head (path go₀ tail).head) :: (path go₀ tail).1) := rfl

theorem path_len' {α: Type} [OfNat α 0] [DecidableEq α] {β: Type}
(go: β → α → α) (l: ℕ) (moves: List β) (hm: moves.length = l)
: List.length (path go moves).1 = Nat.succ l
:= by rw [(path go moves).2,hm]

lemma path_nil {α:Type} [OfNat α 0] [DecidableEq α] {β:Type} [Fintype β]
(go : β → α → α):
(path go []).1 = [0] := rfl

def ne_nil_of_succ_length {α :Type} {k:ℕ}
(tail_ih: Vector α k.succ)
: tail_ih.1 ≠ [] := by
    have : tail_ih.1.length = k.succ := tail_ih.2
    intro hc; rw [hc] at this; contrapose this; simp

lemma path_eq_path_morph {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
(go₀ : Fin b₀ → α → α) (go₁ : Fin b₁ → α → α)
(g : is_embedding go₀ go₁ f)
(moves : List (Fin b₀)):
  (path go₀ moves).1 = (path go₁ (morph f go₀ moves)).1 := by
    induction moves
    . unfold morph; simp; repeat (rw [path_nil])
    rw [path_cons,g head (Vector.head (path go₀ tail)),tail_ih ]
    unfold morph; simp; rw [path_cons]; simp
    have : (Vector.head (path go₀ tail))
         = (Vector.head (path go₁ (List.rec [] (fun head tail tail_ih => f head (Vector.head (path go₀ tail)) :: tail_ih) tail)))
    := by
      rw [two_heads (path go₀ tail) (path go₀ tail).1 (ne_nil_of_succ_length _) rfl]
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
    by rw [path_len go₁ ⟨morph f go₀ l, morph_len f go₀ l⟩]
  ⟩


-- theorem coincide {l:ℕ} (k: Fin l.succ) (dir : Finset (ℤ×ℤ))
--   (ph : Vector Bool l.succ)
--   (moves : Vector (Fin 4) l)
--   -- need (ph : Vector Bool l.succ) for QuadP but not for pts_at !
--   (path_inj: Function.Injective (λ k : Fin l.succ ↦ (path quad moves.1).get k))
--    :
--   pts_at quad k ph ⟨(path quad moves.1).1,path_len' _ _ _ moves.2⟩
--   = pts_at_lin k dir ph ⟨(path quad moves.1).1,path_len' _ _ _ moves.2⟩

--   := by
--     unfold pts_at
--     unfold pts_at_lin
--     simp
--     let R := (unique_loc_quad' k moves ph path_inj)
--     let S := (unique_dir_quad' k moves ph)
--     let Q := choice_pack_finset_card 4 l (QuadP k moves ph) R S
--     unfold QuadP at Q
--     simp at Q
--     unfold point_achieved
--     simp
--     unfold nearby
--     -- rw [← Q]
--     -- apply Finset.card_congr
--     -- intro a ha
--     -- define a function f between the two finsets
--     sorry
/- same as Finset.card (
    Finset.filter (λ i : Fin k ↦ (point_achieved go fold ⟨i.1,finfin i⟩ k ph))
    Finset.univ
  )
  phobic.get a && phobic.get b && a.1.succ < b.1 && nearby go (fold.get a) (fold.get b)
  -/


/- Finished February 10, 2024:
When transforming, the underlying path in say ℤ×ℤ is unchanged.
-/
theorem transform_of_embed {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
(go₀ : Fin b₀ → α → α) (go₁ : Fin b₁ → α → α)
 (l : List (Fin b₀)) (h_embed: is_embedding go₀ go₁ f):
 path_transformed f go₀ go₁ l = path go₀ l
:= by
  apply SetCoe.ext; unfold path_transformed; simp; unfold is_embedding at h_embed; induction l; simp; unfold morph; simp
  . rfl
  have morph_cons : (morph f go₀ (head :: tail)) = (f head ((path go₀ tail).head)) :: (morph f go₀ (tail)) := rfl
  rw [morph_cons];
  repeat (rw [path_cons])
  simp
  constructor
  let a := (Vector.head (path go₀ tail))
  rw [h_embed head a]
  simp
  have : path go₁ (morph f go₀ tail)
     = ⟨(path go₀ tail).1,(by rw [morph_len]; exact (path go₀ tail).2)⟩
    := Vector.eq _ _ (by unfold Vector.toList; rw [← tail_ih])
  rw [this]
  have hau: ∃ a u, path go₀ tail = a ::ᵥ u := Vector.exists_eq_cons (path go₀ tail)
  have : Vector.head ⟨
        (path go₀ tail).1, ((by rw [morph_len]; exact (path go₀ tail).2)
        : (path go₀ tail).1.length = (morph f go₀ tail).length.succ
        )⟩ = Vector.head (path go₀ tail)
  := by
    rcases hau with ⟨a,ha⟩; rcases ha with ⟨u,hu⟩
    . rw [hu]; simp; rfl
  . exact congr_arg _ this
  . rw [tail_ih]


def pts_tot_bound {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) (q : ℕ) :=
∀ moves : Vector β l, List.Nodup (path go moves.1).1 →
pts_tot go ph (⟨(path go moves.1).1,path_len _ _⟩) ≤ q

instance {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) (q : ℕ):
DecidablePred (pts_tot_bound go moves)
:= by
  unfold pts_tot_bound
  unfold pts_tot
  exact inferInstance


instance {α:Type} [OfNat α 0] [DecidableEq α]
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
  exists  ∑ j : Fin (Nat.succ l), j.1
  unfold pts_tot_bound
  intro moves
  let Q := pts_achieved_bound go ph (⟨(path go moves.1).1,path_len _ _⟩)
  tauto


/- ph has to be of succ type because there will at least be an amino acid at the origin. -/

/- HP is the HP protein folding model "objective function" or "value function": -/

def HP {α:Type} [OfNat α 0] [DecidableEq α] {β : Type} [Fintype β]
(go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) :ℕ := Nat.find (pts_tot_bound_exists go ph)


def P_tri' {l:ℕ} := λ ph : Vector Bool l.succ ↦ HP tri ph
def P_quad' {l:ℕ} := λ ph : Vector Bool l.succ ↦ HP quad ph
def P_hex' {l:ℕ} := λ ph : Vector Bool l.succ ↦ HP hex ph

-- #eval P_tri' ⟨[false],rfl⟩
-- #synth Decidable (pts_tot_bound tri { val := [false], property := (_ : List.length [false] = List.length [false]) } 5)
-- #eval pts_tot_bound tri ⟨[false],rfl⟩ 5



/- Restructure this as value_bound_of_strong_embedding -/
theorem value_bound_of_embeds_strongly {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in_strongly go₀ go₁)
{l:ℕ} (ph : Vector Bool l.succ) : HP go₀ ph ≤ HP go₁ ph := by
  apply Nat.find_mono
  intro q hq moves h_inj
  let he := embeds_of_strongly_embeds h_embed
  let Q := pts_bound_of_embeds he ph (⟨(path go₀ moves.1).1,path_len _ _⟩)
  rcases h_embed with ⟨f,hf⟩
  let moves' := (
    ⟨
      morph f go₀ moves.1,
      (by rw [morph_len]; exact moves.2)
    ⟩ : Vector (Fin b₁) l)
  have h_inj':  List.Nodup (path go₁ moves'.1).1 := by
    let Q := transform_of_embed f go₀ go₁ (moves.1) hf
    unfold path_transformed at Q
    let R := congrArg (λ x ↦ x.1) Q
    simp at R
    rw [R]
    tauto
  have : (path go₀ moves.1).1 = (path go₁ (morph f go₀ moves.1)).1 :=
    path_eq_path_morph f go₀ go₁ hf moves.1
  calc
  _ ≤ pts_tot go₁ ph ⟨(path go₀  moves.1).1, path_len _ _⟩ := Q
  _ = pts_tot go₁ ph ⟨(path go₁ moves'.1).1, path_len _ _⟩ := by simp_rw [this]
  _ ≤ q                                                    := hq moves' h_inj'






#eval HP quad ⟨[true,false,false,true],rfl⟩

theorem embeds_strongly_tri_quad : embeds_in_strongly tri quad := by
  exists tri_quad_embedding
  exact tri_quad_embedding_is_embedding

theorem embeds_strongly_quad_hex : embeds_in_strongly quad hex := by
  exists quad_hex_embedding
  exact quad_hex_embedding_is_embedding

/- Here are some quotable results:
  The degree 3 "hexagonal lattice" protein folding model has an objective function
  P_tri that is bounded by that of the usual HP 2D model.
  Similarly for P_quad and P_hex.
-/

theorem HP_quad_bounds_tri {l:ℕ} (ph : Vector Bool l.succ) : HP tri ph ≤ HP quad ph :=
  value_bound_of_embeds_strongly embeds_strongly_tri_quad _
theorem HP_hex_bounds_quad {l:ℕ} (ph : Vector Bool l.succ) : HP quad ph ≤ HP hex ph :=
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
    (λ h ↦ pts_tot -- or pts_tot
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
instance : Decidable stecher_conjecture_counterexample := by
  unfold stecher_conjecture_counterexample; unfold stecher1; unfold stecher2; exact And.decidable

#eval stecher1
-- #eval stecher2
-- #eval stecher_conjecture_counterexample

end Main_theoretical_development

section Directional_approach

/- begin linear bound -/
def quad_dir : Finset (ℤ×ℤ) := {
  val := Multiset.ofList [(1,0),(-1,0),(0,1),(0,-1)]
  nodup := by decide
}

/- The following is a piece of the connection between two approaches: -/
theorem nearby_quad_dir (p q : ℤ×ℤ):
nearby quad p q ↔ ∃ v ∈ quad_dir, q = v + p := by
  constructor;intro h;unfold nearby at h;simp at h;unfold quad_dir;simp
  unfold quad at h;rcases h with ⟨a,ha⟩
  exact match a with
  |0=>by
    (conv at ha => lhs;whnf); conv at ha => rhs;whnf
    left;      simp at ha;rw [ha];apply Prod.ext;simp;ring;simp;
  |1=>by
    (conv at ha => lhs;whnf); conv at ha => rhs;whnf
    right;left;simp at ha;rw [ha];apply Prod.ext;simp;ring;simp;
  |2=>by
    (conv at ha => lhs;whnf); conv at ha => rhs;whnf
    right;right;left;simp at ha;rw [ha];apply Prod.ext;simp;ring_nf;simp;
  |3=>by
    (conv at ha => lhs;whnf); conv at ha => rhs;whnf
    right;right;right;simp at ha;rw [ha];apply Prod.ext;simp;ring_nf;simp;
  intro h;unfold nearby quad;simp;unfold quad_dir at h;cases h;cases h_1.1
  exists 0;(conv => rhs;whnf);rw [h_1.2];simp;apply Prod.ext;simp;ring;simp;ring_nf;cases a
  exists 1;(conv => rhs;whnf);rw [h_1.2];simp;apply Prod.ext;simp;ring;simp;ring_nf;cases a_1
  exists 2;(conv => rhs;whnf);rw [h_1.2];simp;apply Prod.ext;simp;ring_nf;simp;ring_nf;cases a
  exists 3;(conv => rhs;whnf);rw [h_1.2];simp;apply Prod.ext;simp;ring_nf;simp;ring_nf;cases a_1;

def tri_dir (x:ℤ×ℤ)  : Finset (ℤ×ℤ) := {
  val := Multiset.ofList [(1,0),(-1,0),ite (Even (x.1+x.2)) (0,1) (0,-1)]
  nodup := by by_cases h : (Even (x.1+x.2));rw [if_pos h];decide;rw [if_neg h];  decide
}

def pts_at_lin {l:ℕ} (k: Fin l) (dir : Finset (ℤ×ℤ))  (ph : Vector Bool l) (fold : Vector (ℤ×ℤ) l) : ℕ :=
Finset.card (
  Finset.filter (λ v ↦
    ∃ i, i.1.succ < k.1 ∧
    ph.get k
    ∧
    ph.get i ∧
    fold.get k + v = fold.get i
  ) dir
)

-- #eval pts_at_lin ⟨3,by simp⟩ quad_dir ⟨[true,false,false,true],rfl⟩ ⟨[(0,0),(1,0),(1,1),(1,0)],rfl⟩

/- This is now very easy: -/
lemma pts_at_bound_lin
{l:ℕ}  (dir : Finset (ℤ×ℤ)) (ph : Vector Bool l) (fold : Vector (ℤ×ℤ) l) (i:Fin l):
pts_at_lin i dir ph fold ≤ Finset.card dir := by
  unfold pts_at_lin
  apply Finset.card_le_card
  apply Finset.filter_subset

open BigOperators

-- pts_tot_lin is very similar to pts_tot.
def pts_tot_lin {l:ℕ} (dir : Finset (ℤ×ℤ)) (ph : Vector Bool l)(fold : Vector (ℤ×ℤ) l)
  := ∑ i : Fin l, pts_at_lin i dir ph fold

/- Here is our linear bound.
Make "directions" a parameter?
 -/
theorem pts_achieved_bound_lin
{l:ℕ} (dir : Finset (ℤ×ℤ)) (ph : Vector Bool l.succ) (fold : Vector (ℤ×ℤ) l.succ):
pts_tot_lin dir ph fold ≤ l.succ * Finset.card dir := by
-- note that to generalize we need λ x ↦ Finset.card (dir x) to be constant or something.
  suffices pts_tot_lin dir ph fold ≤
  ∑ j : Fin l.succ, Finset.card dir by
    simp at this; tauto
  unfold pts_tot_lin
  apply Finset.sum_le_sum
  intro i; intro
  exact pts_at_bound_lin dir ph fold i

end Directional_approach


section Some_unnecessary_group_computations

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

-- This group presentation is characterized by : abelian; three pairs of inverses; and DWZ=EAX=id?
-- Because given D and E,
-- W = (ZD).inv = D.inv Z.inv = D.inv E
-- A =                          D.inv
-- Z =                          E.inv
-- X = W.inv =                  E.inv D
-- and all powers D^m E^n are distinct.
-- So hex can be realized as quad with (1,-1) and (-1,1) added instead of the "Even" conditions.
-- This way P_{2D} ≤ P_{hex} can be proven "by inclusion".
-- Analogously for tri:
-- tri represents the degree-3 hexagonal/triangular lattice, although that in itself requires checking

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

end Some_unnecessary_group_computations

section Drafts

-- def Prop_quad (j : ℕ) (moves: Vector (Fin 4) l) : Fin 4 → Fin l.succ → Prop := λ a i ↦
--   i.1.succ < j ∧ quad a ((path quad moves.1).get i) = (path quad moves.1).get j
-- this should also talk about ph:


-- abbrev P (j : ℕ) (moves: Vector (Fin 4) l) := Prop_quad j moves


-- noncomputable instance  (j : ℕ) (moves: Vector (Fin 4) l) : DecidablePred fun a => ∃ i, P j moves a i := by
--   exact Classical.decPred fun a => ∃ i, P j moves a i
  -- unfold P Prop_quad
  -- unfold path quad
  -- apply?
  -- sorry

-- noncomputable instance  (j : ℕ) (moves: Vector (Fin 4) l) : DecidablePred fun i => ∃ a, P j moves a i :=
--   sorry

-- noncomputable instance  (j : ℕ) (moves: Vector (Fin 4) l) :
-- (i : Fin l) → DecidablePred fun n => ∃ (h  : n < 4), P j moves ⟨n,h⟩ i
-- := sorry

-- noncomputable instance  (j : ℕ) (moves: Vector (Fin 4) l) :
--   (a : Fin 4) → DecidablePred fun n => ∃ (hq : n < l.succ), P j moves a ⟨n,hq⟩
-- := sorry

-- theorem unique_loc_quad {l:ℕ} (j: Fin l)
--   (moves: Vector (Fin 4) l)
--   (path_inj: Function.Injective (λ k : Fin l.succ ↦ (path quad moves.1).get k)):
--   ∀ (a : Fin 4) (i₀ i₁ : Fin l.succ) (_ : Prop_quad j moves a i₀) (_ : Prop_quad j moves a i₁),
--   i₀ = i₁
--   := λ a _ _ hai₀ hai₁ ↦ path_inj (right_injective_quad a (Eq.trans hai₀.2 hai₁.2.symm))



-- theorem unique_dir_quad {l:ℕ} (j: Fin l)
--   (moves: Vector (Fin 4) l) :
--   ∀ (i : Fin l.succ) (a₀ a₁ : Fin 4)
--   (_ : Prop_quad j moves a₀ i)
--   (_ : Prop_quad j moves a₁ i),
--   a₀ = a₁
--   := λ i _ _ hai₀ hai₁ ↦ left_injective_quad ((path quad moves.1).get i) ((Eq.trans hai₀.2 hai₁.2.symm))



-- noncomputable instance {l:ℕ}  (k : Fin l.succ) (moves: Vector (Fin 4) l) (ph : Vector Bool l.succ):
--   DecidablePred fun a => ∃ i, QuadP k moves ph a i := sorry

-- noncomputable instance {l:ℕ}  (k : Fin l.succ) (moves: Vector (Fin 4) l) (ph : Vector Bool l.succ):
--   DecidablePred fun i => ∃ a, QuadP k moves ph a i := sorry

-- noncomputable instance {l:ℕ}  (k : Fin l.succ) (moves: Vector (Fin 4) l) (ph : Vector Bool l.succ):
--   (i : Fin l) → DecidablePred fun n => ∃ (h : n < 4), QuadP (↑k) moves ph { val := n, isLt := h } ↑↑i
-- := sorry

-- noncomputable instance {l:ℕ}  (k : Fin l.succ) (moves: Vector (Fin 4) l) (ph : Vector Bool l.succ):
-- (a : Fin 4) → DecidablePred fun n => ∃ (hq : n < Nat.succ l), QuadP (↑k) moves ph a { val := n, isLt := hq }
-- := sorry

end Drafts
