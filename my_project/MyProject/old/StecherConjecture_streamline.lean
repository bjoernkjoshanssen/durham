import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Data.Vector.Basic
import MyProject.MonoPred
import MyProject.BacktrackingVerification

set_option tactic.hygienic false
set_option maxHeartbeats 3000000
-- set_option maxRecDepth 10000
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

def rectMap (a : Fin 4) : ℤ×ℤ := match a with
  | 0 => (1,0)
  | 1 => (-1,0)
  | 2 => (0,1)
  | 3 => (0,-1)

def rect (a : Fin 4) (x: ℤ×ℤ) : ℤ×ℤ := x + rectMap a


-- move_hex represents the degree-6 hexagonal/triangular lattice, although that in itself requires checking.
-- This representation was designed to make the y-axis vertical to fit with a computer game.
-- def move_hex : Fin 6 → ℤ×ℤ → ℤ×ℤ
-- | 0 => go_D
-- | 1 => go_A
-- | 2 => go_X
-- | 3 => go_W
-- | 4 => go_E
-- | 5 => go_Z
-- #eval move_hex 0 (0,0)
-- #eval move_hex 5 (1,0)

-- If computer games are not to be used we can use a simpler implementation:
def hexMap (a : Fin 6) : ℤ×ℤ := match a with
  | 0 => (1,0)
  | 1 => (-1,0)
  | 2 => (0,1)
  | 3 => (0,-1)
  | 4 => (1,1)
  | 5 => (-1,-1)

def hex (a : Fin 6) (x: ℤ×ℤ) : ℤ×ℤ := x + hexMap a

theorem hexMap_injective : Function.Injective hexMap := by decide

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

infix:50 " ≼ " => embeds_in_strongly

theorem embeds_in_strongly_transitive {α:Type} {b₀ b₁ b₂: ℕ}
(go₀ : Fin b₀ → α → α)
(go₁ : Fin b₁ → α → α) (go₂ : Fin b₂ → α → α) :
go₀ ≼ go₁ → go₁ ≼ go₂ → go₀ ≼ go₂ := by
  intro h₀₁ h₁₂
  unfold embeds_in_strongly is_embedding at *
  rcases h₀₁ with ⟨f₀₁,hf₀₁⟩
  rcases h₁₂ with ⟨f₁₂,hf₁₂⟩
  exists (λ i x ↦ f₁₂ (f₀₁ i x) x)
  intro i x
  rw [hf₀₁,hf₁₂]

theorem embeds_in_strongly_reflexive {α:Type} {b: ℕ}
(go : Fin b → α → α)
: go ≼ go := by
  unfold embeds_in_strongly is_embedding at *
  exists (λ i _ ↦ i)
  intro i x
  simp

theorem embeds_of_strongly_embeds {α:Type} {b₀ b₁ : ℕ} {go₀ : Fin b₀ → α → α}
{go₁ : Fin b₁ → α → α} (h_embed: go₀ ≼ go₁):
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

3n      4n        6n    n(n-1)/2
P_tri   P_rect    P_hex
-/

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
  ∀ i : Fin 4, ∀ x : ℤ×ℤ, rect i x = hex (quad_hex_embedding i x) x
  | 0 => λ _ ↦ rfl
  | 1 => λ _ ↦ rfl
  | 2 => λ _ ↦ rfl
  | 3 => λ _ ↦ rfl


theorem tri_quad_embedding_is_embedding :
  ∀ i : Fin 3, ∀ x : ℤ×ℤ, tri i x = rect (tri_quad_embedding i x) x
  | 0 => λ x ↦ rfl
  | 1 => λ x ↦ rfl
  | 2 => λ x ↦ by
    by_cases h: Even (x.1+x.2)-- "show" thanks to Johan Commelin
    show (if Even (x.1 + x.2) then sp x else sm x)  = rect (tri_quad_embedding 2 x) x
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

def left_injective {α:Type} {β γ: Type} [Fintype β] (go : β → α → γ)
[DecidableEq α] := ∀ a, Function.Injective (λ b ↦ go b a)

def right_injective {α:Type} {β γ: Type} [Fintype β] (go : β → α → γ)
[DecidableEq α] := ∀ b, Function.Injective (λ a ↦ go b a)


theorem tri_quad_embedding_left_injective :
left_injective tri_quad_embedding := by
  unfold left_injective at *
  intro x
  intro a b hab
  simp at *
  unfold tri_quad_embedding at *
  contrapose hab

  match a with
  | 0 => match b with
    | 0 => tauto
    | 1 => (conv => right;left;whnf);(conv => right;right;whnf);simp
    | 2 =>
      conv => right;left;whnf;
      have : (match (motive := Fin 3 → ℤ × ℤ → Fin 4) 2 with
      | 0 => fun _ => 0
      | 1 => fun _ => 1
      | 2 => fun x => if Even (x.1 + x.2) then (2:Fin 4) else 3)
        = fun x : ℤ×ℤ => if Even (x.1 + x.2) then (2:Fin 4) else 3
         := rfl
      rw [this];simp
      by_cases h : Even (x.1+x.2)
      rw [if_pos h];intro hc
      let Q := congr_arg (λ x ↦ x.1) hc;simp at Q
      rw [if_neg h];intro hc
      let Q := congr_arg (λ x ↦ x.1) hc;simp at Q;tauto
  | 1 => match b with
    | 1 => tauto
    | 0 => (conv => right;left;whnf);(conv => right;right;whnf);simp
    | 2 =>
      conv => right;left;whnf;
      have : (match (motive := Fin 3 → ℤ × ℤ → Fin 4) 2 with
      | 0 => fun _ => 0
      | 1 => fun _ => 1
      | 2 => fun x => if Even (x.1 + x.2) then (2:Fin 4) else 3)
        = fun x : ℤ×ℤ => if Even (x.1 + x.2) then (2:Fin 4) else 3
         := rfl
      rw [this];simp
      by_cases h : Even (x.1+x.2)
      rw [if_pos h];intro hc
      let Q := congr_arg (λ x ↦ x.1) hc;simp at Q
      rw [if_neg h];intro hc
      let Q := congr_arg (λ x ↦ x.1) hc;
      simp at Q;
      ring_nf at Q
      apply Nat.succ_injective at Q
      tauto

  | 2 => match b with
    | 1 =>
      conv => right;right;whnf;
      have : (match (motive := Fin 3 → ℤ × ℤ → Fin 4) 2 with
      | 0 => fun _ => 0
      | 1 => fun _ => 1
      | 2 => fun x => if Even (x.1 + x.2) then (2:Fin 4) else 3)
        = fun x : ℤ×ℤ => if Even (x.1 + x.2) then (2:Fin 4) else 3
         := rfl
      rw [this];simp
      by_cases h : Even (x.1+x.2)
      rw [if_pos h];intro hc
      let Q := congr_arg (λ x ↦ x.1) hc;simp at Q
      rw [if_neg h];intro hc
      let Q := congr_arg (λ x ↦ x.1) hc;
      simp at Q;
      ring_nf at Q
      apply Nat.succ_injective at Q
      tauto

    | 0 =>
      conv => right;right;whnf;
      have : (match (motive := Fin 3 → ℤ × ℤ → Fin 4) 2 with
      | 0 => fun _ => 0
      | 1 => fun _ => 1
      | 2 => fun x => if Even (x.1 + x.2) then (2:Fin 4) else 3)
        = fun x : ℤ×ℤ => if Even (x.1 + x.2) then (2:Fin 4) else 3
         := rfl
      rw [this];simp
      by_cases h : Even (x.1+x.2)
      rw [if_pos h];intro hc
      let Q := congr_arg (λ x ↦ x.1) hc;simp at Q
      rw [if_neg h];intro hc
      let Q := congr_arg (λ x ↦ x.1) hc;
      simp at Q;
      ring_nf at Q
      tauto
    | 2 => tauto

theorem sp_injective : Function.Injective sp := by
  intro x y hxy
  unfold sp at *
  simp at hxy;tauto

theorem sm_injective : Function.Injective sm := by
  intro x y hxy
  unfold sm at *
  simp at hxy;tauto


theorem go_WS_injective : Function.Injective go_WS := by
  intro x y hxy
  unfold go_WS at *
  by_cases hx : Even (x.1 + x.2)
  rw [if_pos hx] at hxy
  by_cases hy : Even (y.1 + y.2)
  rw [if_pos hy] at hxy
  . exact sp_injective hxy
  rw [if_neg hy] at hxy
  unfold sp sm at hxy
  let Q₁ := congr_arg (λ x ↦ x.1) hxy
  simp at Q₁
  let Q₂ := congr_arg (λ x ↦ x.2) hxy
  simp at Q₂
  rw [← Q₁] at hy
  let T := congr_arg (λ x ↦ x + 1) Q₂
  simp at T
  have : x.2 + 2 = y.2 := by
    rw [← T]
    ring
  rw [← this] at hy
  rw [← add_assoc] at hy
  rcases hx with ⟨k,hk⟩
  rw [hk] at hy
  contrapose hy
  simp
  exists (k+1)
  ring
  rw [if_neg hx] at hxy
  by_cases hy : Even (y.1 + y.2)
  rw [if_pos hy] at hxy
  unfold sm sp at *

  let Q₁ := congr_arg (λ x ↦ x.1) hxy
  simp at Q₁
  let Q₂ := congr_arg (λ x ↦ x.2) hxy
  simp at Q₂
  rw [← Q₁] at hy
  let T := congr_arg (λ x ↦ x + 1) Q₂
  simp at T
  have : x.2 = y.2 + 2 := by
    rw [T]
    ring
  rw [this] at hx
  rw [← add_assoc] at hx
  rcases hy with ⟨k,hk⟩
  rw [hk] at hx
  contrapose hx
  simp
  exists (k+1)
  ring

  rw [if_neg hy] at hxy
  exact sm_injective hxy


theorem right_injective_tri : right_injective tri := by
  unfold tri
  intro a; match a with
  | 0 => exact add_left_injective _
  | 1 => exact add_left_injective _
  | 2 =>
    intro x y hxy;
    contrapose hxy
    show ¬ go_WS x = go_WS y
    contrapose hxy
    simp at *
    exact go_WS_injective hxy

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



theorem rectMap_injective : Function.Injective rectMap := by
  decide

theorem left_injective_hex : left_injective hex := by
  unfold left_injective
  intro a
  unfold hex
  intro x y hxy
  simp at hxy
  exact hexMap_injective hxy


theorem left_injective_quad : left_injective rect := by
  unfold left_injective
  intro a
  unfold rect
  intro x y hxy
  simp at hxy
  exact rectMap_injective hxy


theorem right_injective_quad : right_injective rect := by
  unfold rect
  intro a; match a with
  | 0 => exact add_left_injective _
  | 1 => exact add_left_injective _
  | 2 => exact add_left_injective _
  | 3 => exact add_left_injective _

theorem right_injective_hex : right_injective hex := by
  intro a;
  match a with
  | 0 => exact add_left_injective _
  | 1 => exact add_left_injective _
  | 2 => exact add_left_injective _
  | 3 => exact add_left_injective _
  | 4 => exact add_left_injective _
  | 5 => exact add_left_injective _

end Left_and_right_injectivity

section Setting_up_point_earned
theorem finfin {l : ℕ} {k: Fin l} (i : Fin k): i.1 < l := calc
  _ < k.1 := i.isLt
  _ < l   := k.isLt

def nearby {α β : Type} [DecidableEq α] [Fintype β] (go : β → α → α)
(p q : α) : Bool := ∃ a : β, q = go a p

def pt_loc {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
 {l : ℕ} (fold : Vector α l) (i j : Fin l) (phobic : Vector Bool l) : Bool
:=  phobic.get i && phobic.get j && i.1.succ < j.1 && nearby go (fold.get i) (fold.get j)

def pts_at' {α:Type} {β : Type} [Fintype β] (go : β → α → α)
[DecidableEq α] {l:ℕ} (k : Fin l) (ph : Vector Bool l) (fold : Vector α l) : ℕ :=
  Finset.card (
    Finset.filter (λ i : Fin l ↦ (pt_loc go fold i k ph))
    Finset.univ
  )
/-
  We prove that pts_at  = pts_at'.
  pts_at' is more convenient type-theoretically, but
  pts_at is more useful for proving a certain bound.
-/
def change_type  {α:Type} {β : Type} [Fintype β] (go : β → α → α)
[DecidableEq α] {l:ℕ} (k : Fin l) (ph : Vector Bool l) (fold : Vector α l):
Finset.filter (λ i : Fin l ↦ (pt_loc go fold i k ph)) Finset.univ
→
Finset.filter (λ i : Fin k ↦ (pt_loc go fold ⟨i.1,finfin i⟩ k ph)) Finset.univ
  := by
    intro ip; let Q := ip.2; rw [Finset.mem_filter] at Q -- Finset.mem_filter was key here
    unfold pt_loc at Q;
    have : ip.1.1.succ < k := by
      simp at Q;tauto
    exact ⟨⟨ip.1.1,Nat.lt_of_succ_lt this⟩,by rw [Finset.mem_filter];simp;tauto⟩


theorem change_type_card  {α:Type} {β : Type} [Fintype β] (go : β → α → α)
[DecidableEq α] {l:ℕ} (k : Fin l) (ph : Vector Bool l) (fold : Vector α l):
Fintype.card (Finset.filter (λ i : Fin l ↦ (pt_loc go fold i k ph)) Finset.univ)
=
Fintype.card (Finset.filter (λ i : Fin k ↦ (pt_loc go fold ⟨i.1,finfin i⟩ k ph)) Finset.univ)
:= by
  suffices Function.Bijective (change_type go k ph fold) by
    apply Fintype.card_of_bijective; exact this
  constructor
  intro i₁ i₂ hi; unfold change_type at hi; simp at hi
  exact SetCoe.ext (Fin.ext hi)
  intro i; let Q := i.2; rw [Finset.mem_filter] at Q
  exists ⟨
    ⟨i.1,finfin i.1⟩,
    by rw [Finset.mem_filter]; constructor; simp; exact Q.2
  ⟩



def path_aux {α β: Type} {l: ℕ}
(go: β → α → α) (hd: β)
(tl: Vector α l.succ)
   : Vector α l.succ.succ := ⟨(go hd tl.head) :: tl.1, by simp⟩

def path_aux_list {α β: Type}
(go: β → α → α) (hd: β)
(tl: List α) (h : tl ≠ [])
   : List α := (go hd (tl.head h)) :: tl


def path_at {α:Type} {β : Type} (base:α) (go : β → α → α) :
(moves : List β) → Vector α moves.length.succ
| [] => ⟨[base], rfl⟩
| head :: tail => path_aux go head (path_at base go tail)


-- def path_at_list {α:Type} {β : Type} (base:α) (go : β → α → α) :
-- (moves : List β) → List α
-- | [] => [base]
-- | head :: tail => path_aux_list go head (path_at_list base go tail) (by

--   sorry
-- )

/- Using OfNat here since ℤ×ℤ and ℤ×ℤ×ℤ have a natural notion of base point or zero.-/
def path {α:Type} [OfNat α 0] {β : Type} (go : β → α → α) :
  (moves : List β) → Vector α moves.length.succ
  := path_at 0 go

end Setting_up_point_earned

section Equivalent_existential_definitions_of_point_earned


def choice_ex {β:Type} [Fintype β] {l : ℕ} (P : β → Fin l → Prop)
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

lemma choice_ex_injective {β:Type} [Fintype β] {l : ℕ} {P : β → Fin l.succ → Prop}
[DecidablePred fun a => ∃ i, P a i]
[DecidablePred fun i => ∃ a, P a i]
[ (a : β) → DecidablePred fun n => ∃ (hq : n < l.succ), P a { val := n, isLt := hq }]
(h_unique_dir : ∀ i a₀ a₁, P a₀ i → P a₁ i → a₀ = a₁)
:
Function.Injective (choice_ex P) := by
  intro a b hab
  unfold choice_ex at hab
  simp at hab

  let a₂ := a.2; let b₂ := b.2
  simp at a₂ b₂
  rw [Fin.exists_iff] at a₂ b₂
  let ia := (⟨Nat.find a₂, (Nat.find_spec a₂).1⟩ : Fin l.succ)
  let ib := (⟨Nat.find b₂, (Nat.find_spec b₂).1⟩ : Fin l.succ)
  have : ia = ib := Fin.mk_eq_mk.mpr hab

  let hia := Nat.find_spec a₂
  let hib := Nat.find_spec b₂
  have hib₂: P b ib := hib.2

  rw [← this] at hib₂
  exact Subtype.ext (h_unique_dir ia a b hia.2 hib₂)

lemma choice_ex_aux {β:Type} [Fintype β] {l : ℕ} {P: β → Fin l → Prop}
[DecidablePred fun i => ∃ a, P a i] [DecidablePred fun a => ∃ i, P a i]
[(a : β) → DecidablePred fun n => ∃ (hq : n < l), P a { val := n, isLt := hq }]
{i: { x // x ∈ Finset.filter (fun i => ∃ a, P a i) Finset.univ }}
{a: β} (ha : P a i)
:            P a ((choice_ex P ⟨a, (by simp; exists i)⟩) : Fin l)
:= by
    have witness:  ∃ j, ∃ (h : j < l), P a ⟨j,h⟩
      := by exists i; exists i.1.2;
    exact (Nat.find_spec witness).2

lemma choice_ex_surjective {β:Type} [Fintype β] {l : ℕ} {P : β → Fin l.succ → Prop}
[DecidablePred fun a => ∃ i, P a i]
[DecidablePred fun i => ∃ a, P a i]
[ (a : β) → DecidablePred fun n => ∃ (hq : n < l.succ), P a { val := n, isLt := hq }]
(h_unique_loc : ∀ a i₀ i₁, P a i₀ → P a i₁ → i₀ = i₁)
:
Function.Surjective (choice_ex P) := by
  intro i; let i₂ := i.2; simp at i₂;
  rcases i₂ with ⟨a,ha⟩
  exists ⟨a,by simp; exists i⟩
  let j := choice_ex P ⟨
    a,
    (by simp; exists i : a ∈ Finset.filter (fun a => ∃ i, P a i) Finset.univ)
  ⟩
  show j = i
  have : P a (choice_ex P ⟨a, (by simp; exists i)⟩) := choice_ex_aux ha
  let Q := h_unique_loc a i j ha this
  exact Subtype.ext Q.symm

lemma choice_ex_bijective {β:Type} [Fintype β] {l : ℕ} {P : β → Fin l.succ → Prop}
  [DecidablePred fun a => ∃ i, P a i]
  [DecidablePred fun i => ∃ a, P a i]
  [ (a : β) → DecidablePred fun n => ∃ (hq : n < l.succ), P a { val := n, isLt := hq }]
  (h_unique_loc : ∀ a i₀ i₁, P a i₀ → P a i₁ → i₀ = i₁)
  (h_unique_dir : ∀ i a₀ a₁, P a₀ i → P a₁ i → a₀ = a₁)
  : Function.Bijective (choice_ex P) := And.intro
    (choice_ex_injective  h_unique_dir)
    (choice_ex_surjective h_unique_loc)

theorem choice_ex_finset_card {β:Type} [Fintype β] {l : ℕ} {P : β → Fin l.succ → Prop}
-- Completed February 16, 2024
[DecidablePred fun a => ∃ i, P a i]
[DecidablePred fun i => ∃ a, P a i]
[(a : β) → DecidablePred fun n => ∃ (hq : n < l.succ), P a     ⟨n,hq⟩]
(h_unique_loc_dir : (∀ a i₀ i₁, P a i₀ → P a i₁ → i₀ = i₁) ∧ ∀ i a₀ a₁, P a₀ i → P a₁ i → a₀ = a₁):
Finset.card (Finset.filter (λ a ↦ ∃ i, P a i) Finset.univ) =
Finset.card (Finset.filter (λ i ↦ ∃ a, P a i) Finset.univ)
:= by
  suffices Fintype.card (Finset.filter (λ a ↦ ∃ i, P a i) (Finset.univ : Finset (β))) =
           Fintype.card (Finset.filter (λ i ↦ ∃ a, P a i) (Finset.univ : Finset (Fin l.succ))) by
    repeat (rw [← Fintype.card_coe])
    exact this
  exact Fintype.card_of_bijective (choice_ex_bijective h_unique_loc_dir.1 h_unique_loc_dir.2)
end Equivalent_existential_definitions_of_point_earned

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


theorem pt_loc_of_embeds
 {α:Type} [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
 {l:ℕ}
  (fold : Vector α l) (a b : Fin l) (phobic : Vector Bool l)
  (htri: pt_loc go₀ fold a b phobic) :
         pt_loc go₁ fold a b phobic := by
  unfold pt_loc at *; simp at *; constructor; tauto; exact nearby_of_embeds h_embed htri.2


theorem pts_at_of_embeds' {α:Type} [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
{l:ℕ} (k:Fin l) (ph : Vector Bool l) (fold : Vector α l):
pts_at' go₀ k ph fold ≤
pts_at' go₁ k ph fold := by
  unfold pts_at'; apply Finset.card_le_card; intro a ha; simp; simp at ha
  exact pt_loc_of_embeds h_embed fold a k ph ha

open BigOperators


def pts_tot' {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
 {l:ℕ} (ph : Vector Bool l)(fold : Vector α l)
  := ∑ i : Fin l, pts_at' go i ph (fold)

def pts_tot {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
 {l:ℕ} (ph : Vector Bool l)(fold : Vector α l)
  := ∑ i : {i₀ : Fin l // ph.get i₀}, pts_at' go i ph (fold)


theorem pts_bound_of_embeds {α:Type} [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
{l:ℕ} (ph : Vector Bool l) (fold : Vector α l):
pts_tot go₀ ph fold ≤
pts_tot go₁ ph fold := by
  unfold pts_tot; apply Finset.sum_le_sum; intros; exact pts_at_of_embeds' h_embed _ _ _


theorem pts_bound_of_embeds' {α:Type} [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
{l:ℕ} (ph : Vector Bool l) (fold : Vector α l):
pts_tot' go₀ ph fold ≤
pts_tot' go₁ ph fold := by
  unfold pts_tot'; apply Finset.sum_le_sum; intros; exact pts_at_of_embeds' h_embed _ _ _


-- We now seek an upper bound for the objective function in protein folding.

def pts_at {α:Type} {β : Type} [Fintype β] (go : β → α → α)
[DecidableEq α] {l:ℕ} (k : Fin l) (ph : Vector Bool l) (fold : Vector α l) : ℕ :=
  Finset.card (
    Finset.filter (λ i : Fin k ↦ (pt_loc go fold ⟨i.1,finfin i⟩ k ph))
    Finset.univ
  )

theorem pts_at_eq_pts_at'  {α:Type} {β : Type} [Fintype β] (go : β → α → α)
[DecidableEq α] {l:ℕ} (k : Fin l) (ph : Vector Bool l) (fold : Vector α l):
pts_at go k ph fold = pts_at' go k ph fold :=
by unfold pts_at pts_at'; (repeat rw [← Fintype.card_coe]); exact (change_type_card go k ph fold).symm

lemma pts_at_bound' {α:Type} [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α)
{l:ℕ} (ph : Vector Bool l) (fold : Vector α l) (i:Fin l):
pts_at' go i ph fold ≤ i := by
  rw [← pts_at_eq_pts_at', ← Finset.card_fin i.1]; apply Finset.card_le_card; apply Finset.filter_subset

lemma Fin_sum_range (i : ℕ)  :
∑ j : Fin (i+1), j.1 = i.succ * i / 2
 := by let Q := Finset.sum_range_id i.succ; simp at Q; rw [← Q]; exact (Finset.sum_range fun i => i).symm



theorem pts_earned_bound_loc' {α:Type} [DecidableEq α] {β : Type} [Fintype β] (go : β → α → α)
{l:ℕ} (ph : Vector Bool l.succ) (fold : Vector α l.succ):
pts_tot' go ph fold ≤ l.succ * l / 2 := by
  suffices pts_tot' go ph fold ≤ ∑ j : Fin l.succ, j.1 by calc
    _ ≤ ∑ j : Fin l.succ, j.1 := this
    _ = _                     := Fin_sum_range _
  unfold pts_tot'; apply Finset.sum_le_sum; intro i; intro; exact pts_at_bound' go ph fold i


lemma path_len {α: Type} [OfNat α 0] [DecidableEq α] {β: Type}
(go: β → α → α) {l: ℕ} (moves: Vector β l)
: (path go moves.1).1.length = l.succ
:= by rw [(path go moves.1).2]; simp

lemma path_at_len {α: Type} (base :α) [DecidableEq α] {β: Type}
(go: β → α → α) {l: ℕ} (moves: Vector β l)
: (path_at base go moves.1).1.length = l.succ
:= by rw [(path_at base go moves.1).2]; simp


def pathVec {l:ℕ}{α:Type} [OfNat α 0] [DecidableEq α] {β : Type} (go : β → α → α)
(moves : Vector β l) : Vector α l.succ := ⟨(path go moves.1).1,path_len _ _⟩

def pathVec_at {l:ℕ}{α:Type} (base : α) [DecidableEq α] {β : Type} (go : β → α → α)
(moves : Vector β l) : Vector α l.succ := ⟨(path_at base go moves.1).1,path_at_len _ _ _⟩


def pt_dir {α:Type} [OfNat α 0] [DecidableEq α] {β : Type} (go : β → α → α)
 {l:ℕ} (j : Fin l.succ) (moves: Vector β l) (ph : Vector Bool l.succ)
: β → Fin l.succ → Prop  := λ a i ↦
  ph.get i ∧ ph.get j ∧ i.1.succ < j ∧ (pathVec go moves).get j = go a ((pathVec go moves).get i)


theorem unique_loc  {α: Type} [OfNat α 0] [DecidableEq α] {β: Type} [Fintype β]
(go: β → α → α)
 {l:ℕ} (j: Fin l.succ)
  (moves: Vector β l) (ph : Vector Bool l.succ)
  (path_inj: Function.Injective (λ k : Fin l.succ ↦ (pathVec go moves).get k))
  (right_inj: right_injective go)
  :
  ∀ (a : β) (i₀ i₁ : Fin l.succ) (_ : pt_dir go j moves ph a i₀) (_ : pt_dir go j moves ph a i₁),
  i₀ = i₁
  := λ a _ _ hai₀ hai₁ ↦ path_inj (right_inj a (Eq.trans hai₀.2.2.2.symm hai₁.2.2.2))

theorem unique_dir {α: Type} [OfNat α 0] [DecidableEq α] {β: Type} [Fintype β]
(go: β → α → α) {l:ℕ} (j: Fin l.succ)
  (moves: Vector β l) (ph : Vector Bool l.succ)
  (left_inj : left_injective go)
  :
  ∀ (i : Fin l.succ) (a₀ a₁ : β)
  (_ : pt_dir go j moves ph a₀ i)
  (_ : pt_dir go j moves ph a₁ i),
  a₀ = a₁
  := λ i _ _ hai₀ hai₁ ↦ left_inj ((pathVec go moves).get i) ((Eq.trans hai₀.2.2.2.symm hai₁.2.2.2))

theorem unique_loc_dir {α: Type} [OfNat α 0] [DecidableEq α] {β: Type} [Fintype β]
{go: β → α → α} {l:ℕ} {j: Fin l.succ}
  {moves: Vector β l} {ph : Vector Bool l.succ}
  (path_inj: Function.Injective (λ k : Fin l.succ ↦ (pathVec go moves).get k))
  (right_inj: right_injective go)
  (left_inj : left_injective go)
  :
  (∀ (a : β) (i₀ i₁ : Fin l.succ) (_ : pt_dir go j moves ph a i₀) (_ : pt_dir go j moves ph a i₁),
  i₀ = i₁) ∧ (  ∀ (i : Fin l.succ) (a₀ a₁ : β)
  (_ : pt_dir go j moves ph a₀ i)
  (_ : pt_dir go j moves ph a₁ i),
  a₀ = a₁
) := And.intro (unique_loc go j _ ph path_inj right_inj)
               (unique_dir go j _ ph left_inj)

theorem left_injective_of_embeds_in_strongly {α: Type} [OfNat α 0] [DecidableEq α]
{b : ℕ}
{go₀ go₁ : Fin b → α → α}
(f: Fin b → α → Fin b)
(is_emb: is_embedding go₀ go₁ f)
(left_inj_emb : left_injective f) -- which we can prove for tri_quad_embedding although it's harder than left_injective_tri!
(left_inj_go: left_injective go₁)
:
left_injective go₀ := by
  intro x a₀ a₁ hxy
  simp at hxy
  rw [is_emb a₀ x,is_emb a₁ x] at hxy
  exact left_inj_emb x (left_inj_go x hxy)


theorem unique_loc_dir_quad {l:ℕ} (j: Fin l.succ) -- location, direction
  (moves: Vector (Fin 4) l) (ph : Vector Bool l.succ)
  (path_inj: Function.Injective (λ k : Fin l.succ ↦ (pathVec rect moves).get k)):
  (∀ (a : Fin 4) (i₀ i₁ : Fin l.succ) (_ : pt_dir rect j moves ph a i₀) (_ : pt_dir rect j moves ph a i₁),
  i₀ = i₁) ∧ (  ∀ (i : Fin l.succ) (a₀ a₁ : Fin 4)
  (_ : pt_dir rect j moves ph a₀ i)
  (_ : pt_dir rect j moves ph a₁ i),
  a₀ = a₁
) :=  unique_loc_dir path_inj right_injective_quad left_injective_quad

theorem unique_loc_dir_hex {l:ℕ} (j: Fin l.succ)
  (moves: Vector (Fin 6) l) (ph : Vector Bool l.succ)
  (path_inj: Function.Injective (λ k : Fin l.succ ↦ (pathVec hex moves).get k)):
  (∀ (a : Fin 6) (i₀ i₁ : Fin l.succ) (_ : pt_dir hex j moves ph a i₀) (_ : pt_dir hex j moves ph a i₁),
  i₀ = i₁) ∧ (  ∀ (i : Fin l.succ) (a₀ a₁ : Fin 6)
  (_ : pt_dir hex j moves ph a₀ i)
  (_ : pt_dir hex j moves ph a₁ i),
  a₀ = a₁
) := unique_loc_dir path_inj right_injective_hex left_injective_hex

-- This trivial instance is nonetheless needed:
instance  {α: Type} [OfNat α 0] [DecidableEq α] {b:ℕ}
{go: Fin b → α → α}
  {l:ℕ} (j : Fin l.succ) (ph : Vector Bool l.succ) (moves: Vector (Fin b) l) (a : Fin b)
(i : Fin l.succ)
: Decidable (pt_dir go j moves ph a i) := decidable_of_iff (Vector.get ph i = true ∧
      Vector.get ph j = true ∧
        Nat.succ ↑i < ↑j ∧
        Vector.get (pathVec go moves) j = go a (Vector.get (pathVec go moves) i)) (by
          unfold pt_dir;tauto
        )

theorem pts_at'_dir {α: Type} [OfNat α 0] [DecidableEq α] {b:ℕ}
{go: Fin b → α → α}
  {l:ℕ} (j : Fin l.succ) (ph : Vector Bool l.succ)
  (moves: Vector (Fin b) l)
  (path_inj : (Function.Injective fun k => Vector.get (pathVec go moves) k))
  (right_inj: right_injective go)
  (left_inj: left_injective go)
  : pts_at' go j ph (pathVec go moves) ≤ b := by
    unfold pts_at'
    have : Finset.filter (
        λ i : Fin (Nat.succ l) ↦ (∃ a, pt_dir go j moves ph a i)) Finset.univ =
          Finset.filter (
        λ i : Fin (Nat.succ l) ↦  pt_loc go (pathVec go moves) i j ph) Finset.univ
    := by
      apply Finset.ext;intro i;repeat (rw [Finset.mem_filter]);simp;
      unfold pt_dir pt_loc nearby; simp; tauto
    rw [← this,← choice_ex_finset_card (unique_loc_dir path_inj right_inj left_inj)]
    apply card_finset_fin_le

theorem pts_earned_bound_dir' {α: Type} [OfNat α 0] [DecidableEq α] {b:ℕ}
{go: Fin b → α → α}
{l:ℕ} (ph : Vector Bool l.succ)
(moves: Vector (Fin b) l)
(path_inj  : (Function.Injective fun k => Vector.get (pathVec go moves) k))
(right_inj : right_injective go)
(left_inj  : left_injective go)
: pts_tot' go ph (pathVec go moves) ≤ l.succ * b := by
  suffices pts_tot' go ph (pathVec go moves) ≤ ∑ j : Fin l.succ, b by
    simp at this; tauto
  apply Finset.sum_le_sum; intro i; intro
  exact pts_at'_dir i ph moves path_inj right_inj left_inj


theorem pts_earned_bound' {α: Type} [OfNat α 0] [DecidableEq α] {b:ℕ}
{go: Fin b → α → α}
{l:ℕ} (ph : Vector Bool l.succ)
(moves: Vector (Fin b) l)
(path_inj : (Function.Injective fun k => Vector.get (pathVec go moves) k))
(right_inj : right_injective go)
(left_inj : left_injective go)

: pts_tot' go ph (pathVec go moves) ≤ min (l.succ * b) (l.succ * l / 2)
:= by
  suffices (
    pts_tot' go ph (pathVec go moves) ≤ l.succ * b
    ∧ pts_tot' go ph (pathVec go moves) ≤ l.succ * l / 2) by
    exact Nat.le_min.mpr this
  constructor
  exact pts_earned_bound_dir' ph moves path_inj right_inj left_inj
  exact pts_earned_bound_loc' go ph (pathVec go moves)


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

theorem path_at_cons {α:Type} (base :α) [OfNat α 0] [DecidableEq α] {b₀ : ℕ}
(go₀ : Fin b₀ → α → α)
(hd : Fin b₀) (tl : List (Fin b₀))
   : (path_at base go₀ (hd ::        tl)).1 =
             ((go₀  hd (path_at base go₀ tl).head) :: (path_at base go₀ tl).1) := rfl


theorem path_at_cons_vec {α:Type} (base :α) [OfNat α 0] [DecidableEq α] {b₀ : ℕ}
(go₀ : Fin b₀ → α → α)
(hd : Fin b₀) (tl : List (Fin b₀))
   : (path_at base go₀ (hd ::        tl)) =
             ((go₀  hd (path_at base go₀ tl).head) ::ᵥ (path_at base go₀ tl)) := rfl

-- theorem path_append {α:Type} [OfNat α 0] [DecidableEq α] {b₀ : ℕ}
-- (go₀ : Fin b₀ → α → α)
-- (u v : List (Fin b₀)):
-- (path go₀ (u ++ v)).1 = (path go₀ u).1 ++ (path go₀ v).1 := sorry
-- would have to translate the path by a vector
-- #eval path rect ([0,0])
-- #eval path rect ([1,1])

-- (head : Fin b₀) (tail : List (Fin b₀))
--    : (path go₀ (head ::        tail)).1 =
--              ((go₀  head (path go₀ tail).head) :: (path go₀ tail).1) := rfl


theorem path_len' {α: Type} [OfNat α 0] [DecidableEq α] {β: Type}
(go: β → α → α) (l: ℕ) (moves: List β) (hm: moves.length = l)
: List.length (path go moves).1 = Nat.succ l
:= by rw [(path go moves).2,hm]


lemma path_nil {α:Type} [OfNat α 0] [DecidableEq α] {β:Type} [Fintype β]
(go : β → α → α):
(path go []).1 = [0] := rfl

lemma path_at_nil {α:Type} (base:α) [DecidableEq α] {β:Type} [Fintype β]
(go : β → α → α):
(path_at base go []).1 = [base] := rfl

lemma path_at_nil_vec {α:Type} (base:α) [DecidableEq α] {β:Type} [Fintype β]
(go : β → α → α):
(path_at base go []) = ⟨[base],by simp⟩ := rfl

def ne_nil_of_succ_length {α :Type} {k:ℕ}
(tail_ih: Vector α k.succ)
: tail_ih.1 ≠ [] := by
    have : tail_ih.1.length = k.succ := tail_ih.2
    intro hc; rw [hc] at this; contrapose this; simp

-- theorem path_cons_list {α:Type} [OfNat α 0] [DecidableEq α] {b₀ : ℕ}
-- (go₀ : Fin b₀ → α → α)
-- (head : Fin b₀) (tail : List (Fin b₀))
--    : (path go₀ (head ::        tail)).1 =
--              (go₀  head ((path go₀ tail).1.head (by
--               apply ne_nil_of_succ_length
--             )) :: (path go₀ tail).1)
--              := by
--              simp
--              sorry

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
∀ moves : Vector β l,
Function.Injective (λ k ↦ (path go moves.1).1.get k)
→
pts_tot' go ph (⟨(path go moves.1).1,path_len _ _⟩) ≤ q

instance {α:Type} [OfNat α 0] [DecidableEq α] {β : Type} [Fintype β]
(go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) (q : ℕ):
DecidablePred (pts_tot_bound go moves)
:= by
  unfold pts_tot_bound pts_tot'
  exact inferInstance

instance {α:Type} [OfNat α 0] [DecidableEq α] {β : Type} [Fintype β]
(go : β → α → α) : DecidablePred fun n => pts_tot_bound go ph n :=
  by
  unfold pts_tot_bound pts_tot'
  exact inferInstance

theorem pts_tot_bound_exists {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β] (go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) :
∃ q, pts_tot_bound go ph q := by
  exists l.succ * l / 2; intro moves
  let Q := pts_earned_bound_loc' go ph (⟨(path go moves.1).1,path_len _ _⟩)
  tauto

/- HP is the HP protein folding model "objective function" or "value function": -/
def HP {α:Type} [OfNat α 0] [DecidableEq α] {β : Type} [Fintype β]
(go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) :ℕ := Nat.find (pts_tot_bound_exists go ph)
/- ph has to be of succ type because there will at least be an amino acid at the origin. -/

def P_tri'  {l:ℕ} := λ ph : Vector Bool l.succ ↦ HP tri  ph
def P_rect' {l:ℕ} := λ ph : Vector Bool l.succ ↦ HP rect ph
def P_hex'  {l:ℕ} := λ ph : Vector Bool l.succ ↦ HP hex  ph

theorem vector_inj_of_list_inj {t : Type} {n : ℕ}
{v : Vector t n} (h: Function.Injective fun k => List.get v.1 k) :
Function.Injective fun k => Vector.get v k := by
  intro x y hxy
  unfold Function.Injective at *
  simp at hxy
  have hx: x.1 < v.1.length := by
    let Q := x.2
    have : v.1.length = n := v.2
    simp_rw [← this] at Q
    exact Q
  have hy: y.1 < v.1.length := by
    let Q := y.2
    have : v.1.length = n := v.2
    simp_rw [← this] at Q
    exact Q
  have : List.get v.1 ⟨x.1,hx⟩ = List.get v.1 ⟨y,hy⟩ := by exact hxy
  let Q := h this
  simp at Q
  exact Fin.ext Q


theorem list_inj_of_vector_inj {t : Type} {n : ℕ}
{v : Vector t n} (h: Function.Injective fun k => Vector.get v k) :
Function.Injective fun k => List.get v.1 k := by
  intro x y hxy
  unfold Function.Injective at *
  have : Vector.get ⟨v.1,rfl⟩ x = Vector.get ⟨v.1,rfl⟩ y := by exact hxy
  have hx: x.1 < n := by
    let Q := x.2
    have : v.1.length = n := v.2
    simp_rw [this] at Q
    exact Q
  have hy: y.1 < n := by
    let Q := y.2
    have : v.1.length = n := v.2
    simp_rw [this] at Q
    exact Q
  have : Vector.get v ⟨x.1,hx⟩ = Vector.get v ⟨y.1,hy⟩ := by exact hxy
  let Q := h this
  simp at Q hxy
  exact Fin.ext Q

theorem P_tri_lin_bound
{l:ℕ} (ph : Vector Bool l.succ)
: P_tri' ph ≤ l.succ * 3 := by
  suffices pts_tot_bound tri ph (l.succ * 3) by exact Nat.find_le this
  intro moves path_inj
  exact pts_earned_bound_dir' _ _ (vector_inj_of_list_inj path_inj) right_injective_tri left_injective_tri

theorem P_hex_lin_bound
{l:ℕ} (ph : Vector Bool l.succ)
: P_hex' ph ≤ l.succ * 6 := by
  suffices pts_tot_bound hex ph (l.succ * 6) by exact Nat.find_le this
  intro moves path_inj
  exact pts_earned_bound_dir' _ _ (vector_inj_of_list_inj path_inj) right_injective_hex left_injective_hex

theorem P_rect_lin_bound
{l:ℕ} (ph : Vector Bool l.succ)
: P_rect' ph ≤ l.succ * 4 := by
  suffices pts_tot_bound rect ph (l.succ * 4) by exact Nat.find_le this
  intro moves path_inj
  exact pts_earned_bound_dir' _ _ (vector_inj_of_list_inj path_inj) right_injective_quad left_injective_quad

theorem value_bound_of_embeds_strongly {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α}
{go₁ : Fin b₁ → α → α}    (h_embed : go₀    ≼    go₁)
{l:ℕ} (ph : Vector Bool l.succ) : HP go₀ ph ≤ HP go₁ ph := by
  apply Nat.find_mono
  intro q hq moves h_inj
  let he := embeds_of_strongly_embeds h_embed
  let Q := pts_bound_of_embeds' he ph (⟨(path go₀ moves.1).1,path_len _ _⟩)
  rcases h_embed with ⟨f,hf⟩
  let moves' := (
    ⟨
      morph f go₀ moves.1,
      (by rw [morph_len]; exact moves.2)
    ⟩ : Vector (Fin b₁) l)
  have h_inj':
  Function.Injective (λ k ↦ (path go₁ (morph f go₀ moves.1)).1.get k)
  := by
    let Q := transform_of_embed f go₀ go₁ (moves.1) hf
    unfold path_transformed at Q
    let R := congrArg (λ x ↦ x.1) Q
    simp at R

    rw [R]
    tauto
  have : (path go₀ moves.1).1 = (path go₁ (morph f go₀ moves.1)).1 :=
    path_eq_path_morph f go₀ go₁ hf moves.1
  calc
  _ ≤ pts_tot' go₁ ph ⟨(path go₀  moves.1).1, path_len _ _⟩ := Q
  _ = pts_tot' go₁ ph ⟨(path go₁ moves'.1).1, path_len _ _⟩ := by simp_rw [this]
  _ ≤ q                                                    := hq moves' h_inj'

theorem embeds_strongly_tri_quad : tri ≼ rect := by
  exists tri_quad_embedding
  exact tri_quad_embedding_is_embedding

theorem embeds_strongly_quad_hex : rect ≼ hex := by
  exists quad_hex_embedding
  exact quad_hex_embedding_is_embedding

/- Here are some quotable results:
  The degree 3 "hexagonal lattice" protein folding model has an objective function
  P_tri that is bounded by that of the usual HP 2D model.
  Similarly for P_quad and P_hex.
-/


theorem HP_quad_bounds_tri {l:ℕ} (ph : Vector Bool l.succ) : HP tri ph ≤ HP rect ph :=
  value_bound_of_embeds_strongly embeds_strongly_tri_quad _
theorem HP_hex_bounds_quad {l:ℕ} (ph : Vector Bool l.succ) : HP rect ph ≤ HP hex ph :=
  value_bound_of_embeds_strongly embeds_strongly_quad_hex _

-- A sample combination of the two main threads of inequalities:
theorem sample_combination_of_the_two_main_threads_of_inequalities
{l:ℕ} (ph : Vector Bool l.succ):
 HP rect ph ≤ l.succ * 6 := calc
  _         ≤ HP hex ph  := HP_hex_bounds_quad ph
  _         ≤ l.succ * 6 := P_hex_lin_bound ph


end Main_theoretical_development


-- theorem pathVec_at_append  -- started Feb. 23, 2024
--   {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) (t v : List (Fin b)):
--   (pathVec go (⟨t++v,_⟩)).1 =
--   (pathVec_at (pathVec go ⟨v,_⟩).head go ⟨t,_⟩).1
--   ++
--   (pathVec go ⟨v,_⟩).1.tail -- Nice!
--   := by
--   sorry



theorem path_at_append  -- started Feb. 23, 2024
  {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) (t v : List (Fin b)):
  (path go (t++v)).1 =
  (path_at (path go v).head go t).1
  ++
  (path go v).1.tail -- Nice!
  := by
    induction t
    simp;rw [path_at_nil,List.cons_append];simp
    rw [two_heads (path go v) (path go v).1 (ne_nil_of_succ_length _) rfl]
    let Q := List.cons_head!_tail (ne_nil_of_succ_length (path go v))
    have : List.head! (path go v).1 = List.head (path go v).1 (ne_nil_of_succ_length (path go v))
        := by
          refine List.head!_of_head? ?_
          exact List.head?_eq_head ((path go v).1) (ne_nil_of_succ_length (path go v))
    rw [this] at Q
    . rw [Q]
    rename List (Fin b) => tl
    rename Fin b => hd
    simp;
    rw [path_cons]
    rw [tail_ih]
    nth_rewrite 1 [path_at_cons]
    simp
    have :
    (Vector.head (path go (tl ++ v))) =
    (Vector.head (path_at (Vector.head (path go v)) go tl))
    := by
      unfold path
      induction tl
      simp
      -- have : (path_at (Vector.head (path_at 0 go v)) go []).1
      -- = [Vector.head (path_at 0 go v)] := path_at_nil _ _

      rw [path_at_nil_vec]
      . exact rfl


      unfold path at tail_ih
      have : (path_at 0 go (head :: tail ++ v)).1 =
        (path_at (Vector.head (path_at 0 go v)) go (head :: tail)).1 ++ List.tail (path_at 0 go v).1
        := tail_ih

      have : List.head (path_at 0 go (head :: tail ++ v)).1 (ne_nil_of_succ_length _) =
        List.head ((path_at (Vector.head (path_at 0 go v)) go (head :: tail)).1 ++ List.tail (path_at 0 go v).1)
        (by
          intro hc
          have :  (path_at (Vector.head (path_at 0 go v)) go (head :: tail)).1 = []
              := (List.append_eq_nil.mp hc).1
          exact ne_nil_of_succ_length _ this
        )
        := by
          simp_rw [tail_ih]
      -- rw [← two_heads _ _ _ _] at this
      -- rw [← two_heads _ _ _ _] at this
      nth_rewrite 1 [path_at_cons_vec]
      rw [Vector.head_cons]
      have : head :: tail ++ v = head :: (tail ++ v) := rfl
      rw [this]
      rw [path_at_cons_vec]
      rw [Vector.head_cons]
      -- induction v
      -- simp
      -- rw [List.append_nil]
      -- have : Vector.head (path_at 0 go []) = 0 := rfl
      -- rw [this]
      -- rename Fin b => Hd
      -- rename List (Fin b) => Tl
      have : (Vector.head (path_at 0 go (tail ++ v))) =
             (Vector.head (path_at (Vector.head (path_at 0 go v)) go tail))
        := by

          sorry
      rw [this]
    rw [this]

-- theorem preserved_under_prefixes_injective
--   {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ)
--   : ∀ (u v : List (Fin b)),
--   u <+: v → (λ moves ↦ Function.Injective (λ i ↦ (path go moves).get i)) v →
--             (λ moves ↦ Function.Injective (λ i ↦ (path go moves).get i)) u := by
--     unfold Function.Injective at *
--     intro u v huv hP i j hij;
--     simp at hij;
--     rcases huv with ⟨t,ht⟩
--     simp at hP
--     rw [← ht] at hP
--     have : (path go u).1 <:+ (path go (u++t)).1 := sorry
--     have : Vector.get (path go (u++t)) i
--          = Vector.get (path go (u++t)) j := sorry
--     -- let Q := hP hij
--     sorry

#eval (path rect [0,2])
#eval (path rect ([2,2] ++ [0,2]))

-- #eval (path rect [0,1]).1 <:+ (path rect [2,2,0,1]).1


-- theorem pathgocons
-- {b: ℕ}
-- (go: Fin b → ℤ × ℤ → ℤ × ℤ)
-- (u v: List (Fin b))
-- (hv: Function.Injective fun i => List.get (path go v).1 i)
-- (i j: Fin (Nat.succ (List.length u)))
-- (hij: List.get (path go u).1 ⟨i.1,sorry⟩ = List.get (path go u).1 ⟨j.1,sorry⟩)
-- (t: List (Fin b))
-- (hij: (path go u).1.get ⟨i.1,sorry⟩ = (path go u).1.get ⟨j.1,sorry⟩)
-- : (path go (t++u)).1.get ⟨(t.length + i.1),sorry⟩
-- = (path go (t++u)).1.get ⟨(t.length + j.1),sorry⟩ := by
--   induction t
--   simp
--   exact hij

--   simp at *
--   --  let Q := tail_ih ht
--   --  simp
--   simp_rw [path_cons]
--   -- rw [← tail_ih]--  exact hij
--   sorry -- now use path_cons?

-- theorem continuity {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ)
--   : ∀ u v, u <:+ v → (path go u).1 <:+ (path go v).1 := by
--   intro u v huv
--   -- maybe need to talk about paths with a nonzero base point?
--   sorry

theorem building_block
  {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) (tail : List (Fin b)) (head: Fin b):
(path go tail).1 <:+ (path go (head :: tail)).1
:= by
  rw [path_cons]
  exact List.suffix_cons (go head (Vector.head (path go tail))) (path go tail).1


theorem building_block2
  {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) (tail : List (Fin b)) (head: List (Fin b)):
(path go tail).1 <:+ (path go (head ++ tail)).1
:= by
  induction head
  simp
  exact List.suffix_rfl
  calc
  _ <:+ (path go (tail_1 ++ tail)).1 := tail_ih
  _ <:+ _ := building_block _ _ _

def mymonopred {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ)  : MonoPred b :=
{
  P := (λ moves ↦ List.Nodup (path go moves).1)
  preserved_under_suffixes := by
    intro u v huv
    obtain ⟨t,ht⟩ := huv
    symm at ht
    subst ht
    simp
    intro h
    obtain ⟨s,hs⟩ := building_block2 go u t
    rw [← hs] at h
    exact List.Nodup.of_append_right h
}


-- def mymonopred {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ)  : MonoPred b :=
-- {
--   P := (λ moves ↦ Function.Injective (λ i ↦ (pathVec go ⟨moves,rfl⟩).get i))
--   preserved_under_suffixes := by
--     intro u v huv hv i j hij; simp at hij; rcases huv with ⟨t,ht⟩
--     have hil: t.length + i.1 < (path go v).1.length := by
--       let Q := path_len' go v.length v rfl; rw [Q,← ht]; calc
--       _ < t.length + u.length.succ := Nat.add_lt_add_left i.2 t.length
--       _ = _                        := by rw [Nat.add_succ];simp
--     have hjl: t.length + j.1 < (path go v).1.length := by
--       let Q := path_len' go v.length v rfl; rw [Q,← ht]; calc
--       _ < t.length + u.length.succ := Nat.add_lt_add_left j.2 t.length
--       _ = _                        := by rw [Nat.add_succ];simp
--     have : Vector.get (pathVec go ⟨v,rfl⟩) (t.length + i.1)
--          = Vector.get (pathVec go ⟨v,rfl⟩) (t.length + j.1)
--     := by
--       rw [← ht]
--       sorry
--     unfold Function.Injective at hv
--     -- have : t.length + i.1 = t.length + j.1 := hv this
--     let Q := hv this
--     have :  (⟨t.length + i.1,hil⟩ : Fin (path go v).1.length)
--           = (⟨t.length + j.1,hjl⟩ : Fin (path go v).1.length)
--       := by
--       simp at Q; simp
--       sorry
--     exact Fin.ext (Nat.add_left_cancel (Fin.mk_eq_mk.mp this))
-- }

section Backtracking_usage

def first_nonzero_entry (moves : List (Fin 4)) : Option (Fin 4) := by {
  induction moves
  .  exact none
  .  exact ite (tail_ih ≠ none) tail_ih (ite (head = 0) none head)
}

-- By symmetry we may assume that all walks (folds) are orderly, although that in itself could deserve a proof.
def orderly (moves: List (Fin 4)) := moves.reverse.getLast? = some (0:Fin 4)
      ∧ first_nonzero_entry moves.reverse = some 2

instance (moves : List (Fin 4)) : Decidable (orderly moves) := by unfold orderly; exact And.decidable

def pts_tot'_list {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) (ph : List Bool) (moves: List (Fin b)): ℕ
:= dite (moves.length.succ = ph.length)
    (λ h ↦ pts_tot' -- or pts_tot
      go
      (⟨ph, rfl⟩ : Vector Bool ph.length)
      ⟨(path go moves).1,(by rw [← h,path_len'];rfl)⟩
    )
    (λ _ ↦ 0)

-- make these have "go" as a parameter:
def set_of_folds_achieving_pts {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ)
  {l:ℕ} (ph : Vector Bool l.succ.succ) (p:ℕ):=
  those_with_suffix'
    (λ moves ↦ Function.Injective (λ i ↦ (path go moves).get i))
    (λ moves ↦ pts_tot'_list go ph.1 moves ≥ p ∧ orderly moves)
    (Gap_nil' b l.succ) -- (there are 7 moves for a polypeptide of length 8)

def num_folds_achieving_pts {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ)
  {l:ℕ} (ph : Vector Bool l.succ.succ) (p:ℕ) : ℕ :=
  num_by_backtracking
    (λ moves ↦ Function.Injective (λ i ↦ (path go moves).get i))
    (λ moves ↦ pts_tot'_list go ph.1 moves ≥ p ∧ orderly moves)
    (Gap_nil' b l.succ) -- (there are 7 moves for a polypeptide of length 8)


def can_achieve_pts {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ)
  {l:ℕ} (ph : Vector Bool l.succ.succ) (p:ℕ): Prop :=
  set_of_folds_achieving_pts go ph p ≠ ∅

-- theorem itworks {l:ℕ} {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) (ph : Vector Bool l.succ) (moves: Vector (Fin b) l) :
-- pts_tot' go ph (pathVec go moves) = pts_tot'_list go ph.1 moves.1 := by
--   unfold pts_tot'_list pts_tot' pathVec
--   simp
--   rw [ph.2]
--   sorry
#check rect
def x : List Bool := [true,false,true,false,true,false, true,true]
-- #eval HP rect ⟨x,rfl⟩           -- This evaluates to 3 quickly, don't even need the backtracking.
-- #eval HP rect ⟨x ++ [false],rfl⟩-- This evaluates to 2 quickly, don't even need the backtracking.
-- example: HP rect ⟨x ++ [false],rfl⟩ = 2 := by decide
#eval pts_tot'_list rect  x [0, 3, 1, 1, 2, 2, 0]
-- #eval pts_tot'_list rect  x [r2.D, r2.S, r2.A, r2.A, r2.W, r2.W, r2.D]
-- #eval pts_tot'_list rect  (x ++ [false]) [0, 3, 1, 1, 2, 2, 0].reverse

def stecher1 : Prop :=
  those_with_suffix'
    (λ w ↦ Function.Injective (λ i ↦ (path quad w).get i))
    (λ w ↦ pts_tot'_list rect  x w > 2 ∧ orderly w)
    (Gap_nil' 4 7) -- (there are 7 moves for a polypeptide of length 8)
  = {⟨[0, 3, 3, 1, 1, 2, 0],rfl⟩} --{⟨[0, 3, 1, 1, 2, 2, 0],rfl⟩}
instance : Decidable stecher1 := by {
  unfold stecher1
  apply decEq
}
-- #eval [0,2,1].reverse.getLast?
-- #eval first_nonzero_entry [0,2,1]
-- #eval orderly [0,2,1]
-- #eval   (those_with_suffix'
--     (λ w ↦ Function.Injective (λ i ↦ (path quad w).get i))
--     (λ w ↦ pts_tot'_list rect  ([true,false,false,true]) w > 0 ∧ orderly w)
--     (Gap_nil' 4 3)) -- fixed February 20, 2024

def L : ℕ := 10
-- #eval   (those_with_suffix'
--     (λ w ↦ Function.Injective (λ i ↦ (path quad w).get i))
--     (λ w ↦ pts_tot'_list rect  (List.replicate L.succ true) w ≥ 5 ∧ orderly w)
--     (Gap_nil' 4 L)) -- fixed February 20, 2024

-- #eval HP rect ⟨[true],rfl⟩
-- #eval HP rect ⟨List.replicate 9 true,rfl⟩ -- 4
-- #eval HP rect ⟨List.replicate L.succ true,rfl⟩ -- 4
-- #eval HP hex ⟨List.replicate 3 true,rfl⟩ -- amazing

-- #eval (myvec 4 7).length
-- #eval stecher1

def stecher2 : Prop :=
those_with_suffix'
    (λ w ↦ Function.Injective (λ i ↦ (path quad w).get i))
    (
      λ w ↦ pts_tot'_list rect  (x ++ [false]) w > 2
        ∧ orderly w
    )
    (Gap_nil' 4 8) = ∅


def stecher_conjecture_counterexample : Prop := stecher1  ∧ stecher2

instance : Decidable stecher2 := by unfold stecher2; apply decEq
instance : Decidable stecher_conjecture_counterexample := by
  unfold stecher_conjecture_counterexample; unfold stecher1; unfold stecher2; exact And.decidable

-- #eval stecher1
-- #eval stecher2
-- #eval stecher_conjecture_counterexample

end Backtracking_usage

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

theorem fundamental_relation_for_tri: go_D ∘ go_WS ∘ go_A ∘ go_A ∘ go_WS ∘ go_D = id := by
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
