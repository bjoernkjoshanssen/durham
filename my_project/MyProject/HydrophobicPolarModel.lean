import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Data.Vector.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import MyProject.MonoPred
import MyProject.sum_pred
import MyProject.BacktrackingVerification

set_option maxHeartbeats 3000000

/-
A treatment of the hydrophobic-polar protein folding model in a generality
that covers rectangular, triangular and hexagonal lattices: `P_rect`, `P_tri`, `P_hex`.

We formalize the non-monotonicity of the objective function,
refuting an unpublished conjecture of Stecher.

We prove objective function bounds:
`P_tri ≤ P_rect ≤ P_hex` (using a theory of embeddings)
and for any model, `P ≤ b * l` and `P ≤ l * (l-1)/2` [see `pts_earned_bound_loc'`]

(The latter is worth keeping when `l ≤ 2b+1`.)

where `b` is the number of moves and `l` is the word length.
We also prove `P ≤ b * l / 2` using "handshake lemma" type reasoning
that was pointed out in Agarwala, Batzoglou et al. (`RECOMB 97`, Lemma 2.1)
and a symmetry assumption on the folding model that holds for `rect` and `hex` but not for `tri`.
The latter result required improving our definitions.

We prove the correctness of our backtracking algorithm for protein folding.

To prove some results about rotations
(we can always assume our fold starts by going to the right)
we use the type
`Fin n → α` instead of `Vector α n`

In `HPModel_pathF'.lean` we showed that orderly walks are sufficient, in particular "3" (down) can be avoided by reflection,
      except got stuck on proving that the moves left followed by right lead to non-injectivity,
      which was not a problem using pathF.
-/


section Defining_the_protein_folding_moves

/-- The original protein folding model introduced by Ken Dill in 1985. -/
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


def rectMap (a : Fin 4) : ℤ×ℤ := match a with
  | 0 => (1,0)
  | 1 => (-1,0)
  | 2 => (0,1)
  | 3 => (0,-1)

-- rect₃ allows for polynomial-time optimal folding:
def rect₃Map (a : Fin 3) : ℤ×ℤ := match a with
  | 0 => (1,0)
  | 1 => (-1,0)
  | 2 => (0,1)
def rect₃ (a : Fin 3) (x: ℤ×ℤ) : ℤ×ℤ := x + rect₃Map a

def rect (a : Fin 4) (x: ℤ×ℤ) : ℤ×ℤ := x + rectMap a

abbrev κ := rect

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
  | 0 => (1,0) | 1 => (-1,0) | 2 => (0,1) | 3 => (0,-1)| 4 => (1,1)  | 5 => (-1,-1)

def hex₄Map (a : Fin 4) : ℤ×ℤ := match a with
  | 0 => (1,0) | 1 => (-1,0) | 2 => (0,1) | 3 => (1,1)

def hex (a : Fin 6) (x: ℤ×ℤ) : ℤ×ℤ := x + hexMap a
def hex₄ (a : Fin 4) (x: ℤ×ℤ) : ℤ×ℤ := x + hex₄Map a

theorem hexMap_injective : Function.Injective hexMap := by decide

def go_WS : ℤ×ℤ → ℤ×ℤ := λ x ↦ ite (Even (x.1+x.2)) (sp x) (sm x)

def tri : Fin 3 → ℤ×ℤ → ℤ×ℤ
| 0 => go_D
| 1 => go_A
| 2 => go_WS

end Defining_the_protein_folding_moves

section Setting_up_point_earned

def Fin_trans {l : ℕ} {k: Fin l} (i : Fin k): Fin l :=
  ⟨i.1, Fin.val_lt_of_le _ (Fin.is_le')⟩


def Fin_trans'' {l : ℕ} {k: Fin l} (i : Fin k.1.pred): Fin l :=
  ⟨i.1, by
    refine Fin.val_lt_of_le i ?h
    refine Nat.pred_le_iff.mpr ?h.a
    refine Nat.le_step ?h.a.h
    exact Fin.is_le'
  ⟩

def nearby {α β : Type} [DecidableEq α] [Fintype β] (go : β → α → α)
  (p q : α) : Bool := ∃ a : β, q = go a p

def pt_loc {α β : Type} [DecidableEq α] [Fintype β] (go : β → α → α)
 {l : ℕ} (fold : Vector α l) (i j : Fin l) (phobic : Vector Bool l) : Bool
:=  phobic.get i && phobic.get j && i.1.succ < j.1 && nearby go (fold.get i) (fold.get j)

def pts_at' {α β : Type} [DecidableEq α] [Fintype β] (go : β → α → α)
  {l:ℕ} (k : Fin l) (ph : Vector Bool l) (fold : Vector α l) : ℕ :=
  Finset.card (
    Finset.filter (λ i : Fin l ↦ (pt_loc go fold i k ph))
    Finset.univ
  )

/-
  We prove that pts_at  = pts_at'.
  pts_at' is more convenient type-theoretically, but
  pts_at is more useful for proving a certain bound.
-/

def change_type_general'' -- this adds a "pred" that can be used in applications
{l:ℕ} (k : Fin l) (P : Fin l → Fin l → Bool)
[DecidablePred fun i : Fin l => P i k]
(h: ∀ x y : Fin l, P x y → x.1.succ < y.1):
  Finset.filter (λ i : Fin l ↦ (P i k)) (Finset.univ : Finset (Fin l))
→ Finset.filter (λ i : Fin k.1.pred ↦ P (Fin_trans'' i) k) (Finset.univ : Finset (Fin k.1.pred))
  := by
    intro ip;let i₃ := ip.2;
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at i₃ ;
    simp only [Finset.mem_filter, Finset.mem_univ, true_and];
    have : ∀ x y : Fin l, P x y → x.1 < y.1.pred := by
      intro x y hP
      exact Nat.lt_pred_iff.mpr (h x y hP)
    exact ⟨(⟨ip.1.1,this _ _ i₃⟩ : Fin k.1.pred),i₃⟩


theorem change_type_card_general'' {l:ℕ} (k : Fin l) (P : Fin l → Fin l → Bool)
[DecidablePred fun i : Fin l => P i k]
(h: ∀ x y : Fin l, P x y → x.1.succ < y.1)
:
Fintype.card (Finset.filter (λ i : Fin l ↦ P i k) Finset.univ)
=
Fintype.card (Finset.filter (λ i : Fin k.1.pred ↦ (P (Fin_trans'' i) k)) Finset.univ)
:= by
  have : Function.Bijective (change_type_general'' k P h) := by
    constructor
    . intro i₁ i₂ hi; unfold change_type_general'' at hi;
      simp only [eq_mpr_eq_cast, Finset.filter_congr_decidable, Finset.filter_val,
        Multiset.mem_filter, Finset.mem_val, Finset.mem_univ, true_and, set_coe_cast,
        Subtype.mk.injEq, Fin.mk.injEq] at hi
      exact SetCoe.ext (Fin.ext hi)
    . intro i;
      exists ⟨Fin_trans'' i, by
        let Q := i.2;
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at Q ;
        simp only [Finset.mem_filter, Finset.mem_univ, true_and];
        exact Q⟩
      apply Subtype.ext;apply Fin.ext;
      unfold change_type_general'' Fin_trans'';simp
  let Q := Fintype.card_of_bijective this
  rw [Q]



theorem change_type_card_improved  {α:Type} {β : Type} [Fintype β] (go : β → α → α)
  [DecidableEq α] {l:ℕ} (k : Fin l) (ph : Vector Bool l) (fold : Vector α l):
Fintype.card (Finset.filter (λ i : Fin l ↦ (pt_loc go fold i k ph)) Finset.univ)
=
Fintype.card (Finset.filter (λ i : Fin k.1.pred ↦ (pt_loc go fold (Fin_trans'' i) k ph)) Finset.univ)
:= by
  let P := (λ i k : Fin l ↦ ((pt_loc go fold i k ph) : Bool))
  have h : ∀ x y, P x y → x.1.succ < y.1 := by
    intro i k hP
    have : i.1.succ < k.1 := by
      have : P i k ↔ pt_loc go fold i k ph := by tauto
      unfold pt_loc at this
      rw [hP] at this
      simp only [Bool.and_eq_true, decide_eq_true_eq, true_iff] at this
      tauto
    exact this
  exact change_type_card_general'' k P h

def path_aux {α β: Type} {l: ℕ}
  (go: β → α → α) (hd: β)
  (tl: Vector α l.succ)
   : Vector α l.succ.succ := ⟨(go hd tl.head) :: tl.1, by simp⟩
def path_at {α:Type} {β : Type} (base:α) (go : β → α → α) :
  (moves : List β) → Vector α moves.length.succ
  | [] => ⟨[base], rfl⟩
  | head :: tail => path_aux go head (path_at base go tail)

/- Using OfNat here since ℤ×ℤ and ℤ×ℤ×ℤ have a natural notion of base point or zero.-/
def path {α:Type} [OfNat α 0] {β : Type} (go : β → α → α) :
  (moves : List β) → Vector α moves.length.succ
  := path_at 0 go

end Setting_up_point_earned

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
  obtain ⟨f₀₁,hf₀₁⟩ := h₀₁
  obtain ⟨f₁₂,hf₁₂⟩ := h₁₂
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
  obtain ⟨f,hf⟩ := h_embed; intro i x; exists f i x; exact hf i x

-- For tri we can only assert a pointwise version of embed_models:
/- It follows from tri_rect_embedding that any sequence of moves under tri generates a sequence in ℤ×ℤ
  that can also be generated using quad:
-/

def tri_rect_embedding : Fin 3 → ℤ×ℤ → Fin 4
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
def rect_hex_embedding : Fin 4 → ℤ×ℤ → Fin 6
| a => λ _ ↦ a

def rect₃_rect_embedding : Fin 3 → ℤ×ℤ → Fin 4
| a => λ _ ↦ a


theorem rect₃_rect_embedding_is_embedding :
  ∀ i : Fin 3, ∀ x : ℤ×ℤ, rect₃ i x = rect (rect₃_rect_embedding i x) x
  | 0 => λ _ ↦ rfl
  | 1 => λ _ ↦ rfl
  | 2 => λ _ ↦ rfl


theorem rect_hex_embedding_is_embedding :
  ∀ i : Fin 4, ∀ x : ℤ×ℤ, rect i x = hex (rect_hex_embedding i x) x
  | 0 => λ _ ↦ rfl
  | 1 => λ _ ↦ rfl
  | 2 => λ _ ↦ rfl
  | 3 => λ _ ↦ rfl


theorem tri_rect_embedding_is_embedding :
  ∀ i : Fin 3, ∀ x : ℤ×ℤ, tri i x = rect (tri_rect_embedding i x) x
  | 0 => λ x ↦ rfl
  | 1 => λ x ↦ rfl
  | 2 => λ x ↦ by
    by_cases h: Even (x.1+x.2)-- "show" thanks to Johan Commelin
    show (if Even (x.1 + x.2) then sp x else sm x)  = rect (tri_rect_embedding 2 x) x
    rw [if_pos h];
    have : tri_rect_embedding 2 x = 2 := by
      show (if Even (x.1 + x.2) then 2 else 3) = 2;
      simp only [ite_eq_left_iff]; tauto
    . rw [this]; rfl
    have : tri_rect_embedding 2 x = 3 := by
      show (if Even (x.1 + x.2) then 2 else 3) = 3;
      simp only [ite_eq_right_iff]; tauto
    rw [this];
    show (if Even (x.1 + x.2) then sp x else sm x) = sm x
    . simp only [ite_eq_right_iff]; tauto

end Embedding_one_protein_folding_model_into_another

section Left_and_right_injectivity

def left_injective {α:Type} {β γ: Type} [Fintype β] (go : β → α → γ)
[DecidableEq α] := ∀ a, Function.Injective (λ b ↦ go b a)
-- all "β-slices" are injective

def right_injective {α:Type} {β γ: Type} [Fintype β] (go : β → α → γ)
[DecidableEq α] := ∀ b, Function.Injective (λ a ↦ go b a)


theorem rect₃_rect_embedding_left_injective :
left_injective rect₃_rect_embedding := by
  unfold left_injective at *
  intro x a b hab
  simp only at *
  unfold rect₃_rect_embedding at hab
  simp only [Fin.coe_eq_castSucc] at hab
  exact Fin.castSucc_inj.mp hab

theorem tri_rect_embedding_left_injective :
left_injective tri_rect_embedding := by
  unfold left_injective at *
  intro x
  intro a b hab
  simp only at *
  unfold tri_rect_embedding at *
  contrapose hab

  match a with
  | 0 => match b with
    | 0 => tauto
    | 1 =>
      show  ¬ (0 % 4 : Fin 4) =  1 % 4
      exact (bne_iff_ne (0 % 4) (1 % 4)).mp (by exact rfl)
    | 2 =>
      show ¬0 = if Even (x.1 + x.2) then 2 else 3
      by_cases h : Even (x.1+x.2)
      . rw [if_pos h];intro hc
        let Q := congr_arg (λ x ↦ x.1) hc;simp at Q
      . rw [if_neg h];intro hc
        let Q := congr_arg (λ x ↦ x.1) hc; simp only [Fin.val_zero] at Q ;tauto
  | 1 => match b with
    | 1 => tauto
    | 0 =>
      show  ¬ (1 % 4 : Fin 4) =  0 % 4
      exact (bne_iff_ne (1 % 4) (0 % 4)).mp (by exact rfl)
    | 2 =>
      show  ¬1 = if Even (x.1 + x.2) then 2 else 3
      by_cases h : Even (x.1+x.2)
      . rw [if_pos h];intro hc
        let Q := congr_arg (λ x ↦ x.1) hc;simp at Q
      . rw [if_neg h];intro hc
        let Q := congr_arg (λ x ↦ x.1) hc;
        simp only [Fin.val_one] at Q ;
        apply Nat.succ_injective at Q
        tauto
  | 2 => match b with
    | 1 =>
      show ¬(if Even (x.1 + x.2) then 2 else 3) = 1
      by_cases h : Even (x.1+x.2)
      . rw [if_pos h];intro hc
        let Q := congr_arg (λ x ↦ x.1) hc;simp at Q
      . rw [if_neg h];intro hc
        let Q := congr_arg (λ x ↦ x.1) hc;
        simp only [Fin.val_one] at Q ;
        apply Nat.succ_injective at Q
        tauto
    | 0 =>
      show ¬(if Even (x.1 + x.2) then 2 else 3) = 0
      by_cases h : Even (x.1+x.2)
      . rw [if_pos h];intro hc
        let Q := congr_arg (λ x ↦ x.1) hc;
        simp at Q
      . rw [if_neg h];intro hc
        let Q := congr_arg (λ x ↦ x.1) hc;
        simp only [Fin.val_zero] at Q ;
        tauto
    | 2 => tauto

theorem sp_injective : Function.Injective sp := by
  intro x y hxy
  unfold sp at *
  rw [add_left_inj] at hxy
  tauto

theorem sm_injective : Function.Injective sm := by
  intro x y hxy
  unfold sm at *
  rw [add_left_inj] at hxy ;
  tauto


theorem go_WS_injective : Function.Injective go_WS := by
  intro x y hxy
  unfold go_WS at *
  by_cases hx : Even (x.1 + x.2)
  . --pos
    rw [if_pos hx] at hxy
    by_cases hy : Even (y.1 + y.2)
    . -- pos
      rw [if_pos hy] at hxy; exact sp_injective hxy
    -- neg
    rw [if_neg hy] at hxy; unfold sp sm at hxy
    let Q := Prod.ext_iff.mp hxy
    simp only [Prod.fst_add, add_zero, Prod.snd_add] at Q
    contrapose hy;
    simp only [not_not]
    obtain ⟨k,hk⟩ := hx; exists (k+1); linarith
  . -- neg
    rw [if_neg hx] at hxy
    by_cases hy : Even (y.1 + y.2)
    . -- pos
      rw [if_pos hy] at hxy
      unfold sm sp at hxy
      let Q := Prod.ext_iff.mp hxy
      simp only [Prod.fst_add, add_zero, Prod.snd_add] at Q
      contrapose hx; simp only [not_not]
      obtain ⟨k,hk⟩ := hy; exists (k+1); linarith
    . -- neg
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
    rw [not_not] at *
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
    by_cases h:(Even (x.1 + x.2))
    . rw [if_pos h]; simp
    . rw [if_neg h]; simp
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

theorem rectMap_injective : Function.Injective rectMap := by decide

theorem rect₃Map_injective : Function.Injective rect₃Map := by decide


theorem left_injective_hex : left_injective hex := by
  intro a
  unfold hex
  intro x y hxy
  rw [add_right_inj] at hxy
  exact hexMap_injective hxy

theorem left_injective_rect : left_injective rect := by
  unfold left_injective
  intro a
  unfold rect
  intro x y hxy
  rw [add_right_inj] at hxy
  exact rectMap_injective hxy

theorem left_injective_rect₃ : left_injective rect₃ := by
  unfold left_injective
  intro a
  unfold rect₃
  intro x y hxy
  rw [add_right_inj] at hxy
  exact rect₃Map_injective hxy


lemma right_injective_rect : right_injective rect   := λ _ ↦ add_left_injective _
lemma right_injective_rect₃ : right_injective rect₃ := λ _ ↦ add_left_injective _
lemma right_injective_hex : right_injective hex   := λ _ ↦ add_left_injective _

end Left_and_right_injectivity


section Equivalent_existential_definitions_of_point_earned


def choice_ex {β:Type} [Fintype β] {l : ℕ} (P : β → Fin l → Prop)
[DecidablePred fun a => ∃ i, P a i]
[DecidablePred fun i => ∃ a, P a i]
[∀ a, DecidablePred fun n => ∃ (hq : n < l), P a { val := n, isLt := hq }]
:
    (Finset.filter (λ a ↦ ∃ i, P a i) (Finset.univ : Finset β))
 →  (Finset.filter (λ i ↦ ∃ a, P a i) (Finset.univ : Finset (Fin l)))
:= by
  intro a; let a₂ := a.2;
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at a₂
  have h₀: ∃ (i : ℕ), ∃ (hi : i < l), P a ⟨i,hi⟩ := by
    obtain ⟨i,_⟩ := a₂;exists i.1; exists i.2
  exact ⟨⟨Nat.find h₀,(Nat.find_spec h₀).1⟩,by simp; exists a; exact (Nat.find_spec h₀).2⟩

lemma choice_ex_injective {β:Type} [Fintype β] {l : ℕ} {P : β → Fin l.succ → Prop}
[DecidablePred fun a => ∃ i, P a i]
[DecidablePred fun i => ∃ a, P a i]
[ (a : β) → DecidablePred fun n => ∃ (hq : n < l.succ), P a { val := n, isLt := hq }]
(h_unique_dir : ∀ {i a₀ a₁}, P a₀ i → P a₁ i → a₀ = a₁)
:
Function.Injective (choice_ex P) := by
  intro a b hab
  unfold choice_ex at hab
  simp only [Subtype.mk.injEq, Fin.mk.injEq] at hab

  let a₂ := a.2; let b₂ := b.2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at a₂ b₂
  rw [Fin.exists_iff] at a₂ b₂
  let ia := (⟨Nat.find a₂, (Nat.find_spec a₂).1⟩ : Fin l.succ)
  let ib := (⟨Nat.find b₂, (Nat.find_spec b₂).1⟩ : Fin l.succ)

  let hia₂ := (Nat.find_spec a₂).2
  have hib₂: P b ib := (Nat.find_spec b₂).2

  have : ia = ib := Fin.mk_eq_mk.mpr hab
  rw [← this] at hib₂
  exact Subtype.ext (h_unique_dir hia₂ hib₂)

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
(h_unique_loc : ∀ {a i₀ i₁}, P a i₀ → P a i₁ → i₀ = i₁) :
Function.Surjective (choice_ex P) := by
  intro i; let i₂ := i.2; simp only [Finset.mem_filter, Finset.mem_univ,
    true_and] at i₂ ;
  obtain ⟨a,ha⟩ := i₂
  exists ⟨a,by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exists i
  ⟩
  let j := choice_ex P ⟨
    a,
    (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exists i : a ∈ Finset.filter (fun a => ∃ i, P a i) Finset.univ)
  ⟩
  show j = i
  have : P a (choice_ex P ⟨a, (by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and];exists i
  )⟩) := choice_ex_aux ha
  let Q := h_unique_loc ha this
  exact Subtype.ext Q.symm

lemma choice_ex_bijective {β:Type} [Fintype β] {l : ℕ} {P : β → Fin l.succ → Prop}
  [DecidablePred fun a => ∃ i, P a i]
  [DecidablePred fun i => ∃ a, P a i]
  [ (a : β) → DecidablePred fun n => ∃ (hq : n < l.succ), P a { val := n, isLt := hq }]
  (h_unique_loc : ∀ {a i₀ i₁}, P a i₀ → P a i₁ → i₀ = i₁)
  (h_unique_dir : ∀ {i a₀ a₁}, P a₀ i → P a₁ i → a₀ = a₁)
  : Function.Bijective (choice_ex P) := And.intro
    (choice_ex_injective  h_unique_dir)
    (choice_ex_surjective h_unique_loc)

theorem choice_ex_finset_card {β:Type} [Fintype β] {l : ℕ} {P : β → Fin l.succ → Prop}
-- Completed February 16, 2024
[DecidablePred fun a => ∃ i, P a i]
[DecidablePred fun i => ∃ a, P a i]
[(a : β) → DecidablePred fun n => ∃ (hq : n < l.succ), P a     ⟨n,hq⟩]
(h_unique_loc_dir : (∀ {a i₀ i₁}, P a i₀ → P a i₁ → i₀ = i₁) ∧ ∀ {i a₀ a₁}, P a₀ i → P a₁ i → a₀ = a₁):
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

def pathf {α β:Type} [OfNat α 0] {l:ℕ} (go : β → α → α) (moves : Fin l → β)
:
ℕ → α → α :=
λ n base ↦ by
  induction n with
  |zero => exact base
  |succ n_1 n_ih =>
    by_cases h : n_1 < l
    . exact go (moves ⟨n_1,h⟩) n_ih
    . exact n_ih



def M {α : Type} [OfNat α 0] {β : Type} (go : β → α → α) : DFA β α := {
  step := λ x a ↦ go a x
  start := 0
  accept := Set.univ -- we are not really interested in acceptance
}

def pathD'  {α : Type} {l:ℕ} [OfNat α 0] {β : Type} (go : β → α → α) (moves : Vector β l) :
Fin l.succ → α
  := λ i ↦ (M go).eval (moves.1.take i)

def pathD  {α : Type} {l:ℕ} [OfNat α 0] {β : Type} (go : β → α → α) (moves : Fin l → β) :
Fin l.succ → α
  := λ i ↦ (M go).eval (List.ofFn (λ j : Fin i.1 ↦ (moves ⟨j.1, Fin.val_lt_of_le j (Fin.is_le i)⟩)))

#eval pathD rect ![0,1,1]

def path₀ {α : Type} [OfNat α 0] {β : Type} (go : β → α → α) (moves : Vector β l) (i: Fin l.succ)
: α
  := List.foldr go 0 (moves.1.take i)


def path₁ {α : Type} [OfNat α 0] {β : Type} (go : β → α → α) (moves : Fin l → β) (i: Fin l.succ)
: α
  := List.foldr go 0 (List.ofFn (λ j : Fin i ↦  (moves ⟨j.1, Fin.val_lt_of_le j (Fin.is_le i)⟩)))

def path₂ {α : Type} [OfNat α 0] {β : Type} (go : β → α → α) (moves : Fin l → β) (i: Fin l.succ)
: α
  := List.foldl (λ x y ↦ go y x) 0 (List.ofFn (λ j : Fin i ↦  (moves ⟨j.1, Fin.val_lt_of_le j (Fin.is_le i)⟩)))

-- def path₂ {α : Type} [OfNat α 0] {β : Type} (go : β → α → α) :
-- (moves : Fin l → β) → Fin l.succ → α := by
--   induction l
--   intro
--   exact 0
--   intro moves
--   let firstMoves := Fin.init moves
--   let lastMove := moves (Fin.last n)
--   -- exact Fin.cons (go lastMove (n_ih firstMoves (Fin.last n))) (n_ih firstMoves)
--   exact Matrix.vecCons (go lastMove (n_ih firstMoves (Fin.last n))) (n_ih firstMoves)
#eval path₁ rect  ![0,0,1,1]
#eval path₂ rect  ![0,0,1,1] -- wrong!

def pathEnrico {σ μ : Type} [Zero σ] {n : ℕ} (update : μ → σ → σ) (μs : Fin n → μ) : Fin (n+1) → σ :=
match n with
| 0 => ![0]
| n+1 =>
let init := pathEnrico update (Fin.init μs)
Fin.snoc init (update (μs n) (init n))

#eval pathEnrico rect ![0,0,1,1]

-- def path₁ {l:ℕ} {α : Type} [OfNat α 0] {β : Type} (go : β → α → α) (moves : Fin l → β) :=
-- path₀ go (List.ofFn moves)



def mymoves : Fin 6 → Fin 4 := ![0,2,1,0,1,2]
-- #eval mymoves ⟨0,by linarith⟩
-- #eval List.map (morF'' rect_hex_embedding rect mymoves) [0,1,2,3,4,5]
-- #eval List.map (morF rect_hex_embedding rect mymoves) [0,1,2,3,4,5]

def mymoves' : Fin 6 → Fin 3 := ![0,2,1,0,1,2]
-- #eval List.map (morF'' tri_rect_embedding tri mymoves') [0,1,2,3,4,5]

-- this is promising

-- #eval "pause"


-- #eval List.map (pathF rect ![0,0,1,0,0]) [0,1,2,3,4,5,6]
-- #eval List.map (pathF' rect ![0,0,1,0,0]) [0,1,2,3,4,5,6]


-- Extend a map on moves to lists:
def morph {α:Type} [OfNat α 0] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
(go₀ : Fin b₀ → α → α) (l : List (Fin b₀)) : List (Fin b₁) := by
  induction l with
  |nil => exact []
  |cons head tail tail_ih =>
    exact (f head (path go₀ tail).head) :: tail_ih

-- morph is length-preserving:
theorem morph_len {α:Type} [OfNat α 0] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
(go₀ : Fin b₀ → α → α) (l : List (Fin b₀)) :
(morph f go₀ l).length = l.length := by
  induction l
  . unfold morph; rfl
  . rename_i head tail tail_ih
    unfold morph; repeat (rw [List.length_cons])
    simp only [Nat.succ.injEq];
    rw [← tail_ih]; congr

def morphᵥ {l:ℕ}
  {α:Type} [OfNat α 0] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
  (go₀ : Fin b₀ → α → α) (v : Vector (Fin b₀) l)
  : Vector (Fin b₁) l := ⟨morph f go₀ v.1, by rw [morph_len];exact v.2⟩

def morf {l:ℕ}
  {α:Type} [OfNat α 0] {b₀ b₁ : ℕ} (f : Fin b₀ → Fin b₁)
   (v : Vector (Fin b₀) l)
  : Vector (Fin b₁) l := Vector.map f v

def morfF {l:ℕ} -- Here, "f" means: f doesn't depend on space. "F" means: use Fin not Vector
  -- 3/10/24. Hopefully simple enough to prove a lot about it.
  {α:Type} [OfNat α 0] {b₀ b₁ : ℕ} (f : Fin b₀ → Fin b₁)
   (v : Fin l → (Fin b₀))
  : Fin l → (Fin b₁) := λ i ↦ f (v i) --sorry --Vector.map f v

def morf_list
  {α:Type} [OfNat α 0] {b₀ b₁ : ℕ} (f : Fin b₀ → Fin b₁)
   (v : List (Fin b₀))
  : List (Fin b₁) := List.map f v

theorem morf_len {α:Type} [OfNat α 0] {b₀ b₁ : ℕ} (f : Fin b₀ → Fin b₁)
(l : List (Fin b₀)) :
(morf_list f l).length = l.length := by
  induction l; unfold morf_list; rfl; unfold morf_list; repeat (rw [List.length_cons])
  simp; -- finished March 8, 2024


abbrev σ {l:ℕ}
  {α:Type} [OfNat α 0] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
  (go₀ : Fin b₀ → α → α) (v : Vector (Fin b₀) l)  := morphᵥ f go₀ v

theorem nearby_of_embeds {α:Type} [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
 {x y : α} (hn : nearby go₀ x y):
nearby go₁ x y := by
  unfold nearby at hn; simp only [decide_eq_true_eq] at hn ;
  obtain ⟨a,ha⟩ := hn
  let Q := h_embed a x
  unfold nearby; simp only [decide_eq_true_eq]; rw [ha]; tauto


theorem pt_loc_of_embeds
 {α:Type} [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
 {l:ℕ}
  (fold : Vector α l) (a b : Fin l) (phobic : Vector Bool l)
  (htri: pt_loc go₀ fold a b phobic) :
         pt_loc go₁ fold a b phobic := by
  unfold pt_loc at *;
  simp only [Bool.and_eq_true, decide_eq_true_eq] at *;
  constructor; tauto; exact nearby_of_embeds h_embed htri.2


theorem pts_at_of_embeds' {α:Type} [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
{l:ℕ} (k:Fin l) (ph : Vector Bool l) (fold : Vector α l):
pts_at' go₀ k ph fold ≤
pts_at' go₁ k ph fold := by
  unfold pts_at'; apply Finset.card_le_card; intro a ha;
  simp only [Finset.mem_filter,
    Finset.mem_univ, true_and]; simp only [Finset.mem_filter, Finset.mem_univ,
      true_and] at ha
  exact pt_loc_of_embeds h_embed fold a k ph ha


open BigOperators


def pts_tot' {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
 {l:ℕ} (ph : Vector Bool l)(fold : Vector α l)
  := ∑ i : Fin l, pts_at' go i ph fold

/-- This is needed to get the Handshake Lemma bound from Agarwal et al.'s paper,
  but it is also just a nicer definition.-/
def points_tot -- March 13, 2024
{α β : Type} [DecidableEq α] [Fintype β] (go : β → α → α)
{l:ℕ} (ph : Vector Bool l) (fold : Vector α l)
:= Finset.card (
  Finset.filter
  (λ ik : (Fin l) × (Fin l) ↦ ((pt_loc go fold ik.1 ik.2 ph): Prop))
  (Finset.univ)
)   -- think "ik = (i,k)"


-- In order to use the handshaking lemma from
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/DegreeSum.html#SimpleGraph.sum_degrees_eq_twice_card_edges
-- Bonds:
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Dart.html#SimpleGraph.Dart
-- we may introduce this:
-- note that we form a graph on the amino acids rather than on the ambient space.

def SuccGraph {l:ℕ} : SimpleGraph (Fin l.succ) := {
  Adj := λ i j ↦ i.1 = j.1.succ ∨ j.1 = i.1.succ
  symm := λ i j h ↦ by simp only;simp only at h ;tauto
  loopless := λ i ↦ by simp only [or_self];exact Nat.ne_of_lt (Nat.lt.base i.1)
}
-- def NearbyGraph
--  {α:Type} {β : Type} [Fintype β] (go : β → α → α)
-- [DecidableEq α] {l:ℕ} (fold : Vector α l.succ)
--  : SimpleGraph (Fin l.succ) := {
--   Adj := λ i j ↦ nearby go (fold.get i) (fold.get j)
--   symm := λ i j h ↦ by sorry
--   loopless := λ i ↦ by sorry
-- }

def ProteinGraph₀ {α:Type} {β : Type} [Fintype β] (go : β → α → α)
[DecidableEq α] {l:ℕ} (ph : Vector Bool l.succ) (fold : Vector α l.succ)
: SimpleGraph (Fin l.succ) := {
  Adj := λ i j ↦ (pt_loc go fold i j ph) ∨ (pt_loc go fold j i ph)
-- phobic.get i && phobic.get j && (i.1.succ < j.1 ∨ j.1.succ < i.1) && nearby go (fold.get i) (fold.get j)
-- then we can relate it to a graph structure by which i, i.succ are connected.
  symm := by
    intro _ _ h;cases h with
    |inl => right;tauto
    |inr => left;tauto
  loopless := by
    intro i hi;unfold pt_loc at hi; simp only [Bool.and_self, Bool.and_eq_true,
      decide_eq_true_eq, or_self] at hi ;have : i.1.succ < i.1 := by tauto
    contrapose this;exact Nat.not_succ_lt_self
}
-- def ProteinGraph₁ {α:Type} {β : Type} [Fintype β] (go : β → α → α)
-- [DecidableEq α] {l:ℕ} (ph : Vector Bool l.succ) (fold : Vector α l.succ)
-- : SimpleGraph (Fin l.succ) := {
--   Adj := λ i j ↦ ph.get i ∧ ph.get j ∧ (i.1.succ < j.1 ∨ j.1.succ < i.1) ∧ nearby go (fold.get i) (fold.get j)
--   symm := by
--     sorry
--   loopless := by
--     sorry
-- }
-- def ProteinGraph₂ {α:Type} {β : Type} [Fintype β] (go : β → α → α)
-- [DecidableEq α] {l:ℕ} (ph : Vector Bool l.succ) (fold : Vector α l.succ)
-- : SimpleGraph (Fin l.succ) := {
--   Adj := λ i j ↦ ph.get i ∧ ph.get j ∧ ¬ SuccGraph.Adj i j ∧ (NearbyGraph go fold).Adj i j
--   -- more elegant as (NearbyGraph go).Adj (fold.get i) (fold.get j)
--   -- then the "NearbyGraph" is interchangeable with go itself.
--   -- the construction is almost that of a Cayley graph
--   -- and pathᵥ or whatever is a SimpleGraph.Walk
--   symm := by
--     sorry
--   loopless := by
--     sorry
-- }



def slicer {l: ℕ} (P : (Fin l) → (Fin l) → Bool) : Fin l → Finset (Fin l × Fin l)
:= fun k => Finset.filter (fun ik => ik.2 = k ∧ P ik.1 k = true) Finset.univ

lemma slicer_disjointness {l: ℕ} (P : (Fin l) → (Fin l) → Bool)
: ∀ k₁ ∈ Finset.univ, ∀ k₂ ∈ Finset.univ, k₁ ≠ k₂ → Disjoint (slicer P k₁) (slicer P k₂)
:= by
      intro k₁;intro;intro k₂;intro;intro hk₁₂ A hA₁ hA₂ ik hikA
      have : ik ∈ slicer P k₁ := by exact hA₁ hikA
      have h₁: ik.2 = k₁ ∧ P ik.1 k₁ = true := by
        unfold slicer at this;
        simp only [Finset.mem_filter,
        Finset.mem_univ, true_and] at this ;exact this
      have : ik ∈ slicer P k₂ := by exact hA₂ hikA
      have h₂: ik.2 = k₂ ∧ P ik.1 k₂ = true := by
        unfold slicer at this;simp only [Finset.mem_filter, Finset.mem_univ,
          true_and] at this ;exact this
      have : k₁ = k₂ := by exact Eq.trans h₁.1.symm h₂.1
      exfalso; exact hk₁₂ this

lemma slicer_card
{l: ℕ}
(P: Fin l → Fin l → Bool)
: ∀ (x : Fin l),
  Finset.card (Finset.filter (fun ik : Fin l × Fin l => ik.2 = x ∧ P ik.1 x = true) Finset.univ) =
    Finset.card (Finset.filter (fun i_1 : Fin l => P i_1 x = true) Finset.univ)
:= by
    intro x;repeat rw [← Fintype.card_coe];simp only [Finset.mem_filter,
      Finset.mem_univ, true_and]
    let f : {ik : Fin l × Fin l // ik.2 = x ∧ P ik.1 x} → { i_1 : Fin l // P i_1 x}
      := λ ik ↦ ⟨ik.1.1, ik.2.2⟩
    have : Function.Bijective f := by
      constructor;intro x y hxy;
      simp only [Subtype.mk.injEq] at hxy
      have : x.1 = y.1 := by apply Prod.ext;exact hxy;rw [x.2.1,y.2.1]
      exact SetCoe.ext this;intro y;exists ⟨⟨y.1,x⟩,by
        simp only [true_and];
        exact y.2⟩
    apply Fintype.card_of_bijective this

/-- Write `points_tot` as a disjoint union over `ik.2` to prove.-/
theorem pts_tot'_eq_points_tot -- March 14, 2024
{α:Type} {β : Type} [Fintype β] (go : β → α → α)
[DecidableEq α] {l:ℕ} (ph : Vector Bool l) (fold : Vector α l)
:
points_tot go ph fold = pts_tot' go ph fold := by
  unfold pts_tot' points_tot pts_at'
  let P := (λ ik1 k ↦ pt_loc go fold ik1 k ph)
  let t := λ k ↦
    (Finset.filter (λ ik : (Fin l) × (Fin l) ↦
      ik.2 = k ∧ P ik.1 k) Finset.univ)
  have : t = slicer P := rfl
  have hDU: Finset.card (Finset.biUnion Finset.univ (slicer P)) = ∑ k : Fin l,
            Finset.card ((slicer P) k) := Finset.card_biUnion (slicer_disjointness P)
  rw [← this] at hDU
  let Q := Finset.sum_congr rfl (λ x : Fin l ↦ λ _ : x ∈ Finset.univ ↦ slicer_card P x)
  rw [← Q,← hDU]
  congr;apply Finset.ext;simp


theorem pts_bound_of_embeds' {α:Type} [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
{l:ℕ} (ph : Vector Bool l) (fold : Vector α l):
pts_tot' go₀ ph fold ≤
pts_tot' go₁ ph fold := by
  unfold pts_tot'; apply Finset.sum_le_sum; intros; exact pts_at_of_embeds' h_embed _ _ _



def pts_at_improved {α:Type} {β : Type} [Fintype β] (go : β → α → α)
[DecidableEq α] {l:ℕ} (k : Fin l) (ph : Vector Bool l) (fold : Vector α l) : ℕ :=
  Finset.card (
    Finset.filter (λ i : Fin k.1.pred ↦ (pt_loc go fold (Fin_trans'' i) k ph))
    Finset.univ
  )


theorem pts_at_eq_pts_at'_improved  {α:Type} {β : Type} [Fintype β] (go : β → α → α)
[DecidableEq α] {l:ℕ} (k : Fin l) (ph : Vector Bool l) (fold : Vector α l):
pts_at_improved go k ph fold = pts_at' go k ph fold :=
  by
    unfold pts_at_improved pts_at';
    (repeat rw [← Fintype.card_coe]);
    exact (change_type_card_improved go k ph fold).symm


lemma pts_at_bound'_improved {α:Type} [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α)
{l:ℕ} (ph : Vector Bool l) (fold : Vector α l) (i:Fin l):
pts_at' go i ph fold ≤ i.1.pred := by -- can make this i.pred I think
  rw [← pts_at_eq_pts_at'_improved, ← Finset.card_fin i.1.pred];
  unfold pts_at_improved
  apply Finset.card_le_card;
  apply Finset.filter_subset

lemma Fin_sum_range (i : ℕ)  :
∑ j : Fin (i+1), j.1 = i.succ * i / 2
 := by
  let Q := Finset.sum_range_id i.succ;
  simp only [Nat.succ_sub_succ_eq_sub, tsub_zero] at Q ;
  rw [← Q]; exact (Finset.sum_range fun i => i).symm

lemma Fin_sum_range_pred (i : ℕ)  : -- April 2, 2024
∑ j : Fin (i+1), j.1.pred = i * (i-1) / 2
 := by
  let Q := sum_pred i
  rw [← Q]
  exact Fin.sum_univ_eq_sum_range Nat.pred (i + 1)

theorem pts_earned_bound_loc'_improved
{α:Type} [DecidableEq α] {β : Type} [Fintype β] (go : β → α → α)
{l:ℕ} (ph : Vector Bool l.succ) (fold : Vector α l.succ):
pts_tot' go ph fold ≤ l * l.pred / 2 := by
  suffices pts_tot' go ph fold ≤ ∑ j : Fin l.succ, j.1.pred by calc
    _ ≤ ∑ j : Fin l.succ, j.1.pred := this
    _ = _                          := Fin_sum_range_pred _
  unfold pts_tot'; apply Finset.sum_le_sum; intro i; intro;
  exact pts_at_bound'_improved go ph fold i

/-- The result `pts_earned_bound_loc'_improved` is sharp in that for `l=2`,
we have words of length `3` and the points bound is `1`,
which does in fact happen for hex fold. -/
theorem when_zero -- April 2, 2024
{α:Type} [DecidableEq α] {β : Type} [Fintype β] (go : β → α → α)
{l:ℕ} (ph : Vector Bool l.succ) (fold : Vector α l.succ):

  ph.length ≤ 2 → pts_tot' go ph fold = 0

  := by
  intro h
  have : l = 0 ∨ l = 1 := by
    cases Nat.lt_or_eq_of_le (Nat.lt_succ.mp h)
    . left;linarith
    . tauto
  let Q := pts_earned_bound_loc'_improved go ph fold
  cases this
  . rename_i h_1
    subst h_1
    simp only [Nat.pred_zero, mul_zero, Nat.zero_div, nonpos_iff_eq_zero] at Q
    exact Q
  . rename_i h_1
    subst h_1
    simp only [Nat.pred_succ, mul_zero, Nat.zero_div, nonpos_iff_eq_zero] at Q
    exact Q


lemma path_len {α: Type} [OfNat α 0] [DecidableEq α] {β: Type}
(go: β → α → α) {l: ℕ} (moves: Vector β l)
: (path go moves.1).1.length = l.succ
:= by rw [(path go moves.1).2]; simp



lemma path_at_len {α: Type} (base :α) [DecidableEq α] {β: Type}
(go: β → α → α) {l: ℕ} (moves: Vector β l)
: (path_at base go moves.1).1.length = l.succ
:= by rw [(path_at base go moves.1).2]; simp


def pathᵥ {l:ℕ}{α:Type} [OfNat α 0] [DecidableEq α] {β : Type} (go : β → α → α)
(moves : Vector β l) : Vector α l.succ := ⟨(path go moves.1).1,path_len _ _⟩

abbrev π  {l:ℕ}{α:Type} [OfNat α 0] [DecidableEq α] {β : Type}  (go : β → α → α)
(moves : Vector β l) := pathᵥ go moves

lemma pathᵥ_len {α: Type} [OfNat α 0] [DecidableEq α] {β: Type}
(go: β → α → α) {l: ℕ} (moves: Vector β l)
: (pathᵥ go moves).length = l.succ := by simp

def pathᵥ_at {l:ℕ}{α:Type} (base : α) [DecidableEq α] {β : Type} (go : β → α → α)
(moves : Vector β l) : Vector α l.succ := ⟨(path_at base go moves.1).1,path_at_len _ _ _⟩

def pt_dir {α:Type} [OfNat α 0] [DecidableEq α] {β : Type} (go : β → α → α)
 {l:ℕ} (j : Fin l.succ) (moves: Vector β l) (ph : Vector Bool l.succ)
: β → Fin l.succ → Prop  := λ a i ↦
  ph.get i ∧ ph.get j ∧ i.1.succ < j ∧ (pathᵥ go moves).get j = go a ((pathᵥ go moves).get i)



theorem unique_loc  {α: Type} [OfNat α 0] [DecidableEq α] {β: Type} [Fintype β]
  {go: β → α → α}
  {l:ℕ} {j: Fin l.succ}
  {moves: Vector β l} {ph : Vector Bool l.succ}
  (path_inj: Function.Injective (λ k : Fin l.succ ↦ (pathᵥ go moves).get k))
  (right_inj: right_injective go) (a : β) (i₀ i₁ : Fin l.succ)
  (hai₀ : pt_dir go j moves ph a i₀)
  (hai₁ : pt_dir go j moves ph a i₁)
  :
  i₀ = i₁
  := path_inj (right_inj a (Eq.trans hai₀.2.2.2.symm hai₁.2.2.2))



theorem unique_dir {α: Type} [OfNat α 0] [DecidableEq α] {β: Type} [Fintype β]
  {go: β → α → α} {l:ℕ} (j: Fin l.succ)
  (moves: Vector β l) (ph : Vector Bool l.succ)
  (left_inj : left_injective go)

  (i : Fin l.succ) (a₀ a₁ : β)
  (hai₀ : pt_dir go j moves ph a₀ i)
  (hai₁ : pt_dir go j moves ph a₁ i)
  : a₀ = a₁
  := left_inj ((pathᵥ go moves).get i) ((Eq.trans hai₀.2.2.2.symm hai₁.2.2.2))

theorem unique_loc_dir {α: Type} [OfNat α 0] [DecidableEq α] {β: Type} [Fintype β]
{go: β → α → α} {l:ℕ} {j: Fin l.succ}
  {moves: Vector β l} {ph : Vector Bool l.succ}
  (path_inj: Function.Injective (λ k : Fin l.succ ↦ (pathᵥ go moves).get k))
  (right_inj: right_injective go)
  (left_inj : left_injective go)
  :
  (∀ (a : β) (i₀ i₁ : Fin l.succ) (_ : pt_dir go j moves ph a i₀) (_ : pt_dir go j moves ph a i₁),
  i₀ = i₁)
  ∧
  (∀ (i : Fin l.succ) (a₀ a₁ : β)
  (_ : pt_dir go j moves ph a₀ i)
  (_ : pt_dir go j moves ph a₁ i),
  a₀ = a₁
) := And.intro (unique_loc path_inj right_inj)
               (unique_dir j _ ph left_inj)



theorem left_injective_of_embeds_in_strongly {α: Type} [OfNat α 0] [DecidableEq α]
{b : ℕ}
{go₀ go₁ : Fin b → α → α}
(f: Fin b → α → Fin b)
(is_emb: is_embedding go₀ go₁ f)
(left_inj_emb : left_injective f) -- which we can prove for tri_rect_embedding although it's harder than left_injective_tri!
(left_inj_go: left_injective go₁)
:
left_injective go₀ := by
  intro x a₀ a₁ hxy
  simp only at hxy
  rw [is_emb a₀ x,is_emb a₁ x] at hxy
  exact left_inj_emb x (left_inj_go x hxy)


theorem unique_loc_dir_rect {l:ℕ} (j: Fin l.succ) -- location, direction
  (moves: Vector (Fin 4) l) (ph : Vector Bool l.succ)
  (path_inj: Function.Injective (λ k : Fin l.succ ↦ (pathᵥ rect moves).get k)):
  (∀ (a : Fin 4) (i₀ i₁ : Fin l.succ) (_ : pt_dir rect j moves ph a i₀) (_ : pt_dir rect j moves ph a i₁),
  i₀ = i₁) ∧ (  ∀ (i : Fin l.succ) (a₀ a₁ : Fin 4)
  (_ : pt_dir rect j moves ph a₀ i)
  (_ : pt_dir rect j moves ph a₁ i),
  a₀ = a₁
) :=  unique_loc_dir path_inj right_injective_rect left_injective_rect



theorem unique_loc_dir_hex {l:ℕ} (j: Fin l.succ)
  (moves: Vector (Fin 6) l) (ph : Vector Bool l.succ)
  (path_inj: Function.Injective (λ k : Fin l.succ ↦ (pathᵥ hex moves).get k)):
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
        Vector.get (pathᵥ go moves) j = go a (Vector.get (pathᵥ go moves) i)) (by
          unfold pt_dir;tauto
        )


theorem pts_at'_dir {α: Type} [OfNat α 0] [DecidableEq α] {b:ℕ}
{go: Fin b → α → α}
  {l:ℕ} (j : Fin l.succ) (ph : Vector Bool l.succ)
  (moves: Vector (Fin b) l)
  (path_inj : (Function.Injective fun k => Vector.get (pathᵥ go moves) k))
  (right_inj: right_injective go)
  (left_inj: left_injective go)
  : pts_at' go j ph (pathᵥ go moves) ≤ b := by
    unfold pts_at'
    have : Finset.filter (
        λ i : Fin (Nat.succ l) ↦ (∃ a, pt_dir go j moves ph a i)) Finset.univ =
          Finset.filter (
        λ i : Fin (Nat.succ l) ↦  pt_loc go (pathᵥ go moves) i j ph) Finset.univ
    := by
      apply Finset.ext;intro i;repeat (rw [Finset.mem_filter])
      simp only [Finset.mem_univ, true_and]
      unfold pt_dir pt_loc nearby;
      simp only [exists_and_left, Bool.and_eq_true, decide_eq_true_eq];
      tauto
    rw [← this,← choice_ex_finset_card (unique_loc_dir path_inj right_inj left_inj)]
    apply card_finset_fin_le


/-- Almost obsolete, except for `rect₃` fold which is not symmetric so that Handshake Lemma
reasoning does not apply. -/
theorem pts_earned_bound_dir' {α: Type} [OfNat α 0] [DecidableEq α] {b:ℕ}
{go: Fin b → α → α}
{l:ℕ} (ph : Vector Bool l.succ)
(moves: Vector (Fin b) l)
(path_inj  : (Function.Injective fun k => Vector.get (pathᵥ go moves) k))
(right_inj : right_injective go)
(left_inj  : left_injective go)
: pts_tot' go ph (pathᵥ go moves) ≤ l.succ * b := by
  suffices pts_tot' go ph (pathᵥ go moves) ≤ Finset.sum (Finset.univ : Finset (Fin l.succ)) (λ _ ↦ b) by
    simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul] at this ;
    tauto
  apply Finset.sum_le_sum; intro i; intro
  exact pts_at'_dir i ph moves path_inj right_inj left_inj

theorem independence_in_symmetric_pts_earned_bound_dir'₁ :
  ∃ (α β : Type) (_ : Fintype β) (_: DecidableEq α), ∃ go : β → α → α,
  right_injective go ∧ left_injective go ∧ ¬ Symmetric (λ x y ↦ nearby go x y) := by
  exists ℤ×ℤ;exists Fin 3;exists (inferInstance);exists (inferInstance);exists rect₃
  constructor;exact right_injective_rect₃;constructor;exact left_injective_rect₃
  intro hc;have : nearby rect₃ (0,0) (0,1) := by decide
  let Q := hc this
  simp only at Q ;unfold nearby at Q;
  simp only [decide_eq_true_eq] at Q ;contrapose Q;decide

def f_dni : Fin 2 × Fin 2 → Fin 2
| ⟨0,0⟩ => 0
| ⟨0,1⟩ => 0
| ⟨1,0⟩ => 1 -- "does not imply"
| ⟨1,1⟩ => 0

def g : Fin 2 → Fin 2 → Fin 2 := λ x y ↦ f_dni ⟨x,y⟩
instance : Decidable (Symmetric fun x y => nearby g x y = true) := by
  unfold Symmetric;unfold nearby;exact inferInstance

instance : Decidable (left_injective g) := by
  unfold left_injective;exact inferInstance

instance : Decidable (right_injective g) := by
  unfold right_injective;exact inferInstance

-- #eval Symmetric (λ x y ↦ nearby g x y) ∧ ¬ right_injective g ∧ ¬ left_injective g

-- This is the first example I thought of that has a Symmetric nearby function,
-- but is neither left nor right injective.
def ctrex : (Fin 2 → Fin 2) → Fin 2 → Fin 2 := λ f x ↦ f x

theorem independence_in_symmetric_pts_earned_bound_dir'₂ :
  ∃ (α β : Type) (_ : Fintype β) (_: DecidableEq α), ∃ go : β → α → α,
  ¬ right_injective go ∧ ¬ left_injective go ∧ Symmetric (λ x y ↦ nearby go x y) := by
  exists Fin 2;exists Fin 2 → Fin 2;exists (inferInstance);exists (inferInstance);exists ctrex
  constructor;unfold right_injective;intro hc
  have : (λ _ : Fin 2 ↦ (0:Fin 2)) 0 = (λ _ : Fin 2 ↦ (0:Fin 2)) 1  := rfl
  let Q := hc (λ _ ↦ 0);unfold Function.Injective at Q;
  simp only at Q
  let R := @hc 0 0 1 rfl;exact Fin.zero_ne_one R;constructor
  intro hc;unfold left_injective at hc;let Q := hc 0;unfold Function.Injective at Q;let R := @Q (λ x ↦ x) (λ _ ↦ 0) rfl
  simp only at R
  have : ∀ y : Fin 2, y = 0 := by
    intro y;calc
    y = (λ x ↦ x) y := rfl
    _ = (λ x ↦ 0) y := congrArg (λ f ↦ f y) R
    _ = 0 := rfl
  have : 1 = 0 := this 1;symm at this;contrapose this;exact Fin.zero_ne_one;unfold Symmetric
  intro a b;intro;unfold nearby;simp only [decide_eq_true_eq];exists (λ _ ↦ a)




theorem pts_earned_bound' {α: Type} [OfNat α 0] [DecidableEq α] {b:ℕ}
{go: Fin b → α → α}
{l:ℕ} (ph : Vector Bool l.succ)
(moves: Vector (Fin b) l)
(path_inj : (Function.Injective fun k => Vector.get (pathᵥ go moves) k))
(right_inj : right_injective go)
(left_inj : left_injective go)

: pts_tot' go ph (pathᵥ go moves) ≤ min (l.succ * b) (l * l.pred / 2)
-- this is anyway obsolete since Handshake lemma gives another /2 factor
:= by
  suffices (
    pts_tot' go ph (pathᵥ go moves) ≤ l.succ * b
    ∧ pts_tot' go ph (pathᵥ go moves) ≤ l * l.pred / 2) by
    exact Nat.le_min.mpr this
  constructor
  exact pts_earned_bound_dir' ph moves path_inj right_inj left_inj
  exact pts_earned_bound_loc'_improved go ph (pathᵥ go moves)



theorem two_heads {α : Type} {k :ℕ} (v: Vector α k.succ) (w : List α) (hw : w ≠ [])
(h : v.1 = w) : Vector.head v = List.head w hw := by
  symm at h
  cases w
  . tauto
  . rename_i head tail
    simp only [List.head_cons]
    have : v = head ::ᵥ ⟨tail,by
      let v2 := v.2; rw [← h] at v2; simp only [List.length_cons,
      Nat.succ.injEq] at v2 ; tauto
    ⟩ := by
      apply Vector.eq; simp only [Vector.toList_cons, Vector.toList_mk]; rw [h]; rfl
    rw [this]; simp

theorem path_cons {α:Type} [OfNat α 0] [DecidableEq α] {b₀ : ℕ}
(go₀ : Fin b₀ → α → α)
(head : Fin b₀) (tail : List (Fin b₀))
   : (path go₀ (head ::        tail)).1 =
             ((go₀  head (path go₀ tail).head) :: (path go₀ tail).1) := rfl

theorem path_cons_vec {α:Type} [OfNat α 0] [DecidableEq α] {b₀ : ℕ}
(go₀ : Fin b₀ → α → α)
(head : Fin b₀) (tail : List (Fin b₀))
   : (path go₀ (head ::        tail)) =
             ((go₀  head (path go₀ tail).head) ::ᵥ (path go₀ tail)) := rfl


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

lemma plane_assoc (x y z : ℤ×ℤ) : x + (y+z) = (x+y)+z := by ring



-- #eval pathF' rect ![0,2] 2
-- #eval rect (![0,2] 1) (pathF' rect ![0,2] 1)

-- #eval pathF' rect ![0,2] 1
-- #eval rect (![0,2] 0) (pathF' rect ![0,2] 0)





theorem orderly_injective_helper {β:Type} (x : ℕ → β)
  (a b : β) (hab: a ≠ b)
  (h₀ : x 0 = a)
  (j:ℕ) (hj : ∃ i, i < j ∧ x i.succ = b)
  (h₂: ∀ i, i < j → x i = a ∨ x i = b)
  [DecidablePred fun n => n < j ∧ x (Nat.succ n) = b]
  :
  (∃ i, i < j ∧ x i = a ∧ x i.succ = b) := by
  exists (Nat.find hj);let Q := Nat.find_spec hj
  constructor;exact Q.1;constructor;let R := h₂ (Nat.find hj) Q.1
  cases R;
  rename_i h
  exact h;exfalso
  have : (Nat.find hj) ≠ 0 := by
    intro hc;rw [← hc] at h₀;rename_i h;have : a = b := Eq.trans h₀.symm h
    exact hab this
  obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero this
  have : Nat.find hj ≤ i := Nat.find_le (by
    constructor
    calc
      i < i.succ := Nat.lt.base i
      _ = Nat.find hj := hi.symm
      _ < j := Q.1
    rename_i h;rw [← hi];exact h
  )
  have : Nat.succ i ≤ i := Eq.trans_le (id hi.symm) this
  contrapose this;exact Nat.not_succ_le_self i;exact Q.2


theorem fin_fin {k:ℕ} {i:ℕ} {j:Fin k.succ} (h: i < j.1):
i < k := by
    calc
      _ < j.1 := h
      _ ≤ k := Fin.is_le j

theorem fin_fi {k:ℕ} {i:ℕ} {j:Fin k.succ} (h: i < j.1):
i < k.succ := by
    calc
      _ < j.1 := h
      _ ≤ k.succ := Fin.is_le'

theorem orderly_injective_helper₁ {β:Type} (k:ℕ) (x : (Fin k.succ) → β)
  (a b : β) (hab: a ≠ b)
  (h₀ : x 0 = a)
  (j:Fin k.succ) (hj : ∃ i, i.1 < j.1 ∧ x (Fin.succ i) = b)
  (h₂: ∀ i, i.1 < j.1 → x i = a ∨ x i = b)
  [DecidablePred fun n => ∃ (h : n < j.1), x (Fin.succ ⟨n, fin_fin h⟩) = b]
  :
    (∃ i : Fin k, i.1 < j.1 ∧ x (Fin.castSucc i) = a ∧ x (Fin.succ i) = b) := by
  have hthis: ∃ n:ℕ, ∃ h : n < j.1, x (Fin.succ ⟨n,fin_fin h⟩) = b := by
    obtain ⟨i,hi⟩ := hj;exists i.1;exists hi.1;exact hi.2
  have h : Nat.find hthis < j.1 := (Nat.find_spec hthis).1
  exists ⟨Nat.find hthis,fin_fin h⟩
  let h := (Nat.find_spec hthis).1
  constructor
  exact h
  constructor
  cases h₂ ⟨Nat.find hthis,fin_fi h
  ⟩ h
  rename_i h_1;exact h_1;rename_i h_1;exfalso
  have hthis₀: (⟨(Nat.find hthis),fin_fi h⟩ : Fin k.succ) ≠ 0 := by
    intro hc;
    rw [← hc] at h₀;
    have : a = b := Eq.trans h₀.symm h_1
    exact hab this
  have : Nat.find hthis ≠ 0 := by
    intro hc
    exact hthis₀ (Fin.ext hc)
  obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero this
  have : Nat.find hthis ≤ i := Nat.find_le (by
    constructor;
    simp only [Fin.succ_mk];
    simp_rw [← Nat.succ_eq_add_one,← hi];
    exact h_1
    calc
      i < i.succ          := Nat.lt.base i
      _ = Nat.find hthis  := hi.symm
      _ < j               := (Nat.find_spec hthis).1
  )
  have : Nat.succ i ≤ i := Eq.trans_le (id hi.symm) this
  contrapose this;exact Nat.not_succ_le_self i;exact (Nat.find_spec hthis).2

theorem orderly_injective_helper₂ (k:ℕ) (x : (Fin k.succ) → Fin 4)
  (h₀ : x 0 = 0)
  (j:Fin k.succ) (hj : ∃ i, i.1 < j.1 ∧ x (Fin.succ i) = 1)
  (h₂: ∀ i, i.1 < j.1 → x i = 0 ∨ x i = 1)
  :
  (∃ i : Fin k, i.1 < j.1 ∧ x (Fin.castSucc i) = 0 ∧ x (Fin.succ i) = 1)
  :=
  orderly_injective_helper₁ _ _ _ _ (Fin.zero_ne_one) h₀ _ hj h₂




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


lemma path_eq_path_morph {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
(go₀ : Fin b₀ → α → α) (go₁ : Fin b₁ → α → α)
(g : is_embedding go₀ go₁ f)
(moves : List (Fin b₀)):
  (path go₀ moves).1 = (path go₁ (morph f go₀ moves)).1 := by
    induction moves
    . unfold morph; simp only [List.length_nil]; repeat (rw [path_nil])
    rename_i head tail tail_ih
    rw [path_cons,g head (Vector.head (path go₀ tail)),tail_ih ]
    unfold morph; simp only [List.length_cons];
    rw [path_cons]; simp only [List.cons.injEq, and_true]
    have : (Vector.head (path go₀ tail))
         = (Vector.head (path go₁ (List.rec [] (fun head tail tail_ih => f head (Vector.head (path go₀ tail)) :: tail_ih) tail)))
    := by
      rw [two_heads (path go₀ tail) (path go₀ tail).1 (ne_nil_of_succ_length _) rfl]
      simp_rw [tail_ih]
      rw [two_heads]
      unfold morph
      simp
    exact congrArg _ this

lemma path_eq_path_morphᵥ {l:ℕ} {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
(go₀ : Fin b₀ → α → α) (go₁ : Fin b₁ → α → α)
(g : is_embedding go₀ go₁ f)
(moves : Vector (Fin b₀) l):
  (path go₀ moves.1).1 = (path go₁ (morphᵥ f go₀ moves).1).1 := by
  let Q := path_eq_path_morph f go₀ go₁ g moves.1
  rw [Q];unfold morphᵥ;simp

lemma pathᵥ_eq_path_morphᵥ1 {l:ℕ} {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
(go₀ : Fin b₀ → α → α) (go₁ : Fin b₁ → α → α)
(g : is_embedding go₀ go₁ f)
(moves : Vector (Fin b₀) l):
  (pathᵥ go₀ moves).1 = (pathᵥ go₁ (morphᵥ f go₀ moves)).1 := by
  let Q := path_eq_path_morphᵥ f go₀ go₁ g moves
  unfold pathᵥ
  rw [Q]

lemma pathᵥ_eq_path_morphᵥ {l:ℕ} {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
(go₀ : Fin b₀ → α → α) (go₁ : Fin b₁ → α → α)
(g : is_embedding go₀ go₁ f)
(moves : Vector (Fin b₀) l):
    pathᵥ go₀ moves
  = pathᵥ go₁ (morphᵥ f go₀ moves) := by

  let Q := pathᵥ_eq_path_morphᵥ1 f go₀ go₁ g moves
  exact Vector.eq (pathᵥ go₀ moves) (pathᵥ go₁ (morphᵥ f go₀ moves)) Q


def path_transformed {α: Type} [OfNat α 0] [DecidableEq α] {b₀ b₁: ℕ}
(f: Fin b₀ → α → Fin b₁) (go₀: Fin b₀ → α → α) (go₁: Fin b₁ → α → α)
(l: List (Fin b₀)) : Vector α l.length.succ :=
  ⟨
    (path go₁ (morph f go₀ l)).1,
    by rw [path_len go₁ ⟨morph f go₀ l, morph_len f go₀ l⟩]
  ⟩

def path_transformedᵥ {l:ℕ} {α: Type} [OfNat α 0] [DecidableEq α] {b₀ b₁: ℕ}
(f: Fin b₀ → α → Fin b₁) (go₀: Fin b₀ → α → α) (go₁: Fin b₁ → α → α)
(v: Vector (Fin b₀) l) : Vector α l.succ :=
    pathᵥ go₁ (morphᵥ f go₀ v)


/- Finished February 10, 2024:
When transforming, the underlying path in say ℤ×ℤ is unchanged.
-/
theorem transform_of_embed {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁)
(go₀ : Fin b₀ → α → α) (go₁ : Fin b₁ → α → α)
 (l : List (Fin b₀)) (h_embed: is_embedding go₀ go₁ f):
 path_transformed f go₀ go₁ l = path go₀ l
:= by
  apply SetCoe.ext; unfold path_transformed; simp only;
  unfold is_embedding at h_embed;
  induction l;
  . simp only [List.length_nil];
    unfold morph;
    simp only [List.length_nil]
    rfl
  rename_i head tail tail_ih
  have morph_cons : (morph f go₀ (head :: tail)) = (f head ((path go₀ tail).head)) :: (morph f go₀ (tail)) := rfl
  rw [morph_cons];
  repeat (rw [path_cons])
  simp only [List.cons.injEq]
  constructor
  let a := (Vector.head (path go₀ tail))
  rw [h_embed head a]
  simp only
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
    obtain ⟨a,ha⟩ := hau
    obtain ⟨u,hu⟩ := ha
    rw [hu]; simp only [Vector.cons_val, Vector.head_cons]; rfl
  . exact congr_arg _ this
  . rw [tail_ih]


def pts_tot_bound {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) (q : ℕ) :=
∀ moves : Vector β l,
Function.Injective (λ k ↦ (path go moves.1).1.get k)
→
pts_tot' go ph (⟨(path go moves.1).1,path_len _ _⟩) ≤ q

-- def myList {b l:ℕ} := Finset.toList (Finset.univ : Finset (Vector (Fin b) l))
-- Finset.toList is not computable!

-- The following version of pts_tot_bound is correct even for the asymmetric 3-move version of rect:
def pts_tot_bound_rev {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) (q : ℕ) :=
∀ moves : Vector β l,
Function.Injective (λ k ↦ (path go moves.1).1.get k)
→
pts_tot' go ph (⟨(path go moves.1).1.reverse,by
  rw [List.length_reverse]
  exact path_len _ _
⟩) ≤ q


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

instance {α:Type} [OfNat α 0] [DecidableEq α] {β : Type} [Fintype β]
(go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) (q : ℕ):
DecidablePred (pts_tot_bound_rev go moves)
:= by
  unfold pts_tot_bound_rev pts_tot'
  exact inferInstance

instance {α:Type} [OfNat α 0] [DecidableEq α] {β : Type} [Fintype β]
(go : β → α → α) : DecidablePred fun n => pts_tot_bound_rev go ph n :=
  by
  unfold pts_tot_bound_rev pts_tot'
  exact inferInstance

theorem pts_tot_bound_rev_exists {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β] (go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) :
∃ q, pts_tot_bound_rev go ph q := by
  exists l * l.pred / 2; intro moves
  let Q := pts_earned_bound_loc'_improved go ph (⟨(path go moves.1).1.reverse,by
    rw [List.length_reverse]
    exact path_len _ _
  ⟩)
  tauto


theorem pts_tot_bound_exists {α:Type} [OfNat α 0] [DecidableEq α]
{β : Type} [Fintype β] (go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) :
∃ q, pts_tot_bound go ph q := by
  exists l * l.pred / 2; intro moves
  let Q := pts_earned_bound_loc'_improved go ph (⟨(path go moves.1).1,path_len _ _⟩)
  tauto

/- HP is the HP protein folding model "objective function" or "value function": -/
def HP {α:Type} [OfNat α 0] [DecidableEq α] {β : Type} [Fintype β]
(go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) :ℕ := Nat.find (pts_tot_bound_exists go ph)
/- ph has to be of succ type because there will at least be an amino acid at the origin. -/

/-- For nonsymmetric "nearby" relations we must use this version.-/
def HP_rev {α:Type} [OfNat α 0] [DecidableEq α] {β : Type} [Fintype β]
(go : β → α → α) {l:ℕ} (ph : Vector Bool l.succ) :ℕ := Nat.find (pts_tot_bound_rev_exists go ph)


def P_tri'  {l:ℕ} := λ ph : Vector Bool l.succ ↦ HP tri  ph
def P_rect' {l:ℕ} := λ ph : Vector Bool l.succ ↦ HP rect ph
def P_rect₃' {l:ℕ} := λ ph : Vector Bool l.succ ↦ HP_rev rect₃ ph
def P_hex'  {l:ℕ} := λ ph : Vector Bool l.succ ↦ HP hex  ph
-- Is P_rect₃' ≥ P_tri' ?


-- #eval pt_loc rect₃ ⟨[(0,0),(1,0),(1,1),(0,1)],rfl⟩ (0:Fin 4) (3:Fin 4) ⟨[true,false,false,true],rfl⟩
-- #eval pts_tot' rect₃ ⟨[true,false,false,true],rfl⟩ ⟨[(0,0),(1,0),(1,1),(0,1)],rfl⟩
-- #eval pts_tot' rect₃ ⟨[true,false,false,true],rfl⟩ ⟨[(0,0),(1,0),(1,1),(0,1)].reverse,rfl⟩
-- #eval pts_tot' rect₃ ⟨[true,false,false,true],rfl⟩ (path rect₃ [1,2,0])
-- #eval (path rect₃ [1,2,0])
-- #eval P_rect₃' ⟨[true,true,true,true,true,true,true],rfl⟩

-- #eval pts_tot' rect ⟨[true,false,false,true,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,true],rfl⟩ ⟨[2,0,3,0,3,1,3,0,0,2,2,2,2,1,1,1,1,3,3,1,3,0,3,0,2],rfl⟩

theorem vector_inj_of_list_inj {t : Type} {n : ℕ}
{v : Vector t n} (h: Function.Injective fun k => List.get v.1 k) :
Function.Injective fun k => Vector.get v k := by
  intro x y hxy;unfold Function.Injective at *;simp only at hxy
  have hx: x.1 < v.1.length := by
    let Q := x.2;have : v.1.length = n := v.2;simp_rw [← this] at Q;exact Q
  have hy: y.1 < v.1.length := by
    let Q := y.2;have : v.1.length = n := v.2;simp_rw [← this] at Q;exact Q
  have : List.get v.1 ⟨x.1,hx⟩ = List.get v.1 ⟨y,hy⟩ := by exact hxy
  let Q := h this; simp only [Fin.mk.injEq] at Q ;exact Fin.ext Q


theorem list_inj_of_vector_inj {t : Type} {n : ℕ}
{v : Vector t n} (h: Function.Injective fun k => Vector.get v k) :
Function.Injective fun k => List.get v.1 k := by
  intro x y hxy;unfold Function.Injective at *
  have : Vector.get ⟨v.1,rfl⟩ x = Vector.get ⟨v.1,rfl⟩ y := by exact hxy
  have hx: x.1 < n := by
    let Q := x.2;have : v.1.length = n := v.2;simp_rw [this] at Q;exact Q
  have hy: y.1 < n := by
    let Q := y.2;have : v.1.length = n := v.2;simp_rw [this] at Q;exact Q
  have : Vector.get v ⟨x.1,hx⟩ = Vector.get v ⟨y.1,hy⟩ := by exact hxy
  let Q := h this; simp only [Fin.mk.injEq] at Q hxy ;exact Fin.ext Q

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
  exact pts_earned_bound_dir' _ _ (vector_inj_of_list_inj path_inj) right_injective_rect left_injective_rect

theorem value_bound_of_embeds_strongly {α:Type} [OfNat α 0] [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α}
{go₁ : Fin b₁ → α → α}    (h_embed : go₀    ≼    go₁)
{l:ℕ} (ph : Vector Bool l.succ) : HP go₀ ph ≤ HP go₁ ph := by
  apply Nat.find_mono
  intro q hq moves h_inj
  obtain he := embeds_of_strongly_embeds h_embed
  obtain ⟨f,hf⟩ := h_embed
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
      simp only at R

      rw [R]
      tauto
  have : (path go₀ moves.1).1 = (path go₁ (morph f go₀ moves.1)).1 :=
    path_eq_path_morph f go₀ go₁ hf moves.1
  let Q₀ := pts_bound_of_embeds' he ph (⟨(path go₀ moves.1).1,path_len _ _⟩)
  calc
  _ ≤ pts_tot' go₁ ph ⟨(path go₀  moves.1).1, path_len _ _⟩ := Q₀
  _ = pts_tot' go₁ ph ⟨(path go₁ moves'.1).1, path_len _ _⟩ := by simp_rw [this]
  _ ≤ q                                                    := hq moves' h_inj'

-- #eval HP tri ⟨[ true, true, true, true, true, false, false, true, false, false, false, true, true],rfl⟩

-- #eval HP_rev rect₃ ⟨[true,false,false,false,false,true,false,false,false,true],rfl⟩

-- #eval HP tri ⟨[true,false,false,false,false,true,false,false,false,true],rfl⟩



theorem embeds_strongly_tri_quad : tri ≼ rect := by
  exists tri_rect_embedding
  exact tri_rect_embedding_is_embedding

theorem embeds_strongly_quad_hex : rect ≼ hex := by
  exists rect_hex_embedding
  exact rect_hex_embedding_is_embedding

/- Here are some quotable results:
  The degree 3 "hexagonal lattice" protein folding model has an objective function
  P_tri that is bounded by that of the usual HP 2D model.
  Similarly for P_quad and P_hex.
-/


theorem HP_quad_bounds_tri {l:ℕ} (ph : Vector Bool l.succ) : HP tri ph ≤ HP rect ph :=
  value_bound_of_embeds_strongly embeds_strongly_tri_quad _
theorem HP_hex_bounds_quad {l:ℕ} (ph : Vector Bool l.succ) : HP rect ph ≤ HP hex ph :=
  value_bound_of_embeds_strongly embeds_strongly_quad_hex _

/- We want to show that rect is not ≤ hex₄;
because that would be an effective separation result rect ≤ hex₄ ≤ hex
(assuming of course that hex is NP-complete)
True for length up to 7!
-/




-- abbrev t := true
-- abbrev f := false
-- #eval numtrue   (⟨[f,f,f,f,f,t],rfl⟩ : Vector Bool 6)

-- abbrev xx := (⟨[f,f,f,f,f,f],rfl⟩ : Vector Bool 6)
-- abbrev y := [
--   (⟨[f,f,f,f,f,f],rfl⟩ : Vector Bool 6),
--   (⟨[f,f,f,f,f,t],rfl⟩ : Vector Bool 6),
-- ]
-- -- #eval xx
-- -- #eval [HP_rev rect ⟨xx,rfl⟩, HP_rev hex₄ ⟨x,rfl⟩]
-- #eval Vector.map (λ a ↦ [HP_rev rect a, numtrue a, HP_rev hex₄ a]) ⟨y,rfl⟩

end Main_theoretical_development

section Backtracking_usage

theorem path_cons_suffix
  {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) (tail : List (Fin b)) (head: Fin b):
(path go tail).1 <:+ (path go (head :: tail)).1
:= by
  rw [path_cons]
  exact List.suffix_cons (go head (Vector.head (path go tail))) (path go tail).1


theorem path_append_suffix
  {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) (tail : List (Fin b)) (head: List (Fin b)):
(path go tail).1 <:+ (path go (head ++ tail)).1
:= by
  induction head
  simp only [List.nil_append]
  exact List.suffix_rfl
  rename_i head tail_1 tail_ih
  calc
  _ <:+ (path go (tail_1 ++ tail)).1 := tail_ih
  _ <:+ _ := path_cons_suffix _ _ _


theorem nodup_path_preserved_under_suffixes
{b: ℕ}
(go: Fin b → ℤ × ℤ → ℤ × ℤ)
: ∀ (u v : List (Fin b)),
  u <:+ v → (fun moves => List.Nodup (path go moves).1) v → (fun moves => List.Nodup (path go moves).1) u
:=
  by
      intro u v huv
      obtain ⟨t,ht⟩ := huv
      symm at ht
      subst ht
      simp only
      intro h
      obtain ⟨s,hs⟩ := path_append_suffix go u t
      rw [← hs] at h
      exact List.Nodup.of_append_right h

def NodupPath {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ)  : MonoPred b :=
{
  P := (λ moves ↦ List.Nodup (path go moves).1)
  preserved_under_suffixes := nodup_path_preserved_under_suffixes _
}

def first_nonzero_entry (moves : List (Fin 4)) : Option (Fin 4) := by {
  induction moves
  .  exact none
  .  rename_i head _ tail_ih;exact ite (tail_ih ≠ none) tail_ih (ite (head = 0) none head)
}

-- Here's the Fin.find version:
def where_first_nonzero_entryF {l:ℕ} (moves : Fin l → (Fin 4)) : Option (Fin l)
  := Fin.find (λ i ↦ moves i ≠ 0)
def first_nonzero_entryF {l:ℕ} (moves : Fin l → (Fin 4)) : Option (Fin 4) :=
dite (Option.isSome (where_first_nonzero_entryF moves))
  (λ h ↦ some (moves ((where_first_nonzero_entryF moves).get h)))
  (λ _ ↦ none
  )



-- By symmetry we may assume that all walks (folds) are orderly, although that in itself could deserve a proof.
def orderly_and_nontrivial (moves: List (Fin 4)) := moves.reverse.getLast? = some (0:Fin 4)
      ∧ first_nonzero_entry moves.reverse = some 2

def orderly (moves: List (Fin 4)) := -- February 24, 2024
  (
    moves.reverse.getLast? = some (0:Fin 4) ∨
    moves.reverse.getLast? = none
  ) ∧ (
    first_nonzero_entry moves.reverse = some 2 ∨
    first_nonzero_entry moves.reverse = none
  )

instance (moves : List (Fin 4)) : Decidable (orderly moves) := by
  unfold orderly; exact And.decidable
instance (moves : List (Fin 4)) : Decidable (orderly_and_nontrivial moves) := by
  unfold orderly_and_nontrivial; exact And.decidable

def rotate : ℤ × ℤ → ℤ × ℤ := λ (x,y) ↦ (-y,x)
def reflect: ℤ × ℤ → ℤ × ℤ := λ (x,y) ↦ (x,-y)
def rotateIndex (a : Fin 4) : Fin 4 := match a with
| 0 => 2
| 1 => 3
| 2 => 1
| 3 => 0

def reflectIndex (a : Fin 4) : Fin 4 := match a with
| 0 => 0
| 1 => 1
| 2 => 3
| 3 => 2

theorem reflect_basic (u : ℤ × ℤ) (c: Fin 4):
reflect (rect c u) = rect (reflectIndex c) (reflect u)
:= by
  unfold reflect rect;simp only [neg_add_rev]
  exact match c with
  | 0 => by
    apply Prod.ext
    . simp only [Prod.fst_add, add_right_inj];
      decide;
    . simp only [Prod.snd_add];
      rw [Int.add_comm];simp only [add_right_inj];decide
  | 1 => by
    apply Prod.ext
    . simp only [Prod.fst_add, add_right_inj];
      decide;
    . simp only [Prod.snd_add];
      rw [Int.add_comm];simp only [add_right_inj];decide
  | 2 => by
    apply Prod.ext
    . simp only [Prod.fst_add, add_right_inj];
      decide;
    . simp only [Prod.snd_add];
      rw [Int.add_comm];simp only [add_right_inj];decide
  | 3 => by
    apply Prod.ext
    . simp only [Prod.fst_add, add_right_inj];
      decide;
    . simp only [Prod.snd_add];
      rw [Int.add_comm];simp only [add_right_inj];decide

theorem rotate_basic (u : ℤ × ℤ) (c: Fin 4):
rotate (rect c u) = rect (rotateIndex c) (rotate u)
:= by
  unfold rotate rect;simp
  exact match c with
  | 0 => by
    apply Prod.ext;
    simp only [Prod.fst_add];rw [Int.add_comm];
    simp only [add_right_inj];decide;
    simp only [Prod.snd_add, add_right_inj];decide
  | 1 => by
    apply Prod.ext;
    simp only [Prod.fst_add];rw [Int.add_comm];
    simp only [add_right_inj];decide;
    simp only [Prod.snd_add, add_right_inj];decide
  | 2 => by
    apply Prod.ext;
    simp only [Prod.fst_add];rw [Int.add_comm];
    simp only [add_right_inj];decide;
    simp only [Prod.snd_add, add_right_inj];decide
  | 3 => by
    apply Prod.ext;
    simp only [Prod.fst_add];rw [Int.add_comm];
    simp only [add_right_inj];decide;
    simp only [Prod.snd_add, add_right_inj];decide



theorem trafo_preserves_nearby (u v : ℤ × ℤ) (huv: nearby rect u v)
(trafo : ℤ×ℤ → ℤ×ℤ) (trafoIndex: Fin 4 → Fin 4)
(trafo_basic : ∀ (u : ℤ × ℤ), ∀ (c: Fin 4), trafo (rect c u) = rect (trafoIndex c) (trafo u)
)
:
nearby rect (trafo u) (trafo v) := by
  unfold nearby at *;
  simp only [decide_eq_true_eq, Prod.forall] at *;
  obtain ⟨c,hc⟩ := huv
  subst hc;
  exists (trafoIndex c);
  exact trafo_basic u.1 u.2 c

theorem trafo_preserves_nearby_converse {u v : ℤ × ℤ}
{trafo : ℤ×ℤ → ℤ×ℤ} {trafoIndex: Fin 4 → Fin 4} (trafo_basic : ∀ (u : ℤ × ℤ), ∀ (c: Fin 4),
trafo (rect c u) = rect (trafoIndex c) (trafo u)
)
(huv: nearby rect (trafo u) (trafo v))
(hs: Function.Surjective trafoIndex)
(hi: Function.Injective trafo)
:
nearby rect u v := by
  unfold nearby at *;
  simp only [Prod.forall, decide_eq_true_eq] at *;
  obtain ⟨c,hc⟩ := huv
  have : ∃ d, trafoIndex d = c := hs c
  obtain ⟨d,hd⟩ := this
  rw [← hd] at hc
  let Q := trafo_basic u.1 u.2 d
  rw [← Q] at hc
  apply hi at hc
  exists d

lemma four_choices (b : Fin 4):
b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by
  have : b.1 = 0 ∨ b.1 = 1 ∨ b.1 = 2 ∨ b.1 = 3 := by
    cases Nat.lt_or_eq_of_le (Fin.is_le b)
    rename_i h
    cases Nat.lt_or_eq_of_le (Nat.lt_succ.mp h)
    rename_i h_1;cases Nat.lt_or_eq_of_le (Nat.lt_succ.mp h_1);
    rename_i h_2
    left;exact Nat.lt_one_iff.mp h_2;tauto;tauto;tauto
  cases this;
  rename_i h
  left;exact Fin.ext h;
  rename_i h
  cases h;
  rename_i h_1;right;left;exact Fin.ext h_1
  rename_i h_1;cases h_1;
  rename_i h;right;right;left;exact Fin.ext h
  rename_i h;right;right;right;exact Fin.ext h

theorem rotateIndex_surjective : Function.Surjective rotateIndex := by
  intro b
  cases (four_choices b);
  rename_i h;subst h;exists 3;rename_i h;cases h;rename_i h_1;subst h_1;exists 2;rename_i h_1;
  cases h_1;rename_i h;subst h;exists 0;rename_i h;subst h;exists 1

theorem reflectIndex_surjective : Function.Surjective reflectIndex := by
  intro b
  cases (four_choices b);rename_i h_1;subst h_1;
  exists 0;
  rename_i h_1;cases h_1;rename_i h;subst h;exists 1;rename_i h;cases h;rename_i h_1;
  subst h_1;exists 3;rename_i h_1;subst h_1;exists 2

theorem rotate_injective : Function.Injective rotate := by
  intro x y hxy;unfold rotate at hxy;simp only [Prod.mk.injEq, neg_inj] at hxy ;apply Prod.ext;tauto;tauto

theorem reflect_injective : Function.Injective reflect := by
  intro x y hxy;unfold reflect at hxy;simp only [Prod.mk.injEq, neg_inj] at hxy ;apply Prod.ext;tauto;tauto


theorem rotate_preserves_nearby_converse {u v : ℤ × ℤ}
(huv: nearby rect (rotate u) (rotate v))
    : nearby rect u v
  := trafo_preserves_nearby_converse rotate_basic huv rotateIndex_surjective rotate_injective

theorem reflect_preserves_nearby_converse {u v : ℤ × ℤ}
(huv: nearby rect (reflect u) (reflect v))
    : nearby rect u v
  := trafo_preserves_nearby_converse reflect_basic huv reflectIndex_surjective reflect_injective


-- This is a first step towards proving that "rotate" preserves pts_tot':
theorem rotate_preserves_nearby {u v : ℤ × ℤ} (huv: nearby rect u v):
nearby rect (rotate u) (rotate v) :=
  trafo_preserves_nearby _ _ huv _ rotateIndex rotate_basic

theorem reflect_preserves_nearby {u v : ℤ × ℤ} (huv: nearby rect u v):
nearby rect (reflect u) (reflect v) :=
    trafo_preserves_nearby _ _ huv _ reflectIndex reflect_basic



def roeu := (λ a : Fin 4 ↦ λ _ : ℤ×ℤ ↦ rotateIndex a) -- roeu = rotate, essentially unary
def reeu := (λ a : Fin 4 ↦ λ _ : ℤ×ℤ ↦ reflectIndex a) -- reeu = reflect,essentially unary
abbrev ρ := roeu

-- This can be generalized to be in terms of "trafo_eu":
lemma rot_length₀ (moves: List (Fin 4))
(k: Fin (Vector.length (path rect moves)))
: k.1 < Nat.succ (List.length (morph roeu rect moves))
:= by
  rw [morph_len];simp;
lemma ref_length₀ (moves: List (Fin 4))
(k: Fin (Vector.length (path rect moves)))
: k.1 < Nat.succ (List.length (morph reeu rect moves))
:= by
  rw [morph_len];simp;

lemma ref_length₀_morf (moves: List (Fin 4))
(k: Fin (Vector.length (path rect moves)))
: k.1 < Nat.succ (List.length (morf_list reflectIndex moves))
:= by
  rw [morf_len];simp; -- finished 3/8/24


theorem path_len_aux₁
{hd: Fin 4}
{tl: List (Fin 4)}
(k: Fin (Vector.length (path rect (hd :: tl))))
{s: ℕ}
(hs: k.1 = Nat.succ s)
: s < Nat.succ (List.length (tl))
:= by
      let Q := k.2
      rw [hs] at Q
      have h₀: s <  (Vector.length (path rect tl)) :=
        Nat.succ_lt_succ_iff.mp Q
      have h₁: Vector.length (path rect (hd :: tl))
               = List.length (path rect (hd :: tl)).1 :=
        (path_len' rect (List.length (hd :: tl)) (hd :: tl) rfl).symm
      have h₂: Vector.length (path rect tl)
               = List.length (path rect tl).1 := Nat.succ_inj'.mp h₁
      rw [h₂,path_len' rect tl.length _ rfl] at h₀
      exact h₀

theorem morph_path_succ_aux
{hd: Fin 4}
{tl: List (Fin 4)}
(k: Fin (Vector.length (path rect (hd :: tl))))
{s: ℕ}
(hs: k.1 = Nat.succ s)
: s < Nat.succ (List.length (morph roeu rect tl))
:= by
      let h₀ := path_len_aux₁ k hs
      rw [morph_len];
      exact h₀

theorem morph_path_succ_aux_reeu
{hd: Fin 4}
{tl: List (Fin 4)}
(k: Fin (Vector.length (path rect (hd :: tl))))
{s: ℕ}
(hs: k.1 = Nat.succ s)
: s < Nat.succ (List.length (morph reeu rect tl))
:= by
      let h₀ := path_len_aux₁ k hs
      rw [morph_len];
      exact h₀

theorem morf_path_succ_aux
{hd: Fin 4}
{tl: List (Fin 4)}
(k: Fin (Vector.length (path rect (hd :: tl))))
{s: ℕ}
(hs: k.1 = Nat.succ s)
: s < Nat.succ (List.length (morf_list reflectIndex tl))
:= by
      let h₀ := path_len_aux₁ k hs
      rw [morf_len];
      exact h₀


-- Here is a version of reflect_morph that is simply scaled down
-- to not have the extra argument, and use morf_list
lemma reflect_morf_list (moves: List (Fin 4)) (k : Fin (path rect moves).length):
  reflect ((path rect                  moves ).get  k) =
          (path rect (morf_list reflectIndex moves)).get ⟨k.1, ref_length₀_morf moves k⟩
:= by
  induction moves
  . (have : k = 0 := Fin.ext (Fin.coe_fin_one k));subst this;rfl

  rename Fin 4 => hd; rename List (Fin 4) => tl
  rw [path_cons_vec]
  by_cases h : k = 0
  . subst h
    simp only [List.length_cons, Vector.get_zero, Vector.head_cons, Fin.val_zero,
      Fin.zero_eta]
    rw [reflect_basic]
    have : reflect (path rect tl).head = (path rect (morf_list (reflectIndex) tl)).head
    := by
      rename_i tail_ih
      let Q := tail_ih 0;
      simp only [Vector.get_zero, Fin.val_zero, Fin.zero_eta] at Q ;exact Q
    exact congr_arg _ this

  obtain ⟨s,hs⟩ := Fin.eq_succ_of_ne_zero h
  have g₀: ((rect hd (path rect tl).head) ::ᵥ path rect tl).get (Fin.succ s)
                                           = (path rect tl).get s := rfl
  have g₄: ((rect hd (path rect tl).head) ::ᵥ path rect tl).get k
                                           = (path rect tl).get s := by rw [hs,← g₀]
  rw [g₄]
  have g₁: path rect (morf_list reflectIndex (hd :: tl))
         = path rect ((reflectIndex hd ) :: (morf_list reflectIndex (tl))) := rfl
  rw [g₁,path_cons_vec]
  have hs': k.1 = s.1.succ := Fin.mk_eq_mk.mp hs
  have g₃: k.1 < (morf_list reflectIndex (hd :: tl)).length.succ
    := by rw [morf_len];simp
  have g₂: (
      rect (reflectIndex hd)
      ((path rect (morf_list reflectIndex tl)).head)
    ::ᵥ path rect (morf_list reflectIndex tl)).get ⟨k.1, g₃⟩
     = (path rect (morf_list reflectIndex tl)).get ⟨s, morf_path_succ_aux k hs'⟩
    := by simp_rw [hs'];norm_cast
  . rename_i tail_ih;rw [g₂,tail_ih s]


-- Finished February 26, 2024, although the proof is hard to understand:
-- (reflect_morph and rotate_morph can have a common generalization)
lemma reflect_morph (moves: List (Fin 4)) (k : Fin (path rect moves).length):
  reflect ((path rect                  moves ).get  k) =
          (path rect (morph reeu rect moves)).get ⟨k.1, ref_length₀ moves k⟩
:= by
  induction moves
  . -- nil
    (have : k = 0 := Fin.ext (Fin.coe_fin_one k));subst this;rfl
  . -- cons
    rename Fin 4 => hd; rename List (Fin 4) => tl
    rw [path_cons_vec]
    by_cases h : k = 0
    . -- pos
      subst h; simp only [List.length_cons, Vector.get_zero, Vector.head_cons,
        Fin.val_zero, Fin.zero_eta];
      rw [reflect_basic];rename_i tail_ih;let Q := tail_ih 0;
      simp only [Vector.get_zero, Fin.val_zero, Fin.zero_eta] at Q ;exact congr_arg _ Q
    . -- neg
      obtain ⟨s,hs⟩ := Fin.eq_succ_of_ne_zero h
      subst hs
      simp only [List.length_cons, Vector.get_cons_succ, Fin.val_succ]
      rename_i tail_ih;rw [tail_ih s]
      have g₁: path κ (morph reeu rect (hd :: tl))
             = path κ ((     reeu       hd ((path κ tl).head)) :: (morph reeu κ tl)) := rfl
      rw [g₁, path_cons_vec]
      norm_cast

lemma rotate_morph (moves: List (Fin 4)) (k : Fin (path rect moves).length):
  rotate ((path rect                  moves ).get  k) =
          (path rect (morph roeu rect moves)).get ⟨k.1, rot_length₀ moves k⟩
:= by
  induction moves
  . -- nil
    (have : k = 0 := Fin.ext (Fin.coe_fin_one k));subst this;rfl
  . -- cons
    rename Fin 4 => hd; rename List (Fin 4) => tl
    rw [path_cons_vec]
    by_cases h : k = 0
    . -- pos
      subst h;
      simp only [List.length_cons, Vector.get_zero, Vector.head_cons, Fin.val_zero,
        Fin.zero_eta];
      rw [rotate_basic];rename_i tail_ih;let Q := tail_ih 0;
      simp only [Vector.get_zero, Fin.val_zero, Fin.zero_eta] at Q ;exact congr_arg _ Q
    . -- neg
      obtain ⟨s,hs⟩ := Fin.eq_succ_of_ne_zero h
      subst hs
      simp only [List.length_cons, Vector.get_cons_succ, Fin.val_succ]
      rename_i tail_ih;rw [tail_ih s]
      have g₁: path κ (morph ρ rect (hd :: tl))
             = path κ ((     ρ       hd ((path κ tl).head)) :: (morph ρ κ tl)) := rfl
      rw [g₁, path_cons_vec]
      norm_cast

-- Completed March 6, 2024:
/- To avoid type problems,
  1. Separate proofs into their own have-statements
  2. Don't let any variables get automatically cast into ↑↑↑k versions;
  instead specify their type whenever possible. See *** below.
-/
lemma rotate_morphᵥ {l: ℕ} {moves: Vector (Fin 4) l} (k : Fin l.succ):
  rotate ((pathᵥ κ                moves).get  k) =
          (pathᵥ κ (morphᵥ roeu κ moves)).get k
:= by
  have : k.1 < Vector.length (path κ moves.1) := by
    let R := (path κ moves.1).2
    have : (path κ moves.1).length
         = (path κ moves.1).1.length := R.symm
    rw [this, R, moves.2]
    simp
  let Q := rotate_morph moves.1 ⟨k,this⟩ -- ***
  have h₁: rotate (Vector.get (path  κ moves.1) ⟨k.1, this⟩)
         = rotate (Vector.get (pathᵥ κ moves)    k) := congrArg _ rfl
  rw [h₁] at Q
  rw [← h₁, rotate_morph]
  norm_cast

-- reflect_morphᵥ is exactly same proof as rotate_morphᵥ
lemma reflect_morphᵥ {l: ℕ} {moves: Vector (Fin 4) l} (k : Fin l.succ):
  reflect ((pathᵥ κ                moves).get  k) =
          (pathᵥ κ (morphᵥ reeu κ moves)).get k
:= by
  have : k.1 < Vector.length (path κ moves.1) := by
    let R := (path κ moves.1).2
    have : (path κ moves.1).length
         = (path κ moves.1).1.length := R.symm
    rw [this, R, moves.2]
    simp
  let Q := reflect_morph moves.1 ⟨k,this⟩ -- ***
  have h₁: reflect (Vector.get (path  κ moves.1) ⟨k.1, this⟩)
         = reflect (Vector.get (pathᵥ κ moves)    k) := congrArg _ rfl
  rw [h₁] at Q
  rw [← h₁, reflect_morph]
  norm_cast

lemma reflect_morf {l: ℕ} {moves: Vector (Fin 4) l} (k : Fin l.succ):
  reflect ((pathᵥ κ                moves).get  k) =
          (pathᵥ κ (morf reflectIndex moves)).get k
:= by
  -- combine reflect_morphᵥ and reflect_morf_list
  -- completed 3/8/24 !
  have : k.1 < Vector.length (path κ moves.1) := by
    let R := (path κ moves.1).2
    have : (path κ moves.1).length
         = (path κ moves.1).1.length := R.symm
    rw [this, R, moves.2]
    simp
  let Q := reflect_morf_list moves.1 ⟨k,this⟩ -- ***
  have h₁: reflect (Vector.get (path  κ moves.1) ⟨k.1, this⟩)
         = reflect (Vector.get (pathᵥ κ moves)    k) := congrArg _ rfl
  rw [h₁] at Q
  rw [← h₁, reflect_morf_list]
  norm_cast

theorem rotate_preserves_pt_loc' {l:ℕ}
-- Finished March 6, 2024. Improving rotate_preserves_pt_loc.
  (moves : Vector (Fin 4) l) (i j : Fin l.succ) (ph: Vector Bool l.succ)
  (hpt: pt_loc κ (π κ             moves)  i j ph)
  :     pt_loc κ (π κ (morphᵥ roeu κ moves)) i j ph
  := by
    unfold pt_loc at *
    simp only [Bool.and_eq_true, decide_eq_true_eq] at *
    let R := rotate_preserves_nearby hpt.2
    rw [rotate_morphᵥ i, rotate_morphᵥ j] at R
    tauto



theorem reflect_preserves_pt_loc' {l:ℕ}
-- just like rotate_preserves_pt_loc'
  (moves : Vector (Fin 4) l) (i j : Fin l.succ) (ph: Vector Bool l.succ)
  (hpt: pt_loc κ (π κ             moves)  i j ph)
  :     pt_loc κ (π κ (morphᵥ reeu κ moves)) i j ph
  := by
    unfold pt_loc at *
    simp only [Bool.and_eq_true, decide_eq_true_eq] at *
    let R := reflect_preserves_nearby hpt.2
    rw [reflect_morphᵥ i, reflect_morphᵥ j] at R
    tauto

theorem reflect_preserves_pt_loc'_morf {l:ℕ}
-- just like rotate_preserves_pt_loc'. 3/8/24
  (moves : Vector (Fin 4) l) (i j : Fin l.succ) (ph: Vector Bool l.succ)
  (hpt: pt_loc κ (π κ             moves)  i j ph)
  :     pt_loc κ (π κ (morf reflectIndex moves)) i j ph
  := by
    unfold pt_loc at *
    simp only [Bool.and_eq_true, decide_eq_true_eq] at *
    let R := reflect_preserves_nearby hpt.2
    rw [reflect_morf i, reflect_morf j] at R
    tauto



theorem rotate_pts'_atᵥ {l:ℕ} (k : Fin l.succ)
  (ph    : Vector Bool    l.succ)
  (moves : Vector (Fin 4) l):
  pts_at' κ k ph (π κ moves) ≤
  pts_at' κ k ph (π κ (σ ρ κ moves)) := by
  -- Completed March 6, 2024. So easy :)
  apply Finset.card_le_card
  intro i hi
  let Q :=  rotate_preserves_pt_loc' moves i k ph
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
  tauto



theorem reflect_pts'_atᵥ {l:ℕ} (k : Fin l.succ)
  (ph    : Vector Bool    l.succ)
  (moves : Vector (Fin 4) l):
  pts_at' κ k ph (π κ moves) ≤
  pts_at' κ k ph (π κ (σ reeu κ moves)) := by
  -- just like rotate_pts'_atᵥ
  apply Finset.card_le_card
  intro i hi
  let Q :=  reflect_preserves_pt_loc' moves i k ph
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
  tauto

theorem reflect_pts'_atᵥ_morf {l:ℕ} (k : Fin l.succ)
  (ph    : Vector Bool    l.succ)
  (moves : Vector (Fin 4) l):
  -- 3/8/24
  pts_at' κ k ph (π κ moves) ≤
  pts_at' κ k ph (π κ (morf reflectIndex moves)) := by
  apply Finset.card_le_card
  intro i hi
  let Q :=  reflect_preserves_pt_loc'_morf moves i k ph
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
  tauto


theorem rotate_pts_tot
  {l:ℕ} (ph : Vector Bool l.succ)(moves : Vector (Fin 4) l):
  pts_tot' κ ph (π κ moves) ≤
  pts_tot' κ ph (π κ (σ ρ κ moves))
  := by
    unfold pts_tot'
    apply Finset.sum_le_sum
    intro k
    intro
    exact rotate_pts'_atᵥ _ _ _



theorem reflect_pts_tot_morf
  {l:ℕ} (ph : Vector Bool l.succ)(moves : Vector (Fin 4) l):
  pts_tot' κ ph (π κ moves) ≤
  pts_tot' κ ph (π κ (morf reflectIndex moves))
  -- 3/8/24
  := by
    unfold pts_tot'
    apply Finset.sum_le_sum
    intro k
    intro
    exact reflect_pts'_atᵥ_morf _ _ _


theorem reflect_pts_tot
  {l:ℕ} (ph : Vector Bool l.succ)(moves : Vector (Fin 4) l):
  pts_tot' κ ph (π κ moves) ≤
  pts_tot' κ ph (π κ (σ reeu κ moves))
  := by
    unfold pts_tot'
    apply Finset.sum_le_sum
    intro k
    intro
    exact reflect_pts'_atᵥ _ _ _

  -- now we want to argue that we can always rotate to make moves start with 0, since:
theorem rotate_until_right : ∀ k : Fin 4,
  k = 0 ∨
  rotateIndex k = 0 ∨
  rotateIndex (rotateIndex k) = 0 ∨
  rotateIndex (rotateIndex (rotateIndex k)) = 0
| 0 => by left;rfl
| 1 => by right;right;left;rfl
| 2 => by right;right;right;rfl
| 3 => by right;left;rfl

theorem rotate_head
{l: ℕ}
(moves: Vector (Fin 4) (Nat.succ l))
: rotateIndex (Vector.head moves) = Vector.head (σ ρ κ moves)
:= by obtain ⟨a,⟨u,hu⟩⟩ := Vector.exists_eq_cons moves;rw [hu, Vector.head_cons];rfl

theorem rotate_headF
{l: ℕ}
(moves: Fin l.succ → (Fin 4))
: rotateIndex (moves 0) = (morfF rotateIndex moves) 0
:= rfl -- certainly easier with morfF !


theorem towards_orderlyish
  {l:ℕ} (ph : Vector Bool l.succ.succ)(moves : Vector (Fin 4) l.succ):
  ∃ moves', moves'.get 0 = 0 ∧
  pts_tot' κ ph (π κ moves) ≤
  pts_tot' κ ph (π κ moves')
  := by
  let m₀ := moves;let m₁ := (σ ρ κ m₀);let m₂ := (σ ρ κ m₁);let m₃ := (σ ρ κ m₂)
  cases rotate_until_right (moves.get 0);
  -- inl
  . exists m₀
  . -- inr
    rename_i h;cases h;
    . -- inr.inl
      exists m₁
      constructor
      . simp only [Vector.get_zero];
        rename_i h_1
        rw [← h_1];
        simp only [Vector.get_zero];symm;
        simp only [Vector.get_zero] at h_1 ;
        exact rotate_head _
      . exact rotate_pts_tot ph m₀
    . -- inr.inr
      rename_i h_1
      cases h_1;
      . -- inr.inr.inl
        exists m₂
        constructor
        . -- inr.inr.inl.left
          rename_i h;
          rw [← h];simp only [Vector.get_zero]
          rw [rotate_head m₀, rotate_head m₁]
        . -- inr.inr.inl.right
          calc
            pts_tot' κ ph (π κ m₀) ≤ pts_tot' κ ph (π κ m₁):= rotate_pts_tot ph moves
            _                      ≤ _ := rotate_pts_tot ph m₁
      . -- inr.inr.inr
        exists m₃;
        constructor;
        . rename_i h;
          rw [← h];simp only [Vector.get_zero]
          rw [rotate_head m₀,rotate_head m₁,rotate_head m₂]

        . calc
          pts_tot' κ ph (π κ m₀) ≤ pts_tot' κ ph (π κ m₁) := rotate_pts_tot ph m₀
          _                      ≤ pts_tot' κ ph (π κ m₂) := rotate_pts_tot ph m₁
          _                      ≤ _                      := rotate_pts_tot ph m₂

/--
We can always reflect to make the first entry after 0s (and 1s, although they are ruled out by injectivity)
be a 2.-/
theorem rotate_until_right_reflect : ∀ k : Fin 4,
  k = 0 ∨
  k = 1 ∨
  k = 2 ∨
  reflectIndex k = 2
| 0 => by left;rfl
| 1 => by right;left;rfl
| 2 => by right;right;left;rfl
| 3 => by right;right;right;rfl


theorem towards_orderly
  {l:ℕ} (ph : Vector Bool l.succ.succ)(moves : Vector (Fin 4) l.succ):
  ∃ moves', moves'.get 0 = 0 ∧
  (∀ j, (∀ i, i < j → moves'.get i = 0 ∨ moves'.get i = 1) → moves'.get j ≠ 3) ∧
  pts_tot' κ ph (π κ moves) ≤
  pts_tot' κ ph (π κ moves')
  -- completed 3/8/24. Next we can point out that 0 can't be followed by 1 in injective fold.
  := by
  obtain ⟨moves₀,hmoves₀⟩ := towards_orderlyish ph moves
  by_cases h₃: (∀ j, (∀ i, i < j → moves₀.get i = 0 ∨ moves₀.get i = 1) → moves₀.get j ≠ 3)
  . -- pos
    exists moves₀;tauto
  . -- neg
    have : ∃ (j : Fin (l + 1)),
      (∀ i < j, Vector.get moves₀ i = 0 ∨ Vector.get moves₀ i = 1) ∧ Vector.get moves₀ j = 3
      := by
        contrapose h₃;
        simp only [ne_eq, not_forall, not_not, exists_prop, not_exists, not_and]
        intro x hx;contrapose h₃;
        simp only [not_exists, not_and, not_forall, not_not, exists_prop];
        simp only [not_not] at h₃ ;exists x
    obtain ⟨j,hj⟩ := this
    have : Vector.get (morf reflectIndex moves₀) j = 2 := by
      let Q := hj.2;unfold morf reflectIndex;simp only [Vector.get_map];rw [Q];rfl
    exists (morf reflectIndex moves₀)
    constructor
    . let Q := hmoves₀.1;unfold reflectIndex morf; simp only [Vector.get_zero,
      Vector.head_map];
      simp only [Vector.get_zero] at Q ;rw [Q];rfl

    . -- neg.intro.right
      constructor
      . -- neg.intr.right.left
        intro j₁ hj₁;by_cases h : j₁ < j;let Q := hj.1 j₁ h
        -- now it's easy using morf
        . cases Q
          . intro hc;unfold morf at hc; simp only [Vector.get_map] at hc ;
            rename_i h_1;rw [h_1] at hc;contrapose hc;decide
          . intro hc;unfold morf at hc; simp only [Vector.get_map] at hc ;
            rename_i h_1;rw [h_1] at hc;contrapose hc;decide
        . by_cases he : j₁ = j
          . -- pos
            subst he;rw [this];symm;decide
          . -- neg
            have : j < j₁ ∨ j = j₁ ∨ j₁ < j := lt_trichotomy j j₁
            have : j < j₁ := by tauto
            let Q := hj.2
            let R := hj₁ j this
            cases R
            . rename_i h_1;unfold morf at h_1; simp only [Vector.get_map] at h_1 ;rw [Q] at h_1;contrapose h_1;decide
            . rename_i h_1;unfold morf at h_1; simp only [Vector.get_map] at h_1 ;rw [Q] at h_1;contrapose h_1;decide
      . -- neg.intr.right.right
        calc
        _ ≤ pts_tot' κ ph (π κ moves₀) := hmoves₀.2
        _ ≤ _                          := reflect_pts_tot_morf ph moves₀


theorem path_morph_len
{l: ℕ}
(moves: Vector (Fin 4) l)
: (path rect (morph roeu rect moves.1)).1.length = l.succ
:= by
  -- this is just path_len and morph_len and should be generalized
  let morph_vec := (⟨morph roeu rect moves.1,morph_len _ _ _⟩ : Vector (Fin 4) moves.1.length)
  let Q := path_len rect morph_vec
  rw [Q]
  simp

-- #eval orderly [0,2,2]
-- #eval orderly []
-- #eval orderly_and_nontrivial []

def pts_tot'_list_rev {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) (ph : List Bool) (moves: List (Fin b)): ℕ
:= dite (moves.length.succ = ph.length)
    (λ h ↦ pts_tot' -- or pts_tot
      go
      (⟨ph, rfl⟩ : Vector Bool ph.length)
      ⟨(path go moves).1.reverse,(by
        rw [List.length_reverse]
        rw [← h,path_len'];rfl
      )⟩
    )
    (λ _ ↦ 0)

def pts_tot'_list_rev' {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) (ph : List Bool) (moves: List (Fin b)): ℕ
:= dite (moves.length.succ = ph.length)
    (λ h ↦ pts_tot' -- or pts_tot
      go
      (⟨ph, by
        rw [← h]
      ⟩ : Vector Bool moves.length.succ)
      ⟨(path go moves).1.reverse,(by
        rw [List.length_reverse]
        simp_rw [h]
        rw [path_len' go _ moves]
        exact h
        rfl
      )⟩
    )
    (λ _ ↦ 0)


def pts_tot'_list {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) (ph : List Bool) (moves: List (Fin b)): ℕ
:= dite (moves.length.succ = ph.length)
    (λ h ↦ pts_tot' -- or pts_tot
      go
      (⟨ph, rfl⟩ : Vector Bool ph.length)
      ⟨(path go moves).1,(by rw [← h,path_len'];rfl)⟩
    )
    (λ _ ↦ 0)

def InjectivePath {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ) (ph : List Bool)
(p:ℕ) : MonoPred b :=
{
  P := (λ moves ↦ Function.Injective (λ i ↦ (path go moves).get i))
  preserved_under_suffixes := by
    intro u v huv h
    rw [← Vector.nodup_iff_injective_get] at *
    exact nodup_path_preserved_under_suffixes _ _ _ huv h
  Q := (λ moves : List (Fin b) ↦ pts_tot'_list go ph moves ≥ p ∧ orderly_and_nontrivial moves)
  -- this causes problems since "orderly" does not apply to arbitrary b
}

def InjectivePath₄ (go : Fin 4 → ℤ×ℤ → ℤ×ℤ) (ph : List Bool)
(p:ℕ) : MonoPred 4 :=
{
  P := (λ moves ↦ Function.Injective (λ i ↦ (path go moves).get i))
  preserved_under_suffixes := by
    intro u v huv h
    rw [← Vector.nodup_iff_injective_get] at *
    exact nodup_path_preserved_under_suffixes _ _ _ huv h
  Q := (λ moves : List (Fin 4) ↦ pts_tot'_list go ph moves ≥ p ∧ orderly_and_nontrivial moves)
}

def InjectivePath₅ (go : Fin 4 → ℤ×ℤ → ℤ×ℤ) (ph : List Bool)
(p:ℕ) : MonoPred 4 :=
{
  P := (λ moves ↦ Function.Injective (λ i ↦ (path go moves).get i))
  preserved_under_suffixes := by
    intro u v huv h
    rw [← Vector.nodup_iff_injective_get] at *
    exact nodup_path_preserved_under_suffixes _ _ _ huv h
  Q := (λ moves : List (Fin 4) ↦ pts_tot'_list_rev' go ph moves ≥ p ∧ orderly_and_nontrivial moves)
}

instance  (go : Fin 4 → ℤ×ℤ → ℤ×ℤ) (ph : List Bool)
(p:ℕ) : DecidablePred (InjectivePath₅ go ph p).P := by
  unfold InjectivePath₅
  exact inferInstance

instance  (go : Fin 4 → ℤ×ℤ → ℤ×ℤ) (ph : List Bool)
(p:ℕ) : DecidablePred (InjectivePath₅ go ph p).Q := by
  unfold InjectivePath₅
  exact inferInstance


-- Now use this to characterize. First add "M.Q":
theorem using_backtracking_verification₀ {k L p:ℕ}
  (go : Fin 4 → ℤ×ℤ → ℤ×ℤ)
  (bound : k ≤ L.succ) (M:MonoPred b)
  [DecidablePred M.P] [DecidablePred M.Q]
  (w : Vector (Fin 4) (L.succ-k))
  (ph : Vector Bool L.succ.succ)
  [DecidablePred (InjectivePath₄ go ph.1 p).P]
  [DecidablePred (InjectivePath₄ go ph.1 p).Q]
  :
  Fintype.card {
    v : Vector (Fin 4) L.succ // ((InjectivePath₄ go ph.1 p).P v.1
    ∧ (InjectivePath₄ go ph.1 p).Q v.1) ∧ w.1 <:+ v.1
  }
  = num_by_backtracking (InjectivePath₄ go ph.1 p).P (InjectivePath₄ go ph.1 p).Q w
:= backtracking_verification bound (InjectivePath₄ go ph.1 p) w

theorem using_backtracking_verification₁ {k L p:ℕ}
  (bound : k ≤ L.succ) (M:MonoPred 4)
  [DecidablePred M.P] [DecidablePred M.Q]
  (w : Vector (Fin 4) (L.succ-k))
  (ph : Vector Bool L.succ.succ)
  [DecidablePred (InjectivePath₄ rect ph.1 p).P]
  [DecidablePred (InjectivePath₄ rect ph.1 p).Q]
  :
  Fintype.card {
    v : Vector (Fin 4) L.succ // ((InjectivePath₄ rect ph.1 p).P v.1
    ∧ (λ moves ↦ pts_tot'_list rect ph.1 moves ≥ p ∧ orderly_and_nontrivial moves) v.1) ∧ w.1 <:+ v.1
  }
  = num_by_backtracking
    (InjectivePath₄ rect ph.1 p).P
    (λ moves ↦ pts_tot'_list rect ph.1 moves ≥ p ∧ orderly_and_nontrivial moves) w
:= by
  let R := backtracking_verification bound (InjectivePath₄ rect ph.1 p) w
  simp only [ge_iff_le]
  have : (InjectivePath₄ rect (ph.1) p).Q
  = (fun moves => p ≤ pts_tot'_list rect (ph.1) moves ∧ orderly_and_nontrivial moves)
    := by
      rfl
  simp_rw [← this]
  rw [← R]
  apply Fintype.card_congr
  rfl



-- make these have "go" as a parameter:
def set_of_folds_achieving_pts {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ)
  {l:ℕ} (p:ℕ) (ph : Vector Bool l.succ.succ) :=
  those_with_suffix'
    (λ moves ↦ Function.Injective (λ i ↦ (path go moves).get i))
    (λ moves ↦ pts_tot'_list go ph.1 moves ≥ p ∧ orderly_and_nontrivial moves)
    (Gap_nil' b l.succ) -- (there are 7 moves for a polypeptide of length 8)

def set_of_folds_achieving_pts_rev (go : Fin 4 → ℤ×ℤ → ℤ×ℤ)
  {l:ℕ} (p:ℕ) (ph : Vector Bool l.succ.succ) :=
  those_with_suffix'
    (λ moves : List (Fin 4) ↦ Function.Injective (λ i ↦ (path go moves).get i))
    (λ moves : List (Fin 4) ↦ pts_tot'_list_rev go ph.1 moves ≥ p ∧ orderly_and_nontrivial moves)
    (Gap_nil' 4 l.succ) -- (there are 7 moves for a polypeptide of length 8)

def goodFolds (go : Fin 4 → ℤ×ℤ → ℤ×ℤ)
  {l:ℕ} (p:ℕ) (ph : Vector Bool l.succ.succ) :=
-- really, this should be defined in direct terms and then prove that it equals those_with_suffix'
  those_with_suffix'
    (λ moves : List (Fin 4) ↦ Function.Injective (λ i ↦ (path go moves).get i))
    (λ moves : List (Fin 4) ↦ pts_tot'_list_rev' go ph.1 moves ≥ p ∧ orderly_and_nontrivial moves)
    (Gap_nil' 4 l.succ) -- (there are 7 moves for a polypeptide of length 8)

def equifoldable (go : Fin 4 → ℤ×ℤ → ℤ×ℤ)
  {l:ℕ} (ph₀ ph₁ : Vector Bool l.succ.succ) (p:ℕ) :=
  goodFolds go p ph₀ = goodFolds go p ph₁

infix:50 " ∼₃ " => (λ ph₀ ph₁ ↦ equifoldable rect₃ ph₀ ph₁ 2)
infix:50 " ∼ "  => (λ ph₀ ph₁ ↦ equifoldable rect  ph₀ ph₁ 2)


instance (go : Fin 4 → ℤ×ℤ → ℤ×ℤ)
  {l:ℕ}  (p:ℕ) : Equivalence (λ (ph₀ ph₁ : Vector Bool l.succ.succ) ↦ equifoldable go ph₀ ph₁ p)
    := {
      trans := by
        unfold equifoldable;intro _ _ _ h₀₁ h₁₂;exact Eq.trans h₀₁ h₁₂
      refl := by
        unfold equifoldable;intro _;rfl
      symm := by
        unfold equifoldable;intro _ _ h;exact h.symm
    }

instance (go : Fin 4 → ℤ×ℤ → ℤ×ℤ)
  {l:ℕ} (ph₀ ph₁ : Vector Bool l.succ.succ) (p:ℕ) : Decidable (equifoldable go ph₀ ph₁ p) := by
  unfold equifoldable
  unfold goodFolds
  unfold those_with_suffix'
  simp only [ge_iff_le, Nat.zero_eq, Nat.sub_zero]
  exact inferInstance


-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[false,false,true,false,false,true,false,true],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[true,true,true,true,true,true,true,true],rfl⟩

def o := false
def l := true

-- Words of length 6 that have non-∅ values:
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[l,o,l,l,o,l],rfl⟩ -- {[0, 2, 1, 2, 0]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[l,o,l,l,l,l],rfl⟩ -- {[0, 2, 1, 2, 0]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[l,l,o,o,l,l],rfl⟩ -- {[0, 0, 2, 1, 1]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[l,l,o,l,l,l],rfl⟩ -- {[0, 0, 2, 1, 1]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[l,l,l,o,l,l],rfl⟩ -- {[0, 0, 2, 1, 1]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[l,l,l,l,o,l],rfl⟩ -- {[0, 2, 1, 2, 0]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[l,l,l,l,l,l],rfl⟩ -- {[0, 2, 1, 2, 0], [0, 0, 2, 1, 1]}

def toSet
  {l:ℕ} (ph : Vector Bool l) :=
  (Finset.filter (λ i ↦ ph.get i) (Finset.univ : Finset (Fin l)))

/-- This result from March 29, 2024 proves the obvious fact that more H amino acids leads to more points. -/
theorem toSet_dominates {α β:Type} [Fintype β] [OfNat α 0] [DecidableEq α]
(go: β → α→α) {l:ℕ} (ph₀ ph₁ : Vector Bool l.succ) (hsub:
  toSet ph₀ ⊆ toSet ph₁) :
       HP go ph₀ ≤ HP go ph₁ := by
    apply Nat.find_mono
    intro n h moves h_inj
    let h₁ := h moves h_inj
    unfold pts_tot' at *
    have h₀ : (Finset.sum Finset.univ fun i => pts_at' go i ph₀ ⟨ (path go moves.1).1, by rw [path_len]⟩)
            ≤ (Finset.sum Finset.univ fun i => pts_at' go i ph₁ ⟨ (path go moves.1).1, by rw [path_len]⟩) := by
      apply Finset.sum_le_sum
      intro i; intro
      apply Finset.card_le_card
      intro j hj
      unfold pt_loc at *
      simp only [Finset.mem_univ, Bool.and_eq_true, decide_eq_true_eq,
        Finset.mem_filter, true_and] at *
      unfold toSet at hsub

      have h_ : j ∈ Finset.filter (fun i' => Vector.get ph₀ i' = true) Finset.univ
              ∧ i ∈ Finset.filter (fun i' => Vector.get ph₀ i' = true) Finset.univ := by
                simp only [Finset.mem_filter, Finset.mem_univ, true_and];exact hj.1.1
      let Q := And.intro (hsub h_.1) (hsub h_.2)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at Q
      tauto
    exact LE.le.trans h₀ h₁

theorem more_pts_of_subset (go: Fin 4 → ℤ×ℤ→ℤ×ℤ) {l:ℕ} {ph₀ ph₁ : Vector Bool l.succ.succ}
  (w: Gap 4 (Nat.succ l) 0)
              (hsub: toSet ph₀       ⊆ toSet            ph₁)
 :  pts_tot'_list_rev' go       ph₀.1 w.1 ≤ pts_tot'_list_rev' go ph₁.1 w.1 := by
      unfold pts_tot'_list_rev'
      have : Nat.succ (List.length w.1) = List.length ph₀.1 := by rw [w.2, ph₀.2];rfl
      rw [dif_pos this]
      have : Nat.succ (List.length w.1) = List.length ph₁.1 := by rw [w.2, ph₁.2];rfl
      rw [dif_pos this]
      apply Finset.sum_le_sum;   intro i _; unfold pts_at'
      apply Finset.card_le_card; intro j _; unfold pt_loc at *
      simp only [Nat.sub_zero, Finset.mem_univ, Bool.and_eq_true, decide_eq_true_eq,
        Finset.mem_filter, true_and] at *
      have hi: i.1 < l.succ.succ := by let A := i.2;simp_rw [w.2] at A;exact A
      have hj: j.1 < l.succ.succ := by let A := j.2;simp_rw [w.2] at A;exact A
      have hi': ⟨i.1,hi⟩ ∈ Finset.filter (fun i => Vector.get ph₀ i = true) Finset.univ := by
        simp only [Nat.sub_zero, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
      have hj': ⟨j.1,hj⟩ ∈ Finset.filter (fun i => Vector.get ph₀ i = true) Finset.univ := by
        simp only [Nat.sub_zero, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
      unfold toSet at hsub
      let hsubj := hsub hj'; simp only [Nat.sub_zero, Finset.mem_filter,
        Finset.mem_univ, true_and] at hsubj ;
      let hsubi := hsub hi'; simp only [Nat.sub_zero, Finset.mem_filter,
        Finset.mem_univ, true_and] at hsubi ;
      tauto


def meet {l:ℕ} (ph₀ ph₁ : Vector Bool l) : Vector Bool l :=
  Vector.ofFn (λ i ↦ ph₀.get i ∧ ph₁.get i)

infix:50 " ⊓ " => meet


lemma meet_get {l :ℕ} {ph₀ ph₁ : Vector Bool l} {i:Fin l}
: (ph₀ ⊓ ph₁).get i = (ph₀.get i ∧ ph₁.get i) := by
  have : (meet ph₀ ph₁).get i = (ph₀.get i && ph₁.get i) := by
    unfold meet
    simp
  rw [this]
  simp

theorem meet_basic₀ {l :ℕ} {ph₀ ph₁ : Vector Bool l}
  : toSet (ph₀ ⊓ ph₁) ⊆ toSet ph₀ := by
  intro i hi;unfold toSet at *;simp only [Finset.mem_filter, Finset.mem_univ,
    true_and] at *;rw [meet_get] at hi;tauto


theorem meet_basic₁
  {l :ℕ} {ph₀ ph₁ : Vector Bool l}
  : toSet (ph₀ ⊓ ph₁) ⊆ toSet ph₁ := by
  -- verbatim the same proof
  intro i hi;unfold toSet at *;simp only [Finset.mem_filter, Finset.mem_univ,
    true_and] at *;rw [meet_get] at hi;tauto


theorem goodFolds_monotone
  (go: Fin 4 → ℤ×ℤ→ℤ×ℤ) {l :ℕ} (ph₀ ph₁ : Vector Bool l.succ.succ)
                      (hsub: toSet ph₀ ⊆ toSet ph₁) (p:ℕ)
 : goodFolds go p ph₀ ⊆ goodFolds go p ph₁ := by

  let M₀ := InjectivePath₅ go ph₀.1 p
  let M₁ := InjectivePath₅ go ph₁.1 p
  let u := (Gap_nil' 4 (Nat.succ l))
  have verify₀:
    those_with_suffix' M₀.P M₀.Q u = Finset.filter (λ v  ↦ M₀.P v.1 ∧ M₀.Q v.1 ∧ u.1 <:+ v.1) Finset.univ
    := verify_those_with_suffix' (le_refl _) u -- nice to be able to use that!
  have verify₁:
    those_with_suffix' M₁.P M₁.Q u = Finset.filter (λ v  ↦ M₁.P v.1 ∧ M₁.Q v.1 ∧ u.1 <:+ v.1) Finset.univ
    := verify_those_with_suffix' (le_refl _) u
  simp only [Nat.sub_zero, Finset.filter_congr_decidable] at verify₀ verify₁
  unfold InjectivePath₅ at verify₀ verify₁
  simp only [ge_iff_le, Finset.filter_congr_decidable] at verify₀ verify₁

  unfold goodFolds
  simp only [ge_iff_le]
  intro w hw₀
  rw [verify₀] at hw₀
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw₀
  have hp: p ≤ pts_tot'_list_rev' go ph₁.1 w.1 := LE.le.trans hw₀.2.1.1 (more_pts_of_subset go w hsub)
  have hw₁ : w ∈ Finset.filter (fun v =>
    (Function.Injective fun i => Vector.get (path go v.1) i) ∧
    (p ≤ pts_tot'_list_rev' go ph₁.1 v.1 ∧ orderly_and_nontrivial v.1) ∧ (Gap_nil' 4 (Nat.succ l)).1 <:+ v.1
  ) Finset.univ := by
    simp only [Nat.sub_zero, Finset.filter_congr_decidable, Finset.mem_filter,
      Finset.mem_univ, true_and];tauto
  rw [← verify₁] at hw₁
  tauto

/-

For the model `rect`, equifoldability is coNP-complete.
It is in coNP since if `x` and `y` are not equifoldable it suffices to produce a fold by which
`x` achieves `k` points and `y` does not.
It is coNP-hard since `x∼∅ [k]` iff `P(x)<k`.
-/

theorem convex_equifoldable {l :ℕ} (ph₀ ph₁ ph₂: Vector Bool l.succ.succ)
(h₀₁: toSet ph₀ ⊆ toSet ph₁)
                 (h₁₂: toSet ph₁ ⊆ toSet ph₂)
(h₀₂: ph₀ ∼ ph₂) : ph₀ ∼ ph₁ := by
  let Q₀₁ := goodFolds_monotone rect ph₀ ph₁ h₀₁ 2
  let Q₁₂ := goodFolds_monotone rect ph₁ ph₂ h₁₂ 2
  rw [← h₀₂] at Q₁₂
  apply Finset.Subset.antisymm;tauto;tauto

-- theorem monotonicity_of_sim {k l :ℕ} (x₀ y₀: Vector Bool l.succ.succ)
--  (x₁ y₁: Vector Bool k.succ.succ)
-- (h: Vector.append x₀ x₁ ∼ Vector.append y₀ y₁) : x₀ ∼ y₀ := by
--   -- not true, due to Stecher type phenomena:
--   -- let x be a Stecher string, let x' an all-false string of the same length, and
-- consider x++[1] and x'++[1]
--   sorry



def goodPairs -- points_tot = Fin.card points_loc
  (go: Fin 4 → ℤ×ℤ→ℤ×ℤ) {l : ℕ} (fold : Vector (ℤ×ℤ) l) (ph : Vector Bool l)

  :=
Finset.filter
  (λ ik : (Fin l) × (Fin l) ↦ ((pt_loc go fold ik.1 ik.2 ph): Prop))
  (Finset.univ)

/-- Note that this is not true for ∪ and join. -/
theorem goodPairs_meet
  (go: Fin 4 → ℤ×ℤ→ℤ×ℤ) {l : ℕ} (ph₀ ph₁ : Vector Bool l.succ)
  (fold : Vector (ℤ×ℤ) (Nat.succ l))
 : goodPairs go fold (ph₀ ⊓ ph₁) =
   goodPairs go fold ph₀ ∩
   goodPairs go fold ph₁ := by
    -- let f := λ ph ↦ goodPairs go fold ph
    -- show f (meet ph₀ ph₁) = f ph₀ ∩ f ph₁
    apply Finset.ext
    intro ij
    constructor
    . -- mp
      intro hij
      rw [Finset.mem_inter]
      unfold goodPairs at *
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
      unfold pt_loc at *
      simp only [Bool.and_eq_true, decide_eq_true_eq] at *
      have hi: ij.1 ∈ Finset.filter (fun i => Vector.get (meet ph₀ ph₁) i = true) Finset.univ
        := by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hij.1.1.1
      have hj: ij.2 ∈ Finset.filter (fun i => Vector.get (meet ph₀ ph₁) i = true) Finset.univ
        := by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hij.1.1.2
      let Si₀ := meet_basic₀ hi; let Si₁ := meet_basic₁ hi
      let Sj₀ := meet_basic₀ hj; let Sj₁ := meet_basic₁ hj
      unfold toSet at Si₀ Si₁ Sj₀ Sj₁
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at Si₀ Si₁ Sj₀ Sj₁
      tauto
    . -- mpr
      simp only [Finset.mem_inter, and_imp]
      intro h₀ h₁
      unfold goodPairs pt_loc at *
      simp only [Bool.and_eq_true, decide_eq_true_eq, Finset.mem_filter,
        Finset.mem_univ, true_and] at *
      repeat rw [meet_get]
      tauto




-- Words of length 8 that have non-∅ values:
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,o,o,o,o],rfl⟩ -- all ∅
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,o,o,o,l],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,o,o,l,o],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,o,o,l,l],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,o,l,o,o],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,o,l,o,l],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,o,l,l,o],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,o,l,l,l],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,l,o,o,o],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,l,o,o,l],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,l,o,l,o],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,l,o,l,l],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,l,l,o,o],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,l,l,o,l],rfl⟩ -- {[0, 2, 1, 2, 0, 0, 0], [0, 2, 1, 2, 0, 2, 0], [0, 2, 1, 2, 0, 2, 1], [0, 2, 1, 2, 0, 0, 2], [0, 2, 1, 2, 0, 2, 2]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,l,l,l,o],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,o,l,l,l,l],rfl⟩ -- {[0, 2, 1, 2, 0, 0, 0], [0, 2, 1, 2, 0, 2, 0], [0, 2, 1, 2, 0, 2, 1], [0, 2, 1, 2, 0, 0, 2], [0, 2, 1, 2, 0, 2, 2]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,l,o,o,o,o],rfl⟩ -- all ∅
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,l,o,o,o,l],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,l,o,o,l,o],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,l,o,o,l,l],rfl⟩ -- {[0, 0, 2, 1, 1, 2, 0], [0, 0, 2, 1, 1, 1, 1], [0, 0, 2, 1, 1, 2, 1], [0, 0, 2, 1, 1, 1, 2], [0, 0, 2, 1, 1, 2, 2]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,l,o,l,o,o],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,l,o,l,o,l],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,l,o,l,l,o],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,l,o,l,l,l],rfl⟩ -- {[0, 0, 2, 1, 1, 2, 0], [0, 0, 2, 1, 1, 1, 1], [0, 0, 2, 1, 1, 2, 1], [0, 0, 2, 1, 1, 1, 2], [0, 0, 2, 1, 1, 2, 2]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,l,l,o,o,o],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,l,l,o,o,l],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,l,l,o,l,o],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,l,l,o,l,l],rfl⟩ -- {[0, 0, 2, 1, 1, 2, 0], [0, 0, 2, 1, 1, 1, 1], [0, 0, 2, 1, 1, 2, 1], [0, 0, 2, 1, 1, 1, 2], [0, 0, 2, 1, 1, 2, 2]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,l,l,l,o,o],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,l,l,l,o,l],rfl⟩ -- {[0, 2, 1, 2, 0, 0, 0], [0, 2, 1, 2, 0, 2, 0], [0, 2, 1, 2, 0, 2, 1], [0, 2, 1, 2, 0, 0, 2], [0, 2, 1, 2, 0, 2, 2]}
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,l,l,l,l,o],rfl⟩
-- #eval set_of_folds_achieving_pts_rev rect₃ 2 ⟨[o,o,l,l,l,l,l,l],rfl⟩ /- {[0, 2, 1, 2, 0, 0, 0],
--  [0, 2, 1, 2, 0, 2, 0],
--  [0, 0, 2, 1, 1, 2, 0],
--  [0, 0, 2, 1, 1, 1, 1],
--  [0, 2, 1, 2, 0, 2, 1],
--  [0, 0, 2, 1, 1, 2, 1],
--  [0, 2, 1, 2, 0, 0, 2],
--  [0, 0, 2, 1, 1, 1, 2],
--  [0, 2, 1, 2, 0, 2, 2],
--  [0, 0, 2, 1, 1, 2, 2]}-/

-- #eval (
--   ⟨[true,false,true,false,false,true,false,true],rfl⟩ ∼
--   ⟨[true,true,false,false,false,false,true,true],rfl⟩
-- )
-- #eval (
--   ⟨[false,false,true,false,false,true,false,true],rfl⟩ ∼
--   ⟨[true,true,false,false,false,false,true,true],rfl⟩
-- )



def num_folds_achieving_pts {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ)
  {l:ℕ} (ph : Vector Bool l.succ.succ) (p:ℕ) : ℕ :=
  num_by_backtracking
    (λ moves ↦ Function.Injective (λ i ↦ (path go moves).get i))
    (λ moves ↦ pts_tot'_list go ph.1 moves ≥ p ∧ orderly_and_nontrivial moves)
    (Gap_nil' b l.succ) -- (there are 7 moves for a polypeptide of length 8)


def can_achieve_pts {b:ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ)
  {l:ℕ} (ph : Vector Bool l.succ.succ) (p:ℕ): Prop :=
  set_of_folds_achieving_pts go p ph ≠ ∅

def x : List Bool := [true,false,true,false,true,false, true,true]
-- #eval HP rect ⟨x,rfl⟩           -- This evaluates to 3 quickly, don't even need the backtracking.
-- #eval HP rect ⟨x ++ [false],rfl⟩-- This evaluates to 2 quickly, don't even need the backtracking.
-- example: HP rect ⟨x ++ [false],rfl⟩ = 2 := by decide
-- #eval pts_tot'_list rect  x [0, 3, 1, 1, 2, 2, 0]
-- #eval pts_tot'_list rect  x [r2.D, r2.S, r2.A, r2.A, r2.W, r2.W, r2.D]
-- #eval pts_tot'_list rect  (x ++ [false]) [0, 3, 1, 1, 2, 2, 0].reverse

-- def quad : Fin 4 → ℤ×ℤ → ℤ×ℤ
-- | 0 => go_D
-- | 1 => go_A
-- | 2 => sp
-- | 3 => sm

def stecher1 : Prop :=
  those_with_suffix'
    (λ w ↦ Function.Injective (λ i ↦ (path rect w).get i))
    (λ w ↦ pts_tot'_list rect  x w > 2 ∧ orderly_and_nontrivial w)
    (Gap_nil' 4 7) -- (there are 7 moves for a polypeptide of length 8)
  = {⟨[0, 3, 3, 1, 1, 2, 0],rfl⟩} --{⟨[0, 3, 1, 1, 2, 2, 0],rfl⟩}
instance : Decidable stecher1 := by {
  unfold stecher1
  apply decEq
}
-- #eval [0,2,1].reverse.getLast?
-- #eval first_nonzero_entry [0,2,1]
-- #eval orderly_and_nontrivial [0,2,1]
-- #eval   (those_with_suffix'
--     (λ w ↦ Function.Injective (λ i ↦ (path quad w).get i))
--     (λ w ↦ pts_tot'_list rect  ([true,false,false,true]) w > 0 ∧ orderly_and_nontrivial w)
--     (Gap_nil' 4 3)) -- fixed February 20, 2024

def L : ℕ := 10
-- #eval   (those_with_suffix'
--     (λ w ↦ Function.Injective (λ i ↦ (path quad w).get i))
--     (λ w ↦ pts_tot'_list rect  (List.replicate L.succ true) w ≥ 5 ∧ orderly_and_nontrivial w)
--     (Gap_nil' 4 L)) -- fixed February 20, 2024

-- #eval HP rect ⟨[true],rfl⟩
-- #eval HP rect ⟨List.replicate 9 true,rfl⟩ -- 4
-- #eval HP rect ⟨List.replicate L.succ true,rfl⟩ -- 4
-- #eval HP hex ⟨List.replicate 3 true,rfl⟩ -- amazing

-- #eval (myvec 4 7).length
-- #eval stecher1

def stecher2 : Prop :=
those_with_suffix'
    (λ w ↦ Function.Injective (λ i ↦ (path rect w).get i))
    (
      λ w ↦ pts_tot'_list rect  (x ++ [false]) w > 2
        ∧ orderly_and_nontrivial w
    )
    (Gap_nil' 4 8) = ∅


def stecher_conjecture_counterexample : Prop := stecher1  ∧ stecher2

instance : Decidable stecher2 := by unfold stecher2; apply decEq
instance : Decidable stecher_conjecture_counterexample := by
  unfold stecher_conjecture_counterexample; unfold stecher1; unfold stecher2; exact And.decidable

-- #eval stecher1
-- #eval stecher2
#eval stecher_conjecture_counterexample

end Backtracking_usage
