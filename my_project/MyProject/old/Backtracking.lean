import Mathlib.Computability.NFA
import Mathlib.Data.Nat.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Std.Data.Nat.Lemmas
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Digits
import MyProject.Squarefree
-- import MyProject.FoldPred
import MyProject.MonoPred
set_option tactic.hygienic false
set_option maxHeartbeats 3000000


-- set_option maxRecDepth 10000
-- set_option checkBinderAnnotations false

/-
We count the number of words of squarefree words of length L having w as a suffix,
using recursive backtracking. Then we formally prove the correctness.
We generalize to any monotone predicate in place of squarefreeness.
We apply it to self-avoiding walks
(although we do not include a proof of monotonicity of self-avoidance).
We also generalize the backtracking procedure to allow a predicate to be
test at the tree leaves. This way we are able to look for self-avoiding walks
with a given number of points achieved in the HP protein folding model.
We verify a claim from [PAPER] that P(01010100) = 3 > 2 = P(010101001).

Using the self-avoidance numbers we discover the corresponding OEIS entry (https://oeis.org/A001411).
One could also do this for hex (https://oeis.org/A001334),
triangular [called honeycomb in OEIS https://oeis.org/A001668], and 3D lattices (https://oeis.org/A001412).

-/

-- A vector of length L monus k, thought of as a possible suffix for a word of length L
-- in which the first k bits are unspecified
-- For example, a Gap 10 10 has length 10 - 10.
def Gap (b L k : ℕ) : Type := Vector (Fin b) (L - k)

def Gap_cons {n L:ℕ} (b:ℕ) (a:Fin b) (w : Gap b L.succ n.succ)
                  (h: ¬ n ≥ L.succ) : Gap b L.succ n
  := ⟨a :: w.1, by {rw [List.length_cons];simp;exact (Nat.succ_sub (Nat.not_lt.mp h)).symm}⟩

def Gap_nil {k b L : ℕ} (h : k ≥ L) : Gap b L k
  := ⟨List.nil, by {rw [Nat.sub_eq_zero_of_le h];rfl}⟩

def count_those_with_suffix'
  {k b L : ℕ} (P: List (Fin b) → Prop) [DecidablePred P]
  (w : Gap b L.succ k) : ℕ :=
  by {
    induction k
    exact ((ite (P w.1) 1 0))   -- Base case
    exact                       -- Inductive case
      (ite (P w.1))
      (
        dite (n ≥ L.succ)
        -- (fun h ↦ n_ih (Gap_nil h))
        (λ h ↦ n_ih ⟨List.nil, by {rw [Nat.sub_eq_zero_of_le h];rfl}⟩ )
        (fun h ↦ List.sum (
            List.map (fun a ↦ (n_ih (Gap_cons b a w h))) (List.ofFn id)
        ))
      )
      0
  }

-- count_those_with_suffix = number of squarefree words having w as suffix
def count_those_with_suffix {k b :ℕ} {L:ℕ} (M : MonoPred b) [DecidablePred M.P] (w : Gap b L.succ k) : ℕ :=
by {
  induction k
  -- Base case:
  exact ((ite (M.P w.1) 1 0))
  -- Inductive case:
  exact
    (ite (M.P w.1))
    (
      dite (n ≥ L.succ)
      -- (λ h ↦ n_ih (Gap_nil h)) -- caused weird problem
        (λ h ↦ n_ih ⟨List.nil, by {rw [Nat.sub_eq_zero_of_le h];rfl}⟩ )
      (
        λ h ↦ List.sum (
          List.map (λ a ↦ (n_ih (Gap_cons b a w h))) (List.ofFn id)
        )
      )
    )
    0
}

def count_those_with_suffix''
  {k b :ℕ} {L:ℕ} (P: List (Fin b) → Prop) [DecidablePred P]
  (Q: List (Fin b) → Prop) [DecidablePred Q]
  (w : Gap b L.succ k) : ℕ :=
by {
  induction k
  /- Base case: -/
  exact ((ite (P w.1 ∧ Q w.1) 1 0))
  /- Inductive case: -/
  exact
    (ite (P w.1))
    (
      dite (n ≥ L.succ)
      (λ h ↦ n_ih ⟨List.nil, by {rw [Nat.sub_eq_zero_of_le h];rfl}⟩ )
      (
        λ h ↦ List.sum (
          List.map (λ a ↦ (n_ih (Gap_cons b a w h))) (List.ofFn id) -- this much does not rely on it being Fin 2
        )
      )
    )
    0
}

def those_with_suffix {k b :ℕ} {L:ℕ} (M : MonoPred b) [DecidablePred M.P] (w : Gap b L.succ k) : Finset (Vector (Fin b) L.succ) :=
by {
  induction k
  -- Base case:
  exact ((ite (M.P w.1) {w} ∅))
  -- Inductive case:
  exact
    (ite (M.P w.1))
    (
      dite (n ≥ L.succ)
      (λ h ↦ n_ih ⟨List.nil, by {rw [Nat.sub_eq_zero_of_le h];rfl}⟩ )
      (
        λ h ↦ Finset.biUnion (Finset.univ : Finset (Fin b)) (
          (λ a ↦ (n_ih (Gap_cons b a w h)))
        )
      )
    )
    ∅
}

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
      (λ h ↦ n_ih ⟨List.nil, by {rw [Nat.sub_eq_zero_of_le h];rfl}⟩ )
      (
        λ h ↦ Finset.biUnion (Finset.univ : Finset (Fin b)) (
          (λ a ↦ (n_ih (Gap_cons b a w h)))
        )
      )
    )
    ∅
}

def SQF (b:ℕ) : MonoPred b := {
  P := (λ w : List (Fin b) ↦ squarefree w)
  preserved_under_suffixes := suffix_squarefree b
}

def CBF (b:ℕ): MonoPred b := {
  P := (λ w : List (Fin b) ↦ cubefree w)
  preserved_under_suffixes := suffix_cubefree b
}


-- #eval moves_fin [0,2,2]
-- #eval moves_fin [0,2,2,1,1]


instance (b:ℕ): DecidablePred ((SQF b).P) := by {
  unfold SQF
  simp
  exact inferInstance
}

instance  (b:ℕ): DecidablePred ((CBF b).P) := by {
  unfold CBF
  simp
  exact inferInstance
}


theorem cons_suffix (b:ℕ)
{L n_1: ℕ} {a : Fin b}
(h: ¬n_1 ≥ Nat.succ L)
(w: Vector (Fin b) (Nat.succ L -  (Nat.succ n_1)))

: w.1 <:+ (Gap_cons b a w h).1 := by {
  exists [a];
}

lemma still_does_not_hold
{b L z: ℕ }
{M: MonoPred b}
{w: Gap b (Nat.succ L) (Nat.succ z)}
(h: ¬z ≥ Nat.succ L)
(H: ¬M.P w.1)
: ∀ a, ¬ M.P (Gap_cons b a w h).1 := by
  intro a hc; exact H (M.preserved_under_suffixes w.1 (Gap_cons b a w h).1 (cons_suffix b _ _) hc)

lemma still_does_not_hold''
{b L z: ℕ }
{M: MonoPred b}
{w: Gap b (Nat.succ L) (Nat.succ z)}
(h: ¬z ≥ Nat.succ L)
(H: ¬(M.P w.1))
: ∀ a, ¬ (M.P (Gap_cons b a w h).1 ∧ M.Q (Gap_cons b a w h).1) := by
  intro a hc;
  -- need : P ∧ Q is also preserved under suffixes... not true though
  exact H (M.preserved_under_suffixes w.1 (Gap_cons b a w h).1 (cons_suffix b _ _) hc.1)

theorem branch_out'' (b:ℕ) {n L:ℕ} (M:MonoPred b)[DecidablePred M.P][DecidablePred M.Q]
(hnL: ¬ n ≥ L.succ) (w : Gap b L.succ n.succ) :
  count_those_with_suffix'' M.P M.Q (w)
  = List.sum (List.map (λ a ↦ count_those_with_suffix'' M.P M.Q (Gap_cons b a w hnL)) (List.ofFn id))
  := by
  induction n
  -- Base step:
  unfold count_those_with_suffix''
  simp
  intro H

  -- BLOCK
  symm
  have : List.ofFn (fun a => ite (
    M.P (Gap_cons b a w (by linarith)).1
    ∧
    M.Q (Gap_cons b a w (by linarith)).1
  ) 1 0)
        = List.replicate b 0 := by
    refine List.eq_replicate.mpr ?_
    constructor
    simp
    intro i hi
    simp at hi
    rw [List.mem_iff_get] at hi
    rcases hi with ⟨n,hn⟩
    simp at hn
    rw [if_neg (still_does_not_hold'' _ H _)] at hn
    exact hn.symm
  rw [this]
  apply List.sum_const_nat b 0
    -- Inductive step:
  unfold count_those_with_suffix''
  simp
  by_cases H : (M.P w.1)
  rw [if_pos H,dif_neg hnL]

  rw [if_neg H]
  symm
  have hlen {n:ℕ} (h : Nat.succ L ≤ n): List.length ([]: List (Fin (L.succ - n))) = Nat.succ L - n
    := by {simp;exact (Nat.sub_eq_zero_of_le h).symm}
  let Recu := Nat.rec
          (motive := fun {k} => Gap b (Nat.succ L) k → ℕ)
          (fun w => ite (M.P w.1 ∧ M.Q w.1) 1 0) -- needs a Q
          (fun n n_ih w =>
            if M.P w.1 then -- doesn't need a Q
              if h : Nat.succ L ≤ n then        n_ih ⟨[], hlen h⟩
              else List.sum (List.ofFn fun a => n_ih (Gap_cons b a w h))
            else 0)
  have : (List.ofFn fun a =>
    if M.P (Gap_cons b a w hnL).1
    then
      if h : Nat.succ L ≤ n_1 then
        Recu n_1 ⟨[], hlen h⟩
      else
        List.sum (List.ofFn fun a_1 => Recu n_1 (Gap_cons b a_1 (Gap_cons b a w hnL) h))
    else 0)
    = List.replicate b 0 := by {
    refine List.eq_replicate.mpr ?_
    constructor
    simp
    intro i hi
    simp at hi
    rw [List.mem_iff_get] at hi
    rcases hi with ⟨n,hn⟩
    simp at hn
    rw [if_neg (still_does_not_hold _ H _)] at hn
    exact hn.symm
  }
  rw [this]
  apply List.sum_const_nat b 0




theorem branch_out (b:ℕ) {n L:ℕ} (M:MonoPred b)[DecidablePred M.P]
(hnL: ¬ n ≥ L.succ) (w : Gap b L.succ n.succ) :
  count_those_with_suffix M (w)
  = List.sum (List.map (λ a ↦ count_those_with_suffix M (Gap_cons b a w hnL)) (List.ofFn id))
  := by {
    induction n
    -- Base step:
    unfold count_those_with_suffix
    simp
    intro H

    -- BLOCK
    symm
    have : List.ofFn (fun a => ite (M.P (Gap_cons b a w (by linarith)).1) 1 0)
         = List.replicate b 0 := by {
      refine List.eq_replicate.mpr ?_
      constructor
      simp
      intro i hi
      simp at hi
      rw [List.mem_iff_get] at hi
      rcases hi with ⟨n,hn⟩
      simp at hn
      rw [if_neg (still_does_not_hold _ H _)] at hn
      exact hn.symm
    }
    rw [this]
    apply List.sum_const_nat b 0
    -- END OF BLOCK

    -- Inductive step:
    unfold count_those_with_suffix
    simp
    by_cases H : (M.P w.1)
    rw [if_pos H,dif_neg hnL]

    rw [if_neg H]
    -- BLOCK

    symm
    have hlen {n:ℕ} (h : Nat.succ L ≤ n): List.length ([]: List (Fin (L.succ - n))) = Nat.succ L - n
      := by {simp;exact (Nat.sub_eq_zero_of_le h).symm}

    let Recu := Nat.rec
            (motive := fun {k} => Gap b (Nat.succ L) k → ℕ)
            (fun w => ite (M.P w.1) 1 0) -- needs a Q
            (fun n n_ih w =>
              if M.P w.1 then -- doesn't need a Q
                if h : Nat.succ L ≤ n then        n_ih ⟨[], hlen h⟩
                else List.sum (List.ofFn fun a => n_ih (Gap_cons b a w h))
              else 0)
    -- Jan.25: before implementing Q need to understand this better,
    -- or replace it with whatever the new goal is


    have : (List.ofFn fun a =>
      if M.P (Gap_cons b a w hnL).1 then
        if h : Nat.succ L ≤ n_1 then
          Recu n_1 ⟨[], hlen h⟩
        else
          List.sum (List.ofFn fun a_1 => Recu n_1 (Gap_cons b a_1 (Gap_cons b a w hnL) h))
      else 0)
     = List.replicate b 0 := by {
      refine List.eq_replicate.mpr ?_
      constructor
      simp
      intro i hi
      simp at hi
      rw [List.mem_iff_get] at hi
      rcases hi with ⟨n,hn⟩
      simp at hn
      rw [if_neg (still_does_not_hold _ H _)] at hn
      exact hn.symm
    }
    rw [this]
    apply List.sum_const_nat b 0
    -- END OF BLOCK
  }



theorem subtype_ext {α:Type} (P Q:α→ Prop) (h : ∀ x, P x ↔ Q x):
 {x : α // P x} =  {x : α // Q x} := by {
  have : ∀ x, P x = Q x := fun x => propext (h x)
  have : P = Q := funext this
  exact congrArg Subtype this
}

theorem fincard_ext {α:Type} (P Q:α→ Prop) (h : ∀ x, P x ↔ Q x) [Fintype {x : α // P x}][Fintype {x : α // Q x}] :
  Fintype.card {x : α // P x} = Fintype.card {x : α // Q x} := by {
  have H: {x // P x} = {x // Q x} := subtype_ext P Q h
  simp_rw [H]
}


theorem Vector_eq_of_suffix_of_length_eq {L b:ℕ} {w : Vector (Fin b) L}
{v : Vector (Fin b) L} (hv : w.1 <:+ v.1) : w.1 = v.1
:= List.eq_of_suffix_of_length_eq hv (by {rw [v.2,w.2]})


theorem disjoint_branch  {L b: ℕ} {i j : Fin b} (hp: i ≠ j) {M:MonoPred b} --[DecidablePred M.P]
  {n:ℕ} (w: Vector (Fin b) (L.succ-n.succ)) (h : ¬ n ≥ L.succ) -- these don't need to be explicit
  :
  Disjoint (λ v  : Vector (Fin b) L.succ ↦ M.P v.1 ∧ (Gap_cons b i w h).1 <:+ v.1 )
           (λ v  : Vector (Fin b) L.succ ↦ M.P v.1 ∧ (Gap_cons b j w h).1 <:+ v.1 ) := by {
  intro S h0S h1S v hSv
  rcases (h0S v hSv).2 with ⟨t₁,ht₁⟩
  rcases (h1S v hSv).2 with   ⟨t₀,ht₀⟩

  have : t₁ ++ [i] ++ w.1 = t₀ ++ [j] ++ w.1 := calc
                        _ = t₁ ++ i :: w.1   := (List.append_cons t₁ i w.1).symm
                        _ = v.1              := ht₁
                        _ = t₀ ++ j :: w.1   := ht₀.symm
                        _ = _                := (List.append_cons t₀ j w.1)

  have : (t₁ ++ [i]).getLast (by simp)
       = (t₀ ++ [j]).getLast (by simp) := List.getLast_congr _ _ ((List.append_left_inj w.1).mp this)
  simp at this
  exact hp this
}

theorem disjoint_branch''  {L b: ℕ} {i j : Fin b} (hp: i ≠ j) {M:MonoPred b} --[DecidablePred M.P]
  {n:ℕ} (w: Vector (Fin b) (L.succ-n.succ)) (h : ¬ n ≥ L.succ) -- these don't need to be explicit
  :
  Disjoint (λ v  : Vector (Fin b) L.succ ↦ (M.P v.1 ∧ M.Q v.1) ∧ (Gap_cons b i w h).1 <:+ v.1 )
           (λ v  : Vector (Fin b) L.succ ↦ (M.P v.1 ∧ M.Q v.1) ∧ (Gap_cons b j w h).1 <:+ v.1 ) := by {
  intro S h0S h1S v hSv
  rcases (h0S v hSv).2 with ⟨t₁,ht₁⟩
  rcases (h1S v hSv).2 with   ⟨t₀,ht₀⟩

  have : t₁ ++ [i] ++ w.1 = t₀ ++ [j] ++ w.1 := calc
                        _ = t₁ ++ i :: w.1   := (List.append_cons t₁ i w.1).symm
                        _ = v.1              := ht₁
                        _ = t₀ ++ j :: w.1   := ht₀.symm
                        _ = _                := (List.append_cons t₀ j w.1)

  have : (t₁ ++ [i]).getLast (by simp)
       = (t₀ ++ [j]).getLast (by simp) := List.getLast_congr _ _ ((List.append_left_inj w.1).mp this)
  simp at this
  exact hp this
}

theorem Vector_append_succ {L n b: ℕ}
{w: Vector (Fin b) (Nat.succ L - Nat.succ n)}
{v: Vector (Fin b) (Nat.succ L)} {t: List (Fin b)} (ht: t ++ w.1 = v.1) :
t ≠ List.nil := by {
  intro hc; rw [hc] at ht; simp at ht; have : w.1.length = v.1.length := congr_arg _ ht
  rw [w.2,v.2] at this; contrapose this; simp; intro hL
  have : L.succ ≤ L := calc
              _ = L - n := hL.symm
              _ ≤ L := Nat.sub_le L n
  cases (Nat.lt_or_eq_of_le this); contrapose h; linarith; contrapose h; exact Nat.succ_ne_self L
}

theorem List_reverse_ne_nil {α : Type} {t : List α} (hlong : t ≠ List.nil) : t.reverse ≠ List.nil
  := by {
      intro hc; have : t.reverse.reverse = [].reverse := congrArg List.reverse hc
      simp at this; exact hlong this
    }

theorem List_reverse_cons {α : Type} {s t: List α} {a: α} (hs: t.reverse = a :: s)
: t = s.reverse ++ [a] := by
    have hsr : t.reverse.reverse = (a :: s).reverse := congrArg List.reverse hs
    simp at hsr; rw [hsr]

lemma distribute₀ {L n : ℕ}
   (w : Vector (Fin 2) (Nat.succ L - Nat.succ n)) (h : ¬n ≥ Nat.succ L)
   (v : Vector (Fin 2) L.succ) : w.1 <:+ v.1 ↔
    ( (Gap_cons 2 0 w h).1 <:+ v.1)
  ∨ ( (Gap_cons 2 1 w h).1 <:+ v.1)  := by {
    constructor; intro h
    rcases h with ⟨t,ht⟩
    have hlong: t ≠ List.nil := Vector_append_succ ht
    rcases (List.exists_cons_of_ne_nil (List_reverse_ne_nil hlong)) with ⟨a,ha⟩
    rcases ha with ⟨s,hs⟩
    let hr := List_reverse_cons hs
    by_cases ha: (a=0)

    left; exists s.reverse; rw [← ht,hr]; subst ha; simp; rfl

    have ha: a = 1 := Fin.eq_one_of_neq_zero a ha

    right; exists s.reverse; rw [← ht,hr]; subst ha; simp; rfl

    intro hi; cases hi
    rcases h_1 with ⟨u,hu⟩; exists u ++ [0]; rw [← hu]; simp; rfl
    rcases h_1 with ⟨u,hu⟩; exists u ++ [1]; rw [← hu]; simp; rfl
  }

lemma distribute {L n : ℕ}
  (M : Prop) (w : Vector (Fin 2) (Nat.succ L - Nat.succ n)) (h : ¬n ≥ Nat.succ L)
  (v : Vector (Fin 2) L.succ) : M ∧ w.1 <:+ v.1 ↔
    (M ∧ (Gap_cons 2 0 w h).1 <:+ v.1) ∨ (M ∧ (Gap_cons 2 1 w h).1 <:+ v.1)  :=
  by {
    let G := distribute₀ w h v; tauto
  }

lemma prefix_of_same {L b: ℕ} (w: Vector (Fin b) L)
: ∀ x y : {v : Vector (Fin b) L // w.1 <:+ v.1}, x.1 = y.1 := by {
    intro x y
    have : x.1.1 = y.1.1 := calc
               _ = w.1   := (Vector_eq_of_suffix_of_length_eq x.2).symm
               _ = _     :=  Vector_eq_of_suffix_of_length_eq y.2
    exact SetCoe.ext this
  }


lemma list_sum_ofFn_succ {n:ℕ} (f:Fin n.succ → ℕ):
List.sum (List.ofFn (λ i ↦ f i))
=
List.sum (List.ofFn (λ i : Fin n ↦ f i))
+
f n
:= by {
  rw [List.sum_ofFn]
  rw [List.sum_ofFn]
  simp
  exact Fin.sum_univ_castSucc fun i => f i
}


lemma disjoint_from_last {α: Type} {n_1: ℕ} {p: Fin (Nat.succ n_1) → α → Prop}
(h: ∀ (i j : Fin (Nat.succ n_1)), i ≠ j → Disjoint (p i) (p j))
: Disjoint (λ x : α ↦ ∃ i, p (Fin.castSucc i) x) (λ x : α ↦ p (n_1) x) := by
    intro S hS₀ hS₁ x hSx
    rcases hS₀ x hSx with ⟨i,hi⟩

    let hj := hS₁ x hSx
    simp at hj
    have hi': (λ y ↦ y=x) ≤ p i := by {
      intro y hy; rw [hy]
      have : (@Nat.cast (Fin (Nat.succ n_1)) Semiring.toNatCast i : Fin (Nat.succ n_1)) = Fin.castSucc i
        := by simp
      rw [this]; exact hi
    }
    have hj': (λ y ↦ y=x) ≤ p n_1 := by {
      intro y hy; rw [hy]
      have : (@Nat.cast (Fin (Nat.succ n_1)) Semiring.toNatCast n_1 : Fin (Nat.succ n_1))
      = Fin.last n_1 := by simp
      rw [this]; exact hj
    }
    have : (Fin.castSucc i).1 ≠ n_1 := by {
      intro hc; have G : i.1 < n_1 := i.2
      have : (Fin.castSucc i).1 = i.1 := rfl
      rw [this] at hc; rw [hc] at G; exact LT.lt.false G
    }
    have : (Fin.castSucc i) ≠ n_1 := by {
      intro hc; let G := congr_arg (λ x ↦ x.1) hc; simp at G; exact this G
    }
    have : (@Nat.cast (Fin (Nat.succ n_1)) Semiring.toNatCast ↑i : Fin (Nat.succ n_1)) ≠ n_1 := by norm_cast
    exact h i n_1 this hi' hj' x rfl

def getFin {n_1 : ℕ} {i: Fin (Nat.succ n_1)} (hin: ¬i = ↑n_1) : Fin n_1 := by {
  have : i.1 < n_1 ∨ i.1 = n_1 := Nat.lt_or_eq_of_le (Fin.is_le i)
  have : i.1 < n_1 := by {
    cases this; exact h; exfalso
    have : i = n_1 := by apply Fin.ext; rw [h]; simp
    exact hin this
  }
  exact ⟨i.1,this⟩
}

lemma distinguish_from_last {α: Type} {n_1: ℕ} {p: Fin (Nat.succ n_1) → α → Prop} (x : α)
: (∃ i, p (Fin.castSucc i) x) ∨ p (↑n_1) x ↔ ∃ i, p i x := by
  constructor; intro ha; cases ha; rcases h with ⟨i,hi⟩
  exists i; norm_cast
  exists n_1; intro ha; rcases ha with ⟨i,hi⟩; by_cases hin:(i=n_1)
  right; rw [← hin]; exact hi; left
  exists getFin hin -- ⟨i.1,_⟩

def getFin_pred {n_1:ℕ} (i: Fin n_1.pred) : i < n_1 := calc
  i.1 < n_1.pred := i.2
  _   ≤ n_1      := Nat.pred_le n_1

lemma disjoint_cast {α: Type} {n_1: ℕ} {p: Fin (Nat.succ n_1) → α → Prop}
(h: ∀ (i j : Fin (Nat.succ n_1)), i ≠ j → Disjoint (p i) (p j))
 : (∀ (i j : Fin n_1), i ≠ j → Disjoint (p (Fin.castSucc i)) (p (Fin.castSucc j)))
:= by
  intro i j hij
  have : Fin.castSucc i ≠ Fin.castSucc j := by {
    intro hc
    have : i = j := Fin.castSucc_inj.mp hc
    tauto
  }
  have : (@Nat.cast (Fin (Nat.succ n_1)) Semiring.toNatCast ↑i : Fin (Nat.succ n_1))
       ≠ (@Nat.cast (Fin (Nat.succ n_1)) Semiring.toNatCast ↑j : Fin (Nat.succ n_1)) := by
    intro hc; simp at hc; exfalso; exact this hc
  let G := h i j this
  norm_cast at G

lemma input_to_fintype {α:Type} [Fintype α]
  {n_1 : ℕ} {p : Fin n_1.succ → α → Prop}
  [h₀: DecidablePred fun x => ∃ i : Fin n_1, p (Fin.castSucc i) x] (x : α)
  : x ∈ (Finset.filter (fun x => ∃ i : Fin n_1, p (Fin.castSucc i) x) Finset.univ)
                               ↔ ∃ i,           p (Fin.castSucc i) x
  := by {
    have : x ∈ (Finset.filter (fun x => ∃ i : Fin n_1, p (Fin.castSucc i) x) Finset.univ)
         ↔ x ∈ Finset.univ ∧            ∃ i : Fin n_1, p (Fin.castSucc i) x
      := Finset.mem_filter
    constructor
    intro hxs
    exact (this.mp hxs).2

    intro h
    exact this.mpr (And.intro (Finset.mem_univ x) h)
  }

theorem Fintype_card_subtype_or_disjoint' {α:Type} [Fintype α]
{n:ℕ} (p : Fin n → α → Prop)
-- January 30, 2024. Can use this as "hcard" below.
[Fintype {x:α // ∃ i, p i x}]
[∀ i, Fintype {x:α // p i x}]
[DecidablePred fun x => ∃ i : Fin n.pred, p ⟨i,getFin_pred i⟩ x]
(h : ∀ i j, i ≠ j → Disjoint (p i) (p j))
:
List.sum (List.ofFn (λ i ↦ Fintype.card {x:α // p i x}))
                         = Fintype.card {x:α // ∃ i, p i x}
:= by {
  induction n; simp
  rename_i h₀ h₁ h₂
  have h₀: DecidablePred fun x => ∃ i, p (Fin.castSucc i) x := h₂
  let s := Finset.filter
    (λ x ↦ ∃ i : Fin n_1, p (Fin.castSucc i) x) (Finset.univ : Finset α)
  have : Fintype { x : α // ∃ i : Fin n_1, p (Fin.castSucc i) x } := Fintype.subtype s input_to_fintype

  rw [list_sum_ofFn_succ]
  norm_cast

  have hdec : DecidablePred
    fun x : α => ∃ i : Fin n_1.pred, (fun i a => p (Fin.castSucc i) a) ⟨i.1, getFin_pred i⟩ x :=
    Classical.decPred
    fun x    => ∃ i : Fin n_1.pred, (fun i a => p (Fin.castSucc i) a) {val := ↑i, isLt := (_ : ↑i < n_1)} x

  rw [n_ih (λ i a ↦ p (Fin.castSucc i) a) (disjoint_cast h)]

  have h₀ : Fintype { x : α // (∃ i, p (Fin.castSucc i) x) ∨ p (↑n_1) x } :=
       Fintype.ofFinite { x // (∃ i, p (Fin.castSucc i) x) ∨ p (↑n_1) x }
  let G := Fintype.card_subtype_or_disjoint _ _ (disjoint_from_last h)
  rw [← G]; apply fincard_ext; exact distinguish_from_last
}

theorem verification_of_recursive_backtracking_with_predicate (k b L:ℕ)
/- This verifies recursive backtracking for b-ary trees with monotone predicates P,
   with a non-monotone Q at the leaves. January 31, 2024.
-/
(bound : k ≤ L.succ) (M:MonoPred b) [DecidablePred M.P] [DecidablePred M.Q]
(w : Vector (Fin b) (L.succ-k)):
  Fintype.card {v : Vector (Fin b) L.succ // (M.P v.1 ∧ M.Q v.1) ∧ w.1 <:+ v.1}
  = count_those_with_suffix'' M.P M.Q w := by
  induction k
  unfold count_those_with_suffix''; simp
  by_cases hs : (M.P w.1 ∧ M.Q w.1)
  rw [if_pos hs]
  let _ := subsingleton_iff.mpr (
    λ x y : {v : Vector (Fin b) L.succ // (M.P v.1 ∧ M.Q v.1) ∧ w.1 <:+ v.1} ↦ SetCoe.ext (prefix_of_same w ⟨x.1,x.2.2⟩ ⟨y.1,y.2.2⟩)
  )
  let _ := uniqueOfSubsingleton
    (⟨w,⟨hs, List.suffix_rfl⟩⟩ : {v : Vector (Fin b) L.succ // (M.P v.1 ∧ M.Q v.1) ∧ w.1 <:+ v.1})
  exact Fintype.card_unique

  rw [if_neg hs]
  have : ∀ v: Vector (Fin b) L.succ ,¬ ((M.P v.1 ∧ M.Q v.1) ∧ w.1 <:+ v.1) := by {
    intro v hc
    have : w = v := SetCoe.ext (Vector_eq_of_suffix_of_length_eq hc.2)
    subst this
    tauto
  }
  let _ := Subtype.isEmpty_of_false this
  exact Fintype.card_eq_zero
  -- Inductive step:
  by_cases case : (n ≥ L.succ)

  exfalso
  have : n.succ ≤ n := calc
              _ ≤ L.succ := bound
              _ ≤ n      := case
  exact Nat.not_succ_le_self n this
  -- Nontrivial case:
  let α := Vector (Fin b) L.succ
  have hcard : List.sum (
    List.ofFn (
      λ i ↦ Fintype.card {x:α //      (λ i : Fin b ↦ λ v : α ↦ (M.P v.1 ∧ M.Q v.1) ∧ (Gap_cons b i w case).1 <:+ v.1) i x}
    )
  )       = Fintype.card {x:α // ∃ i, (λ i : Fin b ↦ λ v : α ↦ (M.P v.1 ∧ M.Q v.1) ∧ (Gap_cons b i w case).1 <:+ v.1) i x} :=
    Fintype_card_subtype_or_disjoint' _ (λ _ _ hij ↦ disjoint_branch'' hij w case)
  rw [branch_out'' _ _ case] -- this is the hard part. need a version for count_those_with_suffix''

  let G := λ i : Fin b ↦ n_ih (Nat.le_of_lt bound) (Gap_cons b i w case)
  let H := funext G
  rw [← H]

  simp at hcard
  simp
  rw [hcard]
  -- The rest is like "distribute"
  apply fincard_ext
  intro x
  constructor
  intro h
  constructor
  tauto
  rcases h.2 with ⟨t,ht⟩

  have hlong: t ≠ List.nil := Vector_append_succ ht
  rcases (List.exists_cons_of_ne_nil (List_reverse_ne_nil hlong)) with ⟨a,ha⟩
  rcases ha with ⟨s,hs⟩
  let hr := List_reverse_cons hs
  exists a
  exists s.reverse
  rw [← ht,hr];
  simp; rfl


  intro hi;
  constructor
  tauto

  rcases hi.2 with ⟨a,ha⟩;
  rcases ha with ⟨t,ht⟩
  exists t ++ [a]
  rw [← ht]
  simp
  rfl


instance (k b L f:ℕ)
(bound : k ≤ L.succ) (M:MonoPred b) [DecidablePred M.P] [DecidablePred M.Q]
(w : Vector (Fin b) (L.succ-k)):
  Decidable (Fintype.card {v : Vector (Fin b) L.succ // (M.P v.1 ∧ M.Q v.1) ∧ w.1 <:+ v.1} =f)
:= decidable_of_iff (count_those_with_suffix'' M.P M.Q w = f) (by {
  constructor
  intro h; rw [← h]; exact verification_of_recursive_backtracking_with_predicate _ _ _ bound _ _
  intro h; rw [← h]; exact (verification_of_recursive_backtracking_with_predicate _ _ _ bound _ _).symm
})


-- #eval Fintype.card {v : Vector (Fin 3) 3 // (squarefree v.1 ∧ True) ∧ [] <:+ v.1}
-- #eval Fintype.card {v : Vector (Fin 3) 4 // (squarefree v.1 ∧ True) ∧ [] <:+ v.1}
-- #eval Fintype.card {v : Vector (Fin 3) 5 // (squarefree v.1 ∧ True) ∧ [] <:+ v.1}
-- #eval Fintype.card {v : Vector (Fin 3) 6 // (squarefree v.1 ∧ True) ∧ [] <:+ v.1}
-- #eval Fintype.card {v : Vector (Fin 3) 7 // (squarefree v.1 ∧ True) ∧ [] <:+ v.1}
-- #eval Fintype.card {v : Vector (Fin 3) 8 // (squarefree v.1 ∧ True) ∧ [] <:+ v.1}
-- #eval Fintype.card {v : Vector (Fin 3) 9 // (squarefree v.1 ∧ True) ∧ [] <:+ v.1}
-- #eval Fintype.card {v : Vector (Fin 3) 10 // (squarefree v.1 ∧ True) ∧ [] <:+ v.1}
-- example :
-- Fintype.card {v : Vector (Fin 3) 10 // (squarefree v.1 ∧ True) ∧ [] <:+ v.1} = 3 := by decide


theorem verification_of_recursive_backtracking (k b L:ℕ)
-- which parts works with a "Q" attached?
(bound : k ≤ L.succ) (M:MonoPred b) [DecidablePred M.P]
(w : Vector (Fin b) (L.succ-k)):
  Fintype.card {v : Vector (Fin b) L.succ // M.P v.1 ∧ w.1 <:+ v.1}
  = count_those_with_suffix M w := by
  induction k
  unfold count_those_with_suffix; simp
  by_cases hs : (M.P w.1)
  rw [if_pos hs]
  let _ := subsingleton_iff.mpr (
    λ x y : {v : Vector (Fin b) L.succ // M.P v.1 ∧ w.1 <:+ v.1} ↦ SetCoe.ext (prefix_of_same w ⟨x.1,x.2.2⟩ ⟨y.1,y.2.2⟩)
  )
  let _ := uniqueOfSubsingleton
    (⟨w,⟨hs, List.suffix_rfl⟩⟩ : {v : Vector (Fin b) L.succ // M.P v.1 ∧ w.1 <:+ v.1})
  exact Fintype.card_unique

  rw [if_neg hs]
  have : ∀ v: Vector (Fin b) L.succ ,¬ (M.P v.1 ∧ w.1 <:+ v.1) := by {
    intro v hc
    have : w = v := SetCoe.ext (Vector_eq_of_suffix_of_length_eq hc.2)
    subst this
    exact hs hc.1
  }
  let _ := Subtype.isEmpty_of_false this
  exact Fintype.card_eq_zero
  -- Inductive step:
  by_cases case : (n ≥ L.succ)

  exfalso
  have : n.succ ≤ n := calc
              _ ≤ L.succ := bound
              _ ≤ n      := case
  exact Nat.not_succ_le_self n this
  -- Nontrivial case:
  let α := Vector (Fin b) L.succ
  have hcard : List.sum (
    List.ofFn (
      λ i ↦ Fintype.card {x:α //      (λ i : Fin b ↦ λ v : α ↦ M.P v.1 ∧ (Gap_cons b i w case).1 <:+ v.1) i x}
    )
  )       = Fintype.card {x:α // ∃ i, (λ i : Fin b ↦ λ v : α ↦ M.P v.1 ∧ (Gap_cons b i w case).1 <:+ v.1) i x} :=
    Fintype_card_subtype_or_disjoint' _ (λ _ _ hij ↦ disjoint_branch hij w case)
  rw [branch_out _ _ case]

  let G := λ i : Fin b ↦ n_ih (Nat.le_of_lt bound) (Gap_cons b i w case)
  let H := funext G
  rw [← H]

  simp at hcard
  simp
  rw [hcard]
  -- The rest is like "distribute"
  apply fincard_ext
  intro x
  constructor
  intro h
  constructor
  tauto
  rcases h.2 with ⟨t,ht⟩

  have hlong: t ≠ List.nil := Vector_append_succ ht
  rcases (List.exists_cons_of_ne_nil (List_reverse_ne_nil hlong)) with ⟨a,ha⟩
  rcases ha with ⟨s,hs⟩
  let hr := List_reverse_cons hs
  exists a
  exists s.reverse
  rw [← ht,hr];
  simp; rfl


  intro hi;
  constructor
  tauto

  rcases hi.2 with ⟨a,ha⟩;
  rcases ha with ⟨t,ht⟩
  exists t ++ [a]
  rw [← ht]
  simp
  rfl

-- The b=2 version:
theorem formal_verification_of_recursive_backtracking (k L:ℕ) (bound : k ≤ L.succ) (M:MonoPred 2) [DecidablePred M.P]
(w : Vector (Fin 2) (L.succ-k)):
  Fintype.card {v : Vector (Fin 2) L.succ // M.P v.1 ∧ w.1 <:+ v.1}
  = count_those_with_suffix M w
:= verification_of_recursive_backtracking _ _ _ bound _ _
-- := by {
--   induction k

--   unfold count_those_with_suffix; simp
--   by_cases hs : (M.P w.1)

--   rw [if_pos hs]
--   let _ := subsingleton_iff.mpr (
--     λ x y : {v : Vector (Fin 2) L.succ // M.P v.1 ∧ w.1 <:+ v.1} ↦ SetCoe.ext (prefix_of_same w ⟨x.1,x.2.2⟩ ⟨y.1,y.2.2⟩)
--   )
--   let _ := uniqueOfSubsingleton
--     (⟨w,⟨hs, List.suffix_rfl⟩⟩ : {v : Vector (Fin 2) L.succ // M.P v.1 ∧ w.1 <:+ v.1})
--   exact Fintype.card_unique

--   rw [if_neg hs]
--   have : ∀ v: Vector (Fin 2) L.succ ,¬ (M.P v.1 ∧ w.1 <:+ v.1) := by {
--     intro v hc
--     have : w = v := SetCoe.ext (Vector_eq_of_suffix_of_length_eq hc.2)
--     subst this
--     exact hs hc.1
--   }
--   let _ := Subtype.isEmpty_of_false this
--   exact Fintype.card_eq_zero
--   -- Induction step:
--   by_cases case : (n ≥ L.succ)

--   exfalso
--   have : n.succ ≤ n := calc
--               _ ≤ L.succ := bound
--               _ ≤ n      := case
--   exact Nat.not_succ_le_self n this

--   -- The nontrivial case:
--   let g₀ := Gap_cons 2 0 w case --(0 ::ᵥ w)
--   let g₁ := Gap_cons 2 1 w case

--   have halt: ∀ v : Vector (Fin 2) L.succ, M.P v.1 ∧ w.1 <:+ v.1 ↔
--     (M.P v.1 ∧ g₀.1 <:+ v.1) ∨ (M.P v.1 ∧ g₁.1 <:+ v.1)  := λ v ↦ distribute (M.P v.1) _ _ _

--   have hcard: Fintype.card { v : Vector (Fin 2) L.succ // M.P v.1 ∧ w.1 <:+ v.1 }
--             = Fintype.card { v : Vector (Fin 2) L.succ // M.P v.1 ∧ g₀.1 <:+ v.1 }
--             + Fintype.card { v : Vector (Fin 2) L.succ // M.P v.1 ∧ g₁.1 <:+ v.1 }
--     := by rw [
--       fincard_ext _ _ halt,
--       ← Fintype.card_subtype_or_disjoint _ _ (disjoint_branch zero_ne_one _ _)
--     ]

--   rw [hcard,branch_out,n_ih (Nat.le_of_lt bound) g₀,n_ih (Nat.le_of_lt bound) g₁]
--   simp
--   exact case
-- }
