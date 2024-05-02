import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Algebra.BigOperators.Fin
import MyProject.Squarefree
import MyProject.MonoPred
set_option maxHeartbeats 3000000

/- We formally verify the method known as recursive backtracking
for a monotone predicate P and another predicate Q at the leaves. -/

-- A vector of length L monus k, thought of as a possible suffix for a word of length L
-- in which the first k bits are unspecified
-- For example, a Gap 10 10 has length 10 - 10.
def Gap (b L k : ℕ) : Type := Vector (Fin b) (L - k)

/- Note that Gap_cons requires the use of L.succ instead of just L. -/
def Gap_cons {n L b:ℕ} (a:Fin b) (w : Gap b L.succ n.succ)
                  (h: ¬ n ≥ L.succ) : Gap b L.succ n
  := ⟨a :: w.1, by simp only [List.length_cons, Vector.length_val,
    Nat.succ_sub_succ_eq_sub];exact (Nat.succ_sub (Nat.not_lt.mp h)).symm⟩

def Gap_nil {k b L : ℕ} (h : k ≥ L) : Gap b L k
  := ⟨List.nil, by simp only [List.length_nil];rw [Nat.sub_eq_zero_of_le h]⟩

def Gap_nil'  (b n : ℕ)             : Gap b n n := ⟨[], by simp⟩

/-- The number of strings satisfying `P ∧ Q`, where
`P` is a monotone predicate and `Q` is a predicate at the leaves.-/
def num_by_backtracking {k b L:ℕ}
  (P: List (Fin b) → Prop) [DecidablePred P]
  (Q: List (Fin b) → Prop) [DecidablePred Q]
  (w : Gap b L.succ k) : ℕ :=
by {
  induction k
  exact ((if (P w.1 ∧ Q w.1) then 1 else 0))   /- Base case -/
  rename_i n n_ih
  exact  /- Inductive case -/
    (ite (P w.1)) (dite (n ≥ L.succ)
      (λ h ↦                             n_ih (Gap_nil        h) )
      (λ h ↦ List.sum (List.ofFn (λ a ↦ (n_ih (Gap_cons a w h)))))
    ) 0
}

/-- The list `w` is a suffix of `a :: w`, in the setting of the `Gap` types. -/
theorem cons_suffix {b:ℕ} {L n_1: ℕ} {a : Fin b} (h: ¬n_1 ≥ Nat.succ L)
(w: Vector (Fin b) (Nat.succ L -  (Nat.succ n_1)))
: w.1 <:+ (Gap_cons a w h).1 := by exists [a]

/-- Preservation under suffices for `M.P`, for the `Gap` types.-/
lemma still_holds
{b L z: ℕ }
{M: MonoPred b}
{w: Gap b (Nat.succ L) (Nat.succ z)}
(h: ¬z ≥ Nat.succ L) (a : Fin b)
(H: M.P (Gap_cons a w h).1)
: M.P w.1 := (M.preserved_under_suffixes w.1 (Gap_cons a w h).1 (cons_suffix _ _)) H


/-- Contrapositive of `still_holds`.-/
lemma still_does_not_hold
{b L z: ℕ }
{M: MonoPred b}
{w: Gap b (Nat.succ L) (Nat.succ z)}
(h: ¬z ≥ Nat.succ L) (a : Fin b)
(H: ¬M.P w.1)
: ¬ M.P (Gap_cons a w h).1 := by
  contrapose H; simp only [not_not] at *;exact still_holds h a H

/-- Contrapositive of: for monotone `P`, if `P ∧ Q` holds of `a::w` then `P` holds of `w`. -/
lemma still_does_not_hold''
{b L z: ℕ }
{M: MonoPred b}
{w: Gap b (Nat.succ L) (Nat.succ z)}
(h: ¬z ≥ Nat.succ L)
(H: ¬(M.P w.1)) (a : Fin b)
: ¬ (M.P (Gap_cons a w h).1 ∧ M.Q (Gap_cons a w h).1) := by
  contrapose H; simp only [not_and, not_forall, not_not, exists_prop] at *
  exact still_holds _  _ H.1


-- should use List.sum_ofFn here?
/-- Writing `num_by_backtracking` as a sum of values of itself. -/
theorem branch_out'' (b:ℕ) {n L:ℕ} (M:MonoPred b)[DecidablePred M.P][DecidablePred M.Q]
(hnL: ¬ n ≥ L.succ) (w : Gap b L.succ n.succ) :
  num_by_backtracking M.P M.Q (w)
  = List.sum (List.ofFn (λ a ↦ num_by_backtracking M.P M.Q (Gap_cons a w hnL)))
  := by
  cases n -- Note: "induction n" not needed
  . -- zero
    unfold num_by_backtracking
    simp only [ge_iff_le, nonpos_iff_eq_zero, Nat.zero_eq, Nat.sub_zero, dite_false,
      ite_eq_left_iff]
    intro H

    symm
    have : List.ofFn (fun a => ite (M.P (Gap_cons a w (by linarith)).1 ∧ M.Q (Gap_cons a w (by linarith)).1) 1 0)
         = List.replicate b 0 := by
      apply List.eq_replicate.mpr
      constructor
      . simp only [Nat.zero_eq, Nat.sub_zero, List.length_ofFn]
      . intro i hi
        simp only [Nat.zero_eq, Nat.sub_zero] at hi
        rw [List.mem_iff_get] at hi
        obtain ⟨n,hn⟩ := hi
        simp only [Nat.zero_eq, Int.rawCast, Int.cast_id, Nat.rawCast, Nat.cast_id, Int.ofNat_one,
          Int.ofNat_eq_coe, Int.ofNat_zero, Int.Nat.cast_ofNat_Int, eq_mp_eq_cast, id_eq,
          Nat.sub_zero, List.get_ofFn] at hn
        rw [if_neg (still_does_not_hold'' _ H _)] at hn
        exact hn.symm
    rw [this]
    apply List.sum_const_nat b 0
  . -- succ
    unfold num_by_backtracking
    simp only [ge_iff_le, Nat.zero_eq, Nat.sub_zero]
    by_cases H : (M.P w.1)
    . -- pos
      rw [if_pos H,dif_neg hnL]
    . -- neg
      rw [if_neg H]
      symm
      let Recu := Nat.rec
              (motive := fun {k} => Gap b (Nat.succ L) k → ℕ)
              (fun w => ite (M.P w.1 ∧ M.Q w.1) 1 0) -- needs a Q
              (fun n n_ih w =>
                if M.P w.1 then -- doesn't need a Q
                  if h : Nat.succ L ≤ n then        n_ih (Gap_nil h)
                  else List.sum (List.ofFn fun a => n_ih (Gap_cons a w h))
                else 0)
      rename_i n_1
      have : (List.ofFn fun a => if M.P (Gap_cons a w hnL).1 then
            if h : Nat.succ L ≤ n_1 then
              Recu n_1 (Gap_nil h)
            else
              List.sum (List.ofFn fun a_1 => Recu n_1 (Gap_cons a_1 (Gap_cons a w hnL) h))
          else 0) = List.replicate b 0 := by {
        refine List.eq_replicate.mpr ?_
        constructor
        . -- left
          simp only [Nat.zero_eq, Nat.sub_zero, List.length_ofFn]
        . -- right
          intro i hi
          simp only [Nat.zero_eq, Nat.sub_zero] at hi
          rw [List.mem_iff_get] at hi
          obtain ⟨n,hn⟩ := hi
          simp only [Nat.zero_eq, Nat.sub_zero, List.get_ofFn] at hn
          rw [if_neg (still_does_not_hold _ _ H)] at hn
          exact hn.symm
      }
      rw [this]
      apply List.sum_const_nat b 0

theorem subtype_ext {α:Type} (P Q:α→ Prop) (h : ∀ x, P x ↔ Q x):
 {x : α // P x} =  {x : α // Q x} :=  congrArg Subtype (funext (fun x => propext (h x)))

theorem fincard_ext {α:Type} (P Q:α→ Prop) (h : ∀ x, P x ↔ Q x)
  [Fintype {x : α // P x}][Fintype {x : α // Q x}] :
  Fintype.card {x : α // P x} = Fintype.card {x : α // Q x} := by simp_rw [subtype_ext P Q h]

theorem Vector_eq_of_suffix_of_length_eq {L b:ℕ} {w : Vector (Fin b) L}
{v : Vector (Fin b) L} (hv : w.1 <:+ v.1) : w.1 = v.1
:= List.eq_of_suffix_of_length_eq hv (by {rw [v.2,w.2]})

/-- If `i≠j` then `i::w` and `j::w` can't be suffixes of the same vector `v`.-/
theorem disjoint_branch''  {L b: ℕ} {M:MonoPred b} --[DecidablePred M.P]
  {n:ℕ} (w: Vector (Fin b) (L.succ-n.succ)) (h : ¬ n ≥ L.succ) {i j : Fin b} (hp: i ≠ j)
  :
  Disjoint (λ v  : Vector (Fin b) L.succ ↦ (M.P v.1 ∧ M.Q v.1) ∧ (Gap_cons i w h).1 <:+ v.1 )
           (λ v  : Vector (Fin b) L.succ ↦ (M.P v.1 ∧ M.Q v.1) ∧ (Gap_cons j w h).1 <:+ v.1 ) := by {
  intro S h0S h1S v hSv
  obtain ⟨t₁,ht₁⟩ := (h0S v hSv).2
  obtain ⟨t₀,ht₀⟩ := (h1S v hSv).2

  have : t₁ ++ [i] ++ w.1 = t₀ ++ [j] ++ w.1 := calc
     _ = t₁ ++  i  :: w.1 := (List.append_cons t₁ i w.1).symm
     _ = v.1              := ht₁
     _ = t₀ ++ j :: w.1   := ht₀.symm
     _ = _                := (List.append_cons t₀ j w.1)

  have : (t₁ ++ [i]).getLast (by simp)
       = (t₀ ++ [j]).getLast (by simp) := List.getLast_congr _ _ ((List.append_left_inj w.1).mp this)
  simp only [List.getLast_append] at this
  exact hp this
}

lemma list_get_ne_nil {α: Type}
{x y t: List α}
(ht: t ++ x = y)
(hl: List.length x < List.length y)
: t ≠ []
:= by intro hc; subst hc; simp only [List.nil_append] at ht ; subst ht; linarith;

theorem Vector_append_succ_ne_nil {L n b: ℕ}
{w: Vector (Fin b) (Nat.succ L - Nat.succ n)}
{v: Vector (Fin b) (Nat.succ L)} {t: List (Fin b)} (ht: t ++ w.1 = v.1) :
t ≠ List.nil := by
  intro hc; subst hc;  simp only [List.nil_append] at ht ;
  apply congr_arg List.length at ht; simp only [Vector.length_val,
    Nat.succ_sub_succ_eq_sub] at ht
  have : L - n ≤ L := Nat.sub_le L n; rw [ht] at this; linarith;

theorem List_reverse_ne_nil {α : Type} {t : List α} (hlong : t ≠ []) : t.reverse ≠ []
  := by simp only [ne_eq, List.reverse_eq_nil_iff] at *;tauto

theorem List_reverse_cons {α : Type} {s t: List α} {a: α} (hs: t.reverse = a :: s)
: t = s.reverse ++ [a] := by
    apply congrArg List.reverse at hs; simp only [List.reverse_reverse,
      List.reverse_cons] at hs ;tauto

lemma prefix_of_same {L b: ℕ} (w: Vector (Fin b) L)
: ∀ x y : {v : Vector (Fin b) L // w.1 <:+ v.1}, x.1 = y.1 := by
    intro x y
    apply SetCoe.ext
    rw [← Vector_eq_of_suffix_of_length_eq x.2, ← Vector_eq_of_suffix_of_length_eq y.2]

lemma list_sum_ofFn_succ {n:ℕ} (f:Fin n.succ → ℕ):
List.sum (List.ofFn (λ i ↦ f i)) = List.sum (List.ofFn (λ i : Fin n ↦ f i)) + f n := by
  repeat (rw [List.sum_ofFn])
  simp only [Fin.coe_eq_castSucc, Fin.cast_nat_eq_last]; exact Fin.sum_univ_castSucc fun i => f i

lemma disjoint_from_last {α: Type} {n_1: ℕ} {p: Fin (Nat.succ n_1) → α → Prop}
(h: ∀ (i j : Fin (Nat.succ n_1)), i ≠ j → Disjoint (p i) (p j))
: Disjoint (λ x : α ↦ ∃ i, p (Fin.castSucc i) x) (λ x : α ↦ p (n_1) x) := by
    intro S hS₀ hS₁ x hSx
    obtain ⟨i,hi⟩ := hS₀ x hSx

    have hi: (λ y ↦ y=x) ≤ p (Fin.castSucc i) := by intro y hy; subst hy; tauto
    have hj: (λ y ↦ y=x) ≤ p n_1              := by intro y hy; subst hy; tauto

    have : (Fin.castSucc i).1 ≠ n_1 := by intro hc; simp only [Fin.coe_castSucc] at hc ; let G := i.2; linarith
    have : (Fin.castSucc i) ≠ n_1 := by
      contrapose this; simp only [ne_eq, Fin.cast_nat_eq_last, not_not,
        Fin.coe_castSucc] at *;exact Fin.mk_eq_mk.mp this
    exact h (Fin.castSucc i) n_1 this hi hj x rfl


def getFin {n_1 : ℕ} {i: Fin (Nat.succ n_1)} (hin: ¬i = n_1) : Fin n_1 := by
  have : i.1 < n_1 := by
    cases (Nat.lt_or_eq_of_le (Fin.is_le i));
    . rename_i h; exact h;
    . exfalso
      rename_i h;have : i = n_1 := by apply Fin.ext; rw [h]; simp only [Fin.cast_nat_eq_last,
        Fin.val_last]
      exact hin this
  exact ⟨i.1,this⟩

lemma distinguish_from_last {α: Type} {n_1: ℕ} {p: Fin (Nat.succ n_1) → α → Prop} (x : α)
: (∃ i, p (Fin.castSucc i) x) ∨ p (n_1) x ↔ ∃ i, p i x := by
  constructor;
  . -- mp
    intro ha; cases ha;
    . rename_i h;obtain ⟨i,hi⟩ := h;exists i;norm_cast
    . exists n_1;
  . -- mpr
    intro ha; obtain ⟨i,hi⟩ := ha; by_cases hin:(i=n_1)
    . right; rw [← hin]; exact hi;
    . left; exists getFin hin -- ⟨i.1,_⟩

def getFin_pred {n_1:ℕ} (i: Fin n_1.pred) : i < n_1 := calc
  i.1 < n_1.pred := i.2
  _   ≤ n_1      := Nat.pred_le n_1

lemma disjoint_cast {α: Type} {n_1: ℕ} {p: Fin (Nat.succ n_1) → α → Prop}
(h: ∀ (i j : Fin (Nat.succ n_1)), i ≠ j → Disjoint (p i) (p j))
 : (∀ (i j : Fin n_1),            i ≠ j → Disjoint (p (Fin.castSucc i)) (p (Fin.castSucc j)))
:= by
  intro i j hij
  have : Fin.castSucc i ≠ Fin.castSucc j := by
    contrapose hij; simp only [ne_eq, not_not] at *;exact Fin.castSucc_inj.mp hij
  exact h (Fin.castSucc i) (Fin.castSucc j) this



theorem Fintype_card_subtype_or_disjoint' {α:Type} [Fintype α]
{n:ℕ} (p : Fin n → α → Prop) -- January 30, 2024.
[Fintype {x:α // ∃ i, p i x}] [∀ i, Fintype {x:α // p i x}]
[DecidablePred fun x => ∃ i : Fin n.pred, p ⟨i,getFin_pred i⟩ x]
(h : ∀ i j, i ≠ j → Disjoint (p i) (p j))
:
List.sum (List.ofFn (λ i ↦ Fintype.card {x:α // p i x}))
                         = Fintype.card {x:α // ∃ i, p i x}
:= by {
  induction n; simp only [Nat.zero_eq, List.ofFn_zero, List.sum_nil,
    IsEmpty.exists_iff, Fintype.card_eq_zero]
  rename_i h₀ h₁ h₂
  -- Requires several decidability facts:
  obtain : DecidablePred fun x => ∃ i, p (Fin.castSucc i) x := h₂
  rename_i n_1 n_ih
  obtain : DecidablePred fun x : α => ∃ i : Fin n_1.pred, (fun i a => p (Fin.castSucc i) a) ⟨i.1, getFin_pred i⟩ x
    := Classical.decPred _
  obtain : Fintype { x : α // (∃ i, p (Fin.castSucc i) x) ∨ p (↑n_1) x } :=
    Fintype.ofFinite { x // (∃ i, p (Fin.castSucc i) x) ∨ p (↑n_1) x }

  rw [list_sum_ofFn_succ]
  norm_cast
  rw [
    n_ih (λ i a ↦ p (Fin.castSucc i) a) (disjoint_cast h),
    ← Fintype.card_subtype_or_disjoint _ _ (disjoint_from_last h)
  ]; apply fincard_ext; exact distinguish_from_last
}


lemma get_union {α :Type} {x y : List α} (h : x <:+ y) (hl : x.length < y.length) :
∃ a : α, a :: x <:+ y := by
  obtain ⟨t,ht⟩ := h
  obtain ⟨a,⟨s,hs⟩⟩ := (List.exists_cons_of_ne_nil (List_reverse_ne_nil (list_get_ne_nil ht hl)))
  exists a; exists s.reverse
  rw [List_reverse_cons hs] at ht; rw [← ht]; simp

theorem suffix_cons {b L n: ℕ} (w : Gap b (Nat.succ L) (Nat.succ n))
                               (v : Gap b (Nat.succ L) 0)
: w.1 <:+ v.1 ↔ ∃ a, a :: w.1 <:+ v.1
:= by
    constructor
    . -- mp
      intro h
      have : w.1.length < v.1.length := by
        rw [w.2,v.2]; simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
        calc _ ≤ L      := Nat.sub_le L n
             _ < L.succ := Nat.lt.base L
      exact get_union h this
    . -- mpr
      intro h
      obtain ⟨a,⟨t,ht⟩⟩ := h;exists t ++ [a]; rw [← ht];simp

/-- Verifies recursive backtracking for `b`-ary trees with monotone predicates `P`,
   with a non-monotone `Q` at the leaves. January 31, 2024.-/
theorem backtracking_verification {k b L:ℕ}
  (bound : k ≤ L.succ) (M:MonoPred b)
  [DecidablePred M.P] [DecidablePred M.Q]
  (w : Vector (Fin b) (L.succ-k)):
  Fintype.card {
    v : Vector (Fin b) L.succ // (M.P v.1 ∧ M.Q v.1) ∧ w.1 <:+ v.1
  }
  = num_by_backtracking M.P M.Q w
  := by
  induction k -- Since num_by_backtracking was defined by recursion, so is the proof.
  . -- zero
    unfold num_by_backtracking; simp only [Nat.zero_eq, Nat.sub_zero]
    by_cases hs : (M.P w.1 ∧ M.Q w.1)
    . -- pos
      rw [if_pos hs]
      have := subsingleton_iff.mpr (
        λ x y : {v : Vector (Fin b) L.succ // (M.P v.1 ∧ M.Q v.1) ∧ w.1 <:+ v.1}
        ↦ SetCoe.ext (prefix_of_same w ⟨x.1,x.2.2⟩ ⟨y.1,y.2.2⟩)
      )
      have := uniqueOfSubsingleton
        (⟨w,⟨hs, List.suffix_rfl⟩⟩ : {v : Vector (Fin b) L.succ // (M.P v.1 ∧ M.Q v.1) ∧ w.1 <:+ v.1})
      exact Fintype.card_unique
    . -- neg
      rw [if_neg hs]
      have : ∀ v: Vector (Fin b) L.succ ,¬ ((M.P v.1 ∧ M.Q v.1) ∧ w.1 <:+ v.1) := by {
        intro v hc
        have : w = v := SetCoe.ext (Vector_eq_of_suffix_of_length_eq hc.2)
        subst this; tauto
      }
      have := Subtype.isEmpty_of_false this
      exact Fintype.card_eq_zero
  . -- succ
    rename_i n n_ih
    by_cases case : (n ≥ L.succ)
    . -- pos
      exfalso
      have : n.succ ≤ n := calc
                  _ ≤ L.succ := bound
                  _ ≤ n      := case
      exact Nat.not_succ_le_self n this
    . -- neg
      have hcard : List.sum (List.ofFn (λ i ↦
           Fintype.card {v:Vector (Fin b) L.succ //      (M.P v.1 ∧ M.Q v.1) ∧ (Gap_cons i w case).1 <:+ v.1}
      )) = Fintype.card {v:Vector (Fin b) L.succ // ∃ i, (M.P v.1 ∧ M.Q v.1) ∧ (Gap_cons i w case).1 <:+ v.1} :=
           Fintype_card_subtype_or_disjoint' _ (λ _ _ hij ↦ disjoint_branch'' w case hij)
      simp only [exists_and_left] at hcard ;
      rw [
        branch_out'' _ _ case,
        ← funext (λ i : Fin b ↦ n_ih (Nat.le_of_lt bound) (Gap_cons i w case)),
        hcard
      ];
      apply fincard_ext; intro x;
      rw [and_assoc,suffix_cons w x]
      tauto

instance (k b L f:ℕ)
(bound : k ≤ L.succ) (M:MonoPred b) [DecidablePred M.P] [DecidablePred M.Q]
(w : Vector (Fin b) (L.succ-k)):
  Decidable (Fintype.card {v : Vector (Fin b) L.succ // (M.P v.1 ∧ M.Q v.1) ∧ w.1 <:+ v.1} =f)
:= decidable_of_iff (num_by_backtracking M.P M.Q w = f) (by rw [backtracking_verification bound _ _])

#eval Fintype.card {v : Vector (Fin 3) 3 // (squarefree v.1 ∧ True) ∧ [] <:+ v.1}
example :
Fintype.card {v : Vector (Fin 3) 3 // (squarefree v.1 ∧ True) ∧ [] <:+ v.1} = 12 := by decide

instance : DecidableEq (Gap b (Nat.succ L) 0)
:= by
  unfold Gap
  exact Vector.instDecidableEqVector

def those_with_suffix' {k b :ℕ} {L:ℕ} (P: List (Fin b) → Prop) [DecidablePred P]
  (Q: List (Fin b) → Prop) [DecidablePred Q] (w : Gap b L.succ k) : Finset (Gap b L.succ 0) :=
by {
  induction k
  . exact ((ite (P w.1 ∧ Q w.1) {w} ∅))
  . rename_i n n_ih
    exact
      (ite (P w.1))
      (
        dite (n ≥ L.succ)
        (λ h ↦ n_ih (Gap_nil h))
        (
          λ h ↦ Finset.biUnion (Finset.univ : Finset (Fin b)) (
            (λ a ↦ (n_ih (Gap_cons a w h)))
          )
        )
      )
      ∅
}

/-- `those_with_suffix` as a union of its own values.  -/
theorem branch_out_set (b:ℕ) {n L:ℕ}
{M: MonoPred b} [DecidablePred M.P]
[DecidablePred M.Q]
(hnL: ¬ n ≥ L.succ) (w : Gap b L.succ n.succ) :
  those_with_suffix' M.P M.Q (w)
  = Finset.biUnion (Finset.univ : Finset (Fin b)) (λ a ↦ those_with_suffix' M.P M.Q (Gap_cons a w hnL))
:= by
  cases n
  . -- zero
    unfold those_with_suffix'; simp only [ge_iff_le, nonpos_iff_eq_zero, Nat.zero_eq,
      Nat.sub_zero, dite_false, ite_eq_left_iff]; intro H; symm
    have : ∀ a, ite (M.P (Gap_cons a w hnL).1 ∧ M.Q (Gap_cons a w hnL).1)
        ({Gap_cons a w hnL} : Finset _) ∅ = ∅ := by
        intro a
        simp only [Nat.zero_eq, Nat.sub_zero, ite_eq_right_iff,
          Finset.singleton_ne_empty, and_imp, imp_false];contrapose;simp only [Nat.zero_eq, not_not];intro
        exact still_does_not_hold _ _ H
    rw [funext this]
    simp only [Nat.zero_eq]; apply Finset.ext; simp only [Finset.mem_biUnion,
      Finset.mem_univ, Finset.not_mem_empty, and_false, exists_false, implies_true]
  . -- succ
    unfold those_with_suffix'; simp only [ge_iff_le, Nat.zero_eq, Nat.sub_zero]
    by_cases H : (M.P w.1)
    . -- pos
      rw [if_pos H, dif_neg hnL]
    . -- neg
      rw [if_neg H]; symm
      apply Finset.ext; intro v; constructor;
      . -- mp
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
          Finset.not_mem_empty, forall_exists_index, imp_false]
        intro hv;
        rw [if_neg (still_does_not_hold _ _ H)]
        tauto
      . -- mpr
        simp

instance {b L:ℕ} : Fintype (Gap b (Nat.succ L) 0) := by
  unfold Gap
  exact Vector.fintype

theorem filter_suffix_empty
{b L: ℕ}
{P Q : List (Fin b) → Prop}
[DecidablePred P]
[DecidablePred Q]
{w: Gap b (Nat.succ L) 0}
(holds: ¬(P w.1 ∧ Q w.1))
: ∅ = Finset.filter (fun v : Gap b L.succ 0 => P v.1 ∧ Q v.1 ∧ w.1 <:+ v.1) Finset.univ
:= by
  apply Finset.ext
  intro a;
  constructor;
  . intro ha; simp only [Finset.not_mem_empty] at ha ;
  . intro ha; simp only [Nat.sub_zero, Finset.filter_congr_decidable,
    Finset.mem_filter, Finset.mem_univ, true_and] at ha ;
    have : w.1 = a.1 := List.eq_of_suffix_of_length_eq ha.2.2 (by rw [w.2,a.2])
    rw [this] at holds
    tauto

theorem filter_suffix_singleton
{b L: ℕ}
{P Q : List (Fin b) → Prop}
[DecidablePred P]
[DecidablePred Q]
{w: Gap b (Nat.succ L) 0}
(holds: (P w.1 ∧ Q w.1))
: {w} = Finset.filter (fun v : Gap b L.succ 0 => P v.1 ∧ Q v.1 ∧ w.1 <:+ v.1) Finset.univ
:= by
  apply Finset.ext
  intro a;
  constructor;
  . -- mp
    have h : a.1 <:+ a.1 := by exists []
    intro ha; simp only [Finset.mem_singleton] at ha ; subst ha; simp only [Nat.sub_zero,
      Finset.filter_congr_decidable, Finset.mem_filter, Finset.mem_univ, true_and];
    tauto
  . -- mpr
    simp only [Nat.sub_zero, Finset.filter_congr_decidable, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton, and_imp];intro;intro;intro hs;
    have : w.1 = a.1 := List.eq_of_suffix_of_length_eq hs (by rw [w.2,a.2])
    rw [Vector.eq w a this]

open Finset

theorem verify_those_with_suffix' {k b :ℕ} {L:ℕ} (bound : k ≤ L.succ)
{M:MonoPred b}
[DecidablePred M.P]
[DecidablePred M.Q] (w : Gap b L.succ k) :
  those_with_suffix' M.P M.Q w = filter (
    λ v : Gap b L.succ 0 ↦ M.P v.1 ∧ M.Q v.1 ∧ w.1 <:+ v.1
  ) univ := by
  induction k
  . -- zero
    unfold those_with_suffix'
    simp only [Nat.zero_eq, Nat.sub_zero, filter_congr_decidable]
    by_cases holds: (M.P w.1 ∧ M.Q w.1)
    . rw [if_pos holds]; exact filter_suffix_singleton holds
    . rw [if_neg holds]; exact filter_suffix_empty holds

  . -- succ
    rename_i n n_ih
    by_cases hLn: (L.succ ≤ n)
    . -- pos
      have : n.succ ≤ n := calc
                _ ≤ L.succ := bound
                _ ≤ n      := hLn
      exfalso; exact Nat.not_succ_le_self n this
    . -- neg
      let U := (univ : Finset (Gap b L.succ 0))

      have h₂ : filter (fun v => M.P v.1 ∧ M.Q v.1 ∧      w.1 <:+ v.1) U = Finset.biUnion univ
         (λ a ↦ filter (fun v => M.P v.1 ∧ M.Q v.1 ∧ a :: w.1 <:+ v.1) U) := by
        apply ext; simp only [Nat.sub_zero, filter_congr_decidable, mem_filter,
          mem_univ, true_and, mem_biUnion, exists_and_left, and_congr_right_iff];intro;rw [suffix_cons _ _];intros;tauto

      . rw [branch_out_set,h₂,funext (λ a ↦ n_ih (Nat.le_of_lt bound) (Gap_cons a w hLn))];rfl
