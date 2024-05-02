import Mathlib.Computability.NFA
import Mathlib.Data.Nat.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Std.Data.Nat.Lemmas
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Digits
import MyProject.exercise_2_2
set_option tactic.hygienic false
set_option maxHeartbeats 3000000

def isbin (w : List (Fin 3)) := ∀ i, w.get i = 0 ∨ w.get i = 1

instance (w : List (Fin 3)) : Decidable (isbin w) := by {
  unfold isbin
  exact Nat.decidableForallFin fun i => List.get w i = 0 ∨ List.get w i = 1
}

def binexthelp {n:ℕ} {P:Prop}(h:¬ (n ≥5 ∨ P )) : (5-n.succ).succ = 5-n
:= by {
  have : n < 5 := by {
    contrapose h
    simp
    left
    exact Nat.not_lt.mp h
  }
  have h₄: n ≤ 4 := by exact Nat.lt_succ.mp this
  have : 5-n.succ = 4-n := by exact Nat.succ_sub_succ 4 n
  have : (5-n.succ).succ = 5-n := by {
    rw [this]
    exact (Nat.succ_sub h₄).symm
  }
  exact this
}

def binexthelp' {n:ℕ} (h:¬ (n ≥5 )) : (5-n.succ).succ = 5-n
:= by {
  have : n < 5 := by {
    contrapose h
    simp
    exact Nat.not_lt.mp h
  }
  have h₄: n ≤ 4 := by exact Nat.lt_succ.mp this
  have : 5-n.succ = 4-n := by exact Nat.succ_sub_succ 4 n
  have : (5-n.succ).succ = 5-n := by {
    rw [this]
    exact (Nat.succ_sub h₄).symm
  }
  exact this
}

def binextending (k:ℕ) (w : Vector (Fin 3) (5-k)) : Vector (Fin 3) 5 → Prop :=
by {
  induction k
  exact (λ f ↦ (f = w ∧ isbin w.1))
  exact dite (n ≥ 5 ∨ ¬ isbin w.1) (λ _ _ ↦ False) (
    by {
      intro h; let H := binexthelp h
      let G₀ := (0::ᵥ w); rw [H] at G₀
      let G₁ := (1::ᵥ w); rw [H] at G₁
      let G₂ := (2::ᵥ w); rw [H] at G₂
      intro w
      exact n_ih G₀ w  ∨  n_ih G₁ w  ∨  n_ih G₂ w
    }
  )
}

def num_binextending (k:ℕ) (w : Vector (Fin 3) (5-k)) : ℕ :=
by {
  induction k
  exact ((ite (isbin w.1) 1 0))
  exact dite (n ≥ 5 ∨ ¬ isbin w.1) (λ _ ↦ 0) (
    by {
      intro h; let H := binexthelp h
      let G₀ := (0::ᵥ w); rw [H] at G₀
      let G₁ := (1::ᵥ w); rw [H] at G₁
      let G₂ := (2::ᵥ w); rw [H] at G₂
      exact (n_ih G₀)  +  (n_ih G₁)  +  (n_ih G₂)
    }
  )
}

-- controlled_append:
def capp {n:ℕ} (a:Fin 3) (w : Vector (Fin 3) (5-n.succ)) (h: ¬ n ≥ 5)
                            : Vector (Fin 3) (5-n)
:= ⟨ a :: w.1, by {
  rw [List.length_cons]
  simp
  have : n < 5 := by exact Nat.not_le.mp h
  have : n ≤ 4 := by exact Nat.not_lt.mp h
  exact (Nat.succ_sub this).symm
}⟩

-- rep_suf = number of not squarefree words having w as suffix
def rep_suf {k:ℕ} (w : Vector (Fin 3) (5-k)) : ℕ :=
by {
  induction k
  -- Base case:
  exact ((ite (squarefree w) 1 0))
  -- Inductive case:
  exact
    (ite (squarefree w))
    (
      dite (n ≥ 5)
      (λ _ ↦ 0)
      (λ h ↦ (n_ih (capp 0 w h))
          +  (n_ih (capp 1 w h))
          +  (n_ih (capp 2 w h)))
    )
    0
}

def rep_suf' (l : List (Fin 3)) : ℕ :=
dite (l.length > 5)
(λ _ ↦ 0)
(by {
  intro h
  have : l.length = 5 - (5 - l.length) := sorry
  exact rep_suf ⟨l,this⟩
})

theorem reprep {k:ℕ} (w : Vector (Fin 3) (5-k)) :
rep_suf w = rep_suf' w.1 := by {
  unfold rep_suf'
  by_cases h:(w.1.length > 5)
  simp
  rw [if_neg _]


  sorry
}

-- theorem sdfgsdfg  (a :ℕ)
--   (w₁ : Vector (Fin 3) (5-a))
--   (w₂ : Vector (Fin 3) (5-a.succ)) (he: w₁.1=w₂.1 ) :

-- rep_suf w₁ =
-- rep_suf w₂
-- := by {
--   induction a
--   unfold rep_suf
--   simp
--   -- have : 5-a=5-a.succ := sorry
--   sorry
-- }

theorem extsf {lu lv : ℕ} (u : Vector (Fin 3) lu) (v : Vector (Fin 3) lv)
(h: u.1 <:+ v.1) (hu : squarefree v) : squarefree u := by {
  unfold squarefree
  unfold squarefree at hu
  intro lx
  intro
  intro x hx
  rcases h with ⟨t,ht⟩
  intro hc
  have hgood: (x.1 ++ x.1).length ≤ u.1.length := by {
    exact List.IsInfix.length_le hc
  }
  rcases hc with ⟨s₀,hs₀⟩
  rcases hs₀ with ⟨s₁,hs₁⟩
  have : t.length + u.1.length = (t ++ u.1).length :=
    by exact (List.length_append t u.1).symm
  have h₀: t.length + u.1.length = v.1.length := by {
    rw [this]
    rw [ht]
  }
  have: 0 < x.1.length := by exact List.length_pos.mpr hx
  have : lx < v.length :=
    calc
    lx = x.1.length := x.2.symm
    _ < x.1.length + x.1.length := by exact Nat.lt_add_of_pos_left this
    _ = (x.1 ++ x.1).length := by exact (List.length_append x.1 x.1).symm
    _ ≤ u.1.length := hgood
    _ ≤ t.length + u.1.length := by linarith
    _ = v.1.length := by exact h₀
    _ = v.length := by exact Vector.length_val v
  let G := hu lx this x hx
  unfold List.IsInfix at G
  have : ∃ s t, s ++ (x.1 ++ x.1) ++ t = v.1 := by {
    exists t ++ s₀
    exists s₁
    rw [← ht]
    rw [← hs₁]
    simp
  }
  exact G this
}

theorem numhelp (n:ℕ) (h: ¬ n ≥ 5) (w : Vector (Fin 3) (5-n.succ)) :
rep_suf  (w)
  = rep_suf  (capp 0 w h)
  + rep_suf  (capp 1 w h)
  + rep_suf  (capp 2 w h) := by {

  induction n
  -- Base step:
  unfold rep_suf
  simp
  intro H
  -- BLOCK
  have : w.1 <:+ (capp 0 w h).1 := by {exists [0];}
  have : ¬ squarefree (capp 0 w h) := by {
    intro hc
    exact H (extsf w (capp 0 w h) this hc) -- since it extends w
  }
  rw [if_neg this]
  have : w.1 <:+ (capp 1 w h).1 := by {exists [1];}
  have : ¬ squarefree (capp 1 w h) := by {
    intro hc
    exact H (extsf w (capp 1 w h) this hc) -- since it extends w
  }
  rw [if_neg this]

  have : w.1 <:+ (capp 2 w h).1 := by {exists [2];}
  have : ¬ squarefree (capp 2 w h) := by {
    intro hc
    exact H (extsf w (capp 2 w h) this hc) -- since it extends w
  }
  rw [if_neg this]
  -- END OF BLOCK

  -- Inductive step:
  unfold rep_suf
  simp
  by_cases H : (squarefree w)
  rw [if_pos H]
  rw [dif_neg h]

  rw [if_neg H]
  -- BLOCK
  have : w.1 <:+ (capp 0 w h).1 := by {
    exists [0];
  }
  have : ¬ squarefree (capp 0 w h) := by {
    intro hc
    exact H (extsf w (capp 0 w h) this hc) -- since it extends w
  }
  rw [if_neg this]
  have : w.1 <:+ (capp 1 w h).1 := by {exists [1];}
  have : ¬ squarefree (capp 1 w h) := by {
    intro hc
    exact H (extsf w (capp 1 w h) this hc) -- since it extends w
  }
  rw [if_neg this]

  have : w.1 <:+ (capp 2 w h).1 := by {exists [2];}
  have : ¬ squarefree (capp 2 w h) := by {
    intro hc
    exact H (extsf w (capp 2 w h) this hc) -- since it extends w
  }
  rw [if_neg this]
  -- END OF BLOCK
  }

-- #eval rep_suf 1 ⟨[0,1,0,2],rfl⟩ -- {20102}, not {01020,01021}


-- An unexpected bonus of this is that we don't have to deal with cardinality and finset.

instance (α:Type) (P:α → Prop) (h : ∀ x y : {v // P v}, x = y):
Subsingleton {v :α // P v} :=
by {
  exact subsingleton_iff.mpr h
}

theorem Fintype_card_union_add_card_inter {α:Type} (P Q:α→ Prop)
[Fintype α]
[DecidablePred fun a => P a ∨ Q a]
[DecidablePred P]
[Fintype {x : α // P x}][Fintype {x : α // Q x}]
[Fintype {x : α // P x ∧ Q x}][Fintype {x : α // P x ∨ Q x}]
:
 Fintype.card {x : α // P x ∨ Q x} + Fintype.card {x : α // P x ∧ Q x} =
 Fintype.card {x : α // Q x} +  Fintype.card {x : α // Q x} := by {
-- let s : Finset α := Finset.univ
let s := Finset.subtype P Finset.univ
let s := Finset.subtype (λ a ↦ P a ∨ Q a) Finset.univ
/-
can prove using:
theorem Fintype.subtype_card{α : Type u_1} {p : α → Prop}
(s : Finset α) (H : ∀ (x : α), x ∈ s ↔ p x) :
Fintype.card { x : α // p x } = s.card

def Finset.subtype{α : Type u_4} (p : α → Prop) [DecidablePred p] (s : Finset α) :
Finset (Subtype p)
-/
sorry
}


theorem subtype_ext {α:Type} (P Q:α→ Prop) (h : ∀ x, P x ↔ Q x):
 {x : α // P x} =  {x : α // Q x} := by {
  have : ∀ x, P x = Q x := by exact fun x => propext (h x)
  have : P = Q := funext this
  exact congrArg Subtype this
}

theorem fincard_ext {α:Type} (P Q:α→ Prop) (h : ∀ x, P x ↔ Q x) [Fintype {x : α // P x}][Fintype {x : α // Q x}] :
  Fintype.card {x : α // P x} = Fintype.card {x : α // Q x} := by {
  have H: {x // P x} = {x // Q x} := subtype_ext P Q h
  simp_rw [H]
}

example {α:Type} (P Q:α→ Prop) (u v : {x : α // P x}) (h : u.1=v.1) :
Q u → Q v := by exact (iff_of_eq (congrArg Q h)).mp

instance (α:Type) (P:α → Prop)
(h : ∀ x y : {v // P v}, x = y)
(v : {v // P v})
:
Unique {v :α // P v} :=
by {
  let G := subsingleton_iff.mpr h
  exact uniqueOfSubsingleton v
}

theorem verify (k:ℕ)  (w : Vector (Fin 3) (5-k)):
  Fintype.card {v : Vector (Fin 3) 5 // squarefree v ∧ w.1 <:+ v.1}
  = rep_suf  w
:= by {
  induction k
  unfold rep_suf
  simp
  have h₁: ∀ v : Vector (Fin 3) 5, w.1 <:+ v.1 → w.1 = v.1 := by {
    intro v hv
    exact List.eq_of_suffix_of_length_eq hv (by {rw [v.2,w.2]})
  }
  have : ∀ x y : {v : Vector (Fin 3) 5 // squarefree v ∧ w.1 <:+ v.1}, x.1.1 = y.1.1 := by {
    intro x y
    let Gx := h₁ x x.2.2
    let Gy := h₁ y y.2.2
    exact Eq.trans Gx.symm Gy
  }
  have h₃: ∀ x y : {v : Vector (Fin 3) 5 // squarefree v ∧ w.1 <:+ v.1}, x.1 = y.1 := by {
    intro x y
    exact SetCoe.ext (this x y)
  }
  have h₂: ∀ x y : {v : Vector (Fin 3) 5 // squarefree v ∧ w.1 <:+ v.1}, x = y := by {
    intro x y
    have h₀: x.1 = y.1 := h₃ x y
    exact SetCoe.ext h₀
  }
  by_cases h : (squarefree w)
  rw [if_pos h]
  let G := subsingleton_iff.mpr (h₂)
  let u : {v : Vector (Fin 3) 5 // squarefree v ∧ w.1 <:+ v.1} :=
  ⟨w,by {
    constructor
    exact h
    exact List.suffix_rfl
  }⟩
  let H := uniqueOfSubsingleton u
  refine Fintype.card_unique
  rw [if_neg h]
  have : ∀ v: Vector (Fin 3) 5 ,¬ (squarefree v ∧ w.1 <:+ v.1) := by {
    intro v hc
    have : v = w := by {
      exact (SetCoe.ext (h₁ v hc.2)).symm
    }
    subst this
    exact h hc.1
  }
  let K := Subtype.isEmpty_of_false this
  exact Fintype.card_eq_zero
  -- Induction step:
  have h₃: ∀ v : Vector (Fin 3) 5,
    w.1 <:+ v.1 ↔ ∃ a : Fin 3, a :: w.1 <:+ v.1 := by {
      intro v
      unfold List.IsSuffix
      constructor
      intro h
      rcases h with ⟨s,hs⟩
      rw [← hs]
      have hsn: s ≠ List.nil := by {
        intro hc
        rw [hc] at hs
        simp at hs
        have : w.1.length = v.1.length := congr_arg _ hs
        rw [w.2,v.2] at this
        contrapose this
        simp
        have : 4 - n < 5 := calc
          _ ≤ 4 := by exact Nat.sub_le 4 n
          _ < 5 := by exact Nat.lt.base 4
        exact Nat.ne_of_lt this
      }
      have : ([] : List (Fin 3)).reverse = [] := by exact List.reverse_nil
      have : List.reverse s ≠ [] := by {
        intro hc
        rw [← this] at hc
        have : s = [] := by exact List.reverse_eq_nil_iff.mp hc
        exact hsn this
      }
      have : ∃ a t, List.reverse s = a :: t := by exact List.exists_cons_of_ne_nil this
      rcases this with ⟨b,hb⟩
      rcases hb with ⟨u,hu⟩
      exists b
      exists u.reverse
      have : (b :: u).reverse = u.reverse ++ [b] := by exact List.reverse_cons b u
      have : s = u.reverse ++ [b] := by {
        rw [← this]
        exact List.reverse_eq_iff.mp hu
      }
      rw [this]
      simp


      intro h
      rcases h with ⟨a,ha⟩
      rcases ha with ⟨t,ht⟩
      exists t ++ [a]
      rw [← ht]
      simp
    }
  have : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
  have hca: ∀ v : Vector (Fin 3) 5,
    w.1 <:+ v.1 ↔ 0 :: w.1 <:+ v.1
                ∨ 1 :: w.1 <:+ v.1
                ∨ 2 :: w.1 <:+ v.1 := by {
                  intro v;constructor;intro h
                  let G := (h₃ v).mp h;rcases G with ⟨a,ha⟩
                  have : a = 0 ∨ a = 1 ∨ a = 2 := this a
                  cases this; subst h_1
                  left; exact ha;cases h_1
                  subst h_2;right;left;exact ha;subst h_2;right;right
                  exact ha;intro h;cases h
                  unfold List.IsSuffix at h_1; unfold List.IsSuffix
                  rcases h_1 with ⟨t,ht⟩; exists t ++ [0]
                  rw [← ht]; simp
                  cases h_1

                  unfold List.IsSuffix at h; unfold List.IsSuffix
                  rcases h with ⟨t,ht⟩; exists t ++ [1]
                  rw [← ht]; simp

                  unfold List.IsSuffix at h; unfold List.IsSuffix
                  rcases h with ⟨t,ht⟩; exists t ++ [2]; rw [← ht]; simp
                  }
  by_cases h : (¬ n ≥ 5)
  let g₀ := capp 0 w h --(0 ::ᵥ w)
  let g₁ := capp 1 w h
  let g₂ := capp 2 w h

  have : ∀ v : Vector (Fin 3) 5, squarefree v ∧ w.1 <:+ v.1 ↔
  ( squarefree v ∧ g₀.1 <:+ v.1) ∨ (squarefree v ∧ g₁.1 <:+ v.1) ∨
  ( squarefree v ∧ g₂.1 <:+ v.1)  := by {
  sorry
}
  have : Fintype.card { v : Vector (Fin 3) 5 // squarefree v ∧ w.1 <:+ v.1 } =
         Fintype.card { v : Vector (Fin 3) 5 //  squarefree v ∧ g₀.1 <:+ v.1 ∨ (squarefree v ∧ g₁.1 <:+ v.1) ∨
( squarefree v ∧ g₂.1 <:+ v.1) } := fincard_ext _ _ this
  have : Fintype.card { v : Vector (Fin 3) 5 // squarefree v ∧ w.1 <:+ v.1 }
   = Fintype.card { v : Vector (Fin 3) 5 // squarefree v ∧ g₀.1 <:+ v.1 }
   + Fintype.card { v : Vector (Fin 3) 5 // squarefree v ∧ g₁.1 <:+ v.1 }
   + Fintype.card { v : Vector (Fin 3) 5 // squarefree v ∧ g₂.1 <:+ v.1 } := sorry
  -- use disjointness and hca. basically easy

  rw [this]
  have : rep_suf  (w)
  = rep_suf  g₀
  + rep_suf  g₁
  + rep_suf  g₂ := numhelp n _ _
  rw [this]
  let Q₀ := n_ih g₀
  rw [Q₀]
  let Q₁ := n_ih g₁
  rw [Q₁]
  let Q₂ := n_ih g₂
  rw [Q₂]

  -- when ≥ 5:

  simp at h
  -- use n_ih after rewriting the type
  have : 5 ≤ n.succ := by exact Nat.le_step h
  have h₅: 5-n.succ = 0 := Nat.sub_eq_zero_of_le this
  have : w.1.length = 5-n := calc
    _ = 5-n.succ := w.2
    _ = 0 := h₅
    _ = 5-n := (Nat.sub_eq_zero_of_le h).symm
  let w' := (⟨w.1,this⟩ : Vector (Fin 3) (5-n))
  let H := n_ih w'
  -- have : w.1 = w'.1 := rfl
  rw [H]
  simp at H

  -- exact iff_of_eq (congrArg _ this).mp H
  -- rw [h₅] at w

  -- have : w.length = 0 := by {
  --   let G := w.2
  --   simp_rw [this] at G;
  --   exact this
  -- }
  -- have : w = Vector.nil := sorry

  sorry
}


-- #eval num_binextending 2 ⟨[0,0,0],rfl⟩

theorem hgs: binextending 0 ⟨[0,0,0,0,0],rfl⟩ ⟨[0,0,0,0,0],rfl⟩
:= by {
  unfold binextending
  simp
  decide
}

theorem hgs''': binextending 1 ⟨[0,0,0,0],rfl⟩ ⟨[0,0,0,0,0],rfl⟩
:= by {
  unfold binextending
  simp
  rw [if_pos (by decide)]
  decide
}

theorem hgs'''': ¬ binextending 1 ⟨[0,0,0,0],rfl⟩ ⟨[0,0,0,0,2],rfl⟩
:= by {
  unfold binextending
  simp
  rw [if_pos (by decide)]
  decide
}

theorem hgs''''': ¬ binextending 1 ⟨[0,0,0,0],rfl⟩ ⟨[2,0,0,0,0],rfl⟩
:= by {
  unfold binextending
  simp
  rw [if_pos (by decide)]
  decide
}

theorem hgs'': ¬ binextending 0 ⟨[0,0,0,2,0],rfl⟩ ⟨[0,0,2,0,0],rfl⟩
:= by {
  unfold binextending
  simp
  decide
}
theorem hgs': ¬ binextending 0 ⟨[0,0,0,0,0],rfl⟩ ⟨[0,0,1,0,0],rfl⟩
:= by {
  unfold binextending
  simp
  decide
}
