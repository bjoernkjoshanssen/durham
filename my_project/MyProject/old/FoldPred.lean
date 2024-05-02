import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector.Basic
import MyProject.MonoPred
set_option tactic.hygienic false
set_option maxHeartbeats 3000000

/- This proof illustrate the value
of a folding that can be extended infinitely, to avoid typecasting
issues. This is a surprising angle on the KKNS paper.
It also has pleasing uses of "decide".
-/

def left  (p: ℤ × ℤ) : ℤ × ℤ := (p.1-1,p.2) -- A
def right (p: ℤ × ℤ) : ℤ × ℤ := (p.1+1,p.2) -- D
def up    (p: ℤ × ℤ) : ℤ × ℤ := (p.1  ,p.2+1) -- W
def down  (p: ℤ × ℤ) : ℤ × ℤ := (p.1  ,p.2-1) -- S




-- Instead of Fin n perhaps we should have a graph structure on Fin n
def FinGraph {n:ℕ} : SimpleGraph (Fin n) := {
  Adj := λ k l ↦ l.1 = k.1 + 1 ∨ k.1 = l.1 + 1
  symm := λ k l h ↦ by {
    cases h;
    right; assumption
    left;  assumption
  }
  loopless := by {intro k; simp}
}

def folding {α β:Type} {A:SimpleGraph α}{B:SimpleGraph β} (f : β → α)
  := Function.Injective f ∧ ∀ k l, B.Adj k l → A.Adj (f k) (f l)
-- For a graph obtained by symmetrizing a digraph, this can be stated
-- more simply, though.

-- this is basically an injective weak homomorphism and we have a set
-- on which we want many ctrexamples to strong homomorphism.

-- def folding (f : ℕ → (ℤ × ℤ)) := ∀ k, Z2.Adj (f k) (f k.succ)

theorem case3' {k n:ℕ} (h: k < n.succ)
(h₄: ¬Nat.succ k < n.succ) : k = n := by {
  have : k < n ∨ k = n := Nat.lt_or_eq_of_le (Nat.lt_succ.mp h)
  cases this; exfalso; contrapose h₄; simp; exact Nat.lt_succ.mpr h_1
  exact h_1
}

def myfold : List (ℤ×ℤ) := [(0,0),(1,0),(1,1),(0,1)]

def f₁ (n:ℕ):  ℤ×ℤ  := dite (n<4)
  (λ h ↦ myfold.get ⟨n,h⟩)
  (λ _ ↦ (0,n-2))

def nearby' (p q : ℤ × ℤ) : Prop :=
  q ∈ [down p, up p, left p, right p]


-- Graph theoretic approach:
def nearby (p q : ℤ × ℤ) : Prop :=
  (p.1-q.1)^2 + (p.2-q.2)^2 = 1
def Z2 : SimpleGraph (ℤ×ℤ) := {
  Adj := λ p q ↦ nearby p q
  symm := by {intros _ _ h; unfold nearby at h; unfold nearby; rw [← h]; ring}
  loopless := by {intro p; unfold nearby; simp}
}

instance (p q : ℤ × ℤ) : Decidable (nearby' p q) := by {
  unfold nearby'
  exact List.instDecidableMemListInstMembershipList q [down p, up p, left p, right p]
}

def folding' (f : ℕ → (ℤ × ℤ)) := ∀ k, nearby' (f k) (f k.succ)

def point_achieved'
  (l : ℕ → (ℤ×ℤ)) (a b : ℕ) (phobic : ℕ → Bool) : Prop
:= by {
  exact phobic a ∧ phobic b ∧ a.succ < b ∧ nearby' (l a) (l b)
}

def point_achieved''
  (l : ℕ → (ℤ×ℤ)) (a b : ℕ) (phobic : ℕ → Bool) : Bool
:= by {
  exact phobic a && phobic b && a.succ < b && nearby' (l a) (l b)
}


-- to use point_achieved' need to make an infinite version of [true,b₀,b₁,true]:
def phobe (n:ℕ): Bool   := dite (n<4)
  (λ h ↦ [true,false,false,true].get ⟨n,h⟩)
  (λ _ ↦ false)

instance (a b : ℕ) (ph : ℕ → Bool)
  (f : ℕ → (ℤ×ℤ))
  : Decidable (point_achieved' f a b ph) := by {
  unfold point_achieved'
  exact And.decidable
}
instance (a b : ℕ) (ph : ℕ → Bool)
  (f : ℕ → (ℤ×ℤ))
  : Decidable (point_achieved'' f a b ph) := by {
  unfold point_achieved''
  exact Bool.decEq (ph a && ph b && decide (Nat.succ a < b) && decide (nearby' (f a) (f b))) true
}

-- theorem first_point'' : point_achieved'' f₁ 0 3 phobe
-- := by decide
def F : Bool → ℕ := λ b ↦ ite (b=true) 1 0

def FF (b : Prop) [Decidable b] : ℕ := ite (b) 1 0

-- theorem fp : List.sum (List.map F [
--   point_achieved'' f₁ 0 3 phobe,
--   point_achieved'' f₁ 1 3 phobe
-- ]) = 1 :=
-- by {
--   decide
-- }

def pts_at (k : ℕ) (ph : ℕ → Bool)
  (f : ℕ → (ℤ×ℤ)) :=
  List.sum (List.map F (List.ofFn (λ i : Fin k ↦   point_achieved'' f i k ph)))




-- #eval fold_of_moves₃ some_moves
def rect_fold : List (ℤ×ℤ) :=
  [(0, -1), (-1, -1), (-1, -2), (0, -2), (1, -2), (1, -1), (1, 0), (0, 0)]




-- #eval Function.Injective (λ i ↦ (fold_of_moves₃ some_moves).1.get i)

-- #eval Function.Injective (λ i ↦ (fold_of_moves₃ (moves_of_digits₃ [0,1,2,3])).1.get i)
-- Will be faster if avoid the char's
def move_fin : Fin 4 → ((ℤ×ℤ) → (ℤ×ℤ))
| 0 => λ x ↦ (x.1 + 1,x.2    )
| 1 => λ x ↦ (x.1 - 1,x.2    )
| 2 => λ x ↦ (x.1    ,x.2 + 1)
| 3 => λ x ↦ (x.1    ,x.2 - 1)


def move_fin₃ : Fin 6 → ((ℤ×ℤ×ℤ) → (ℤ×ℤ×ℤ))
| 0 => λ x ↦ (x.1 + 1,x.2    )
| 1 => λ x ↦ (x.1 - 1,x.2    )
| 2 => λ x ↦ (x.1    ,x.2.1 + 1,x.2.2)
| 3 => λ x ↦ (x.1    ,x.2.1 - 1,x.2.2)
| 4 => λ x ↦ (x.1    ,x.2.1, x.2.2 + 1)
| 5 => λ x ↦ (x.1    ,x.2.1, x.2.2 - 1)

def pp :  ((ℤ×ℤ) → (ℤ×ℤ)) := λ x ↦ (x.1+1,x.2+1) -- 1
def ps :  ((ℤ×ℤ) → (ℤ×ℤ)) := λ x ↦ (x.1+1,x.2) -- 1
def sp :  ((ℤ×ℤ) → (ℤ×ℤ)) := λ x ↦ (x.1,x.2+1) -- 2

def mm :  ((ℤ×ℤ) → (ℤ×ℤ)) := λ x ↦ (x.1-1,x.2-1) -- 1
def ms :  ((ℤ×ℤ) → (ℤ×ℤ)) := λ x ↦ (x.1-1,x.2) -- 1
def sm :  ((ℤ×ℤ) → (ℤ×ℤ)) := λ x ↦ (x.1,x.2-1) -- 2

def pm :  ((ℤ×ℤ) → (ℤ×ℤ)) := λ x ↦ (x.1+1,x.2-1) -- 1
def mp :  ((ℤ×ℤ) → (ℤ×ℤ)) := λ x ↦ (x.1-1,x.2+1) -- 1


def move_hex : Fin 6 → ((ℤ×ℤ) → (ℤ×ℤ))
| 0 => ps
| 1 => ms
| 2 => λ x ↦ ite (Even x.2) (sp x) (pp x)
| 3 => λ x ↦ ite (Even x.2) (mm x) (sm x)
| 4 => λ x ↦ ite (Even x.2) (mp x) (sp x)
| 5 => λ x ↦ ite (Even x.2) (sm x) (pm x)
#eval move_hex 0 (0,0)
#eval move_hex 5 (1,0)

def move_tri : Fin 3 → ((ℤ×ℤ) → (ℤ×ℤ))
| 0 => ps
| 1 => λ x ↦ ite (Even (x.1+x.2)) (sp x) (sm x)
| 2 => ms

-- #eval move_fin₃ 0 (0,0,0)
-- #eval move_fin₃ 1 (0,0,0)
-- #eval move_fin₃ 2 (0,0,0)
-- #eval move_fin₃ 3 (0,0,0)
-- #eval move_fin₃ 4 (0,0,0)
-- #eval move_fin₃ 5 (0,0,0)

def walk' {α:Type} [OfNat α 0]  {b : ℕ} (go : Fin b → α → α)
  (l : List (Fin b)) :  {l : List α // l ≠ List.nil} := by {
  induction l
  exact ⟨[0], List.cons_ne_nil _ _⟩
  exact ⟨(go head (List.head tail_ih.1 tail_ih.2)) :: tail_ih.1, List.cons_ne_nil _ _⟩
}

-- def SpaceType : Type 1 := { α : Type // α = (ℤ×ℤ) ∨ α = (ℤ×ℤ×ℤ)}


-- def nearby_with  {α:Type} [OfNat α 0] {b : ℕ} (go : Fin b → α → α)
-- [DecidableEq α]
-- [DecidablePred (λ (i,v,w) ↦ go i v = w)]
-- [∀ i v w, Decidable (go i v = w)]
-- (p q : α) : Prop :=
-- ∃ a : Fin b, q = go a p -- get decidability issues when trying to use this
-- -- Doesn't work above



def nearby_with₀  {b : ℕ} (go : Fin b → ℤ×ℤ → ℤ×ℤ)
-- this is good enough to cover three of our HP models
-- in fact all our models could live in Z^3
-- [DecidablePred (λ (i,v,w) ↦ go i v = w)]
-- [∀ i v w, Decidable (go i v = w)]
(p q : ℤ×ℤ) : Bool :=
∃ a : Fin b, q = go a p

def nearby_with₀₀  {b : ℕ} (go : Fin b → ℤ×ℤ×ℤ → ℤ×ℤ×ℤ)
[DecidablePred (λ (i,v,w) ↦ go i v = w)]
[∀ i v w, Decidable (go i v = w)]
(p q : ℤ×ℤ×ℤ) : Bool :=
∃ a : Fin b, q = go a p

def nearby_with₁  (go : Fin 4 → ℤ×ℤ → ℤ×ℤ)
[DecidablePred (λ (i,v,w) ↦ go i v = w)]
[∀ i v w, Decidable (go i v = w)]
(p q : ℤ×ℤ) : Bool :=
∃ a : Fin 4, q = go a p

def nearby_with₂ (p q : ℤ×ℤ) : Bool :=
  ∃ a : Fin 4, q = move_fin a p

def point_achieved_with
  (l : ℕ → (ℤ×ℤ)) (a b : ℕ) (phobic : ℕ → Bool) : Bool
:= by {
  exact phobic a && phobic b && a.succ < b && nearby_with₂ (l a) (l b)
}

def point_achieved_with₁ (go : Fin 4 → ℤ×ℤ → ℤ×ℤ)
  (l : ℕ → (ℤ×ℤ)) (a b : ℕ) (phobic : ℕ → Bool) : Bool
:= by {
  exact phobic a && phobic b && a.succ < b && nearby_with₀ go (l a) (l b)
}


def pts_at_with (go : Fin 4 → ℤ×ℤ → ℤ×ℤ)
(k : ℕ) (ph : ℕ → Bool)
  (f : ℕ → ℤ×ℤ) :=
  List.sum (List.map F (List.ofFn (λ i : Fin k ↦   point_achieved_with₁ (go : Fin 4 → ℤ×ℤ → ℤ×ℤ) f i k ph)))

-- def trunkwalk' {α:Type} [OfNat α 0]  {b : ℕ} (go : Fin b → α → α)
--   (l : List (Fin b)) :  List α := List.dropLast (walk' go l).1


-- def walk'' {α:Type}  {b : ℕ} (go : Fin b → α → α)
--   (l : List (Fin b)) :  {l : List α // l ≠ List.nil} := by {
--     let G := List.foldr go init l
--     sorry
--   }

def walk {α:Type} [OfNat α 0] {b : ℕ} (go : Fin b → α → α)
(l : List (Fin b)) : List α :=
  (walk' go l.reverse).1

def moves_fin' (l : List (Fin 4)) :  {l : List (ℤ×ℤ) // l ≠ List.nil} :=
  walk' move_fin l
def moves_fin (l : List (Fin 4)) : List (ℤ×ℤ) :=
  walk move_fin l

def moves_hex' (l : List (Fin 6)) :  {l : List (ℤ×ℤ) // l ≠ List.nil} :=
  walk' move_hex l
def moves_hex (l : List (Fin 6)) : List (ℤ×ℤ) := (moves_hex' l.reverse).1

def moves_tri' (l : List (Fin 3)) :  {l : List (ℤ×ℤ) // l ≠ List.nil} :=
  walk' move_tri l
def moves_tri (l : List (Fin 3)) : List (ℤ×ℤ) := (moves_tri' l.reverse).1

def moves_fin'₃ (l : List (Fin 6)) :  {l : List (ℤ×ℤ×ℤ) // l ≠ List.nil} :=
  walk' move_fin₃ l
def moves_fin₃ (l : List (Fin 6)) : List (ℤ×ℤ×ℤ) := (moves_fin'₃ l.reverse).1


theorem moves_len'
  {α:Type} [OfNat α 0] {b : ℕ} (go : Fin b → α → α)
  (l : List (Fin b)) :

  (walk' go l).1.length = l.length.succ := by {
  induction l

  unfold walk';
  rw [List.length_cons]
  rfl
  unfold walk'
  simp
  rw [← Nat.succ_eq_add_one,← tail_ih]
  unfold walk'
  simp
}

theorem moves_len
  {α:Type} [OfNat α 0] {b : ℕ} (go : Fin b → α → α)
  (l : List (Fin b)) :

  (walk go l).length = l.length.succ := by {
    unfold walk; rw [moves_len']; simp
}

theorem moves_fin'_len (l : List (Fin 4)) : (moves_fin' l).1.length = l.length.succ :=
  moves_len' _ _

theorem moves_fin_len (l : List (Fin 4)) : (moves_fin l).length = l.length.succ :=
  moves_len _ _


-- #eval moves_fin' [0,1,1]
-- #eval moves_fin' [2,2,0,1,1]

#eval walk' move_hex [0,1,1]
#eval walk' move_hex ([2,2] ++ [0,1,1])

#eval [move_hex 0 (move_hex 1 (move_hex 1 (0, 0))), move_hex 1 (move_hex 1 (0, 0)), move_hex 1 (0, 0), (0, 0)]


#eval List.head (walk' move_hex [0,1,1]).1 (by {unfold walk';simp})
-- #eval List.dropLast (walk' (List.head (walk' move_hex [0,1,1]).1 (by {unfold walk';simp})) move_hex [2,2]).1



theorem moves_extend_sample:
  (walk' move_hex [0,1,1]).1 <:+ (walk' move_hex [2,2,0,1,1]).1 := by {
    unfold walk'
    simp
    exists [(0, 2), (-1, 1)]
}


theorem get_monotone {α β : Type} (f : List α → {l: List β // l ≠ []})
  (h: ∀ x a, ∃ b, f (a :: x) = b :: (f x).1) ( x y : List α) :
  (f x).1 <:+ (f (y ++ x)).1 := by {
    induction y
    simp
    exists []
    simp

    let G := h (tail ++ x) head
    rcases G with ⟨b,hb⟩
    rw [hb]
    rcases tail_ih with ⟨t,ht⟩
    rw [← ht]
    exists b :: t
  }

theorem list_get_append_right  {α:Type} (u v : List α) (m: Fin (List.length v)):
(u ++ v).get ⟨u.length + m,by {rw [List.length_append];simp}⟩
     = v.get m := by {
  have h : ¬(m + u.length) < u.length := λ hc ↦ Nat.not_succ_le_zero m.1 (Nat.add_lt_add_iff_right.mp (Nat.lt_add_left 0 hc))
  have h' : (m + u.length) < (u ++ v).length := by {
    rw [List.length_append,add_comm u.length v.length]
    exact (add_lt_add_iff_right u.length).mpr m.2
  }
  have h'' : (m + u.length) - u.length < v.length := by simp
  have G : (u ++ v).get ⟨m + u.length,h'⟩
                = v.get ⟨m + u.length - u.length, h''⟩ :=
              List.get_append_right u v h
  simp_rw [add_comm]
  simp at G; exact G
}
theorem injective_suffix {α:Type} (u v : List α)
(h : Function.Injective (λ i ↦ (u ++ v).get i)) :
     Function.Injective (λ i ↦ (     v).get i) := by {
    intro m n hmn

    have : (u++v).get ⟨u.length + m,by rw [List.length_append];simp⟩
         = (u++v).get ⟨u.length + n,by rw [List.length_append];simp⟩ := by
      rw [list_get_append_right,list_get_append_right]
      exact hmn

    have : u.length + m = u.length + n :=congr_arg (λ x ↦ x.1)  (h this)
    simp at this
    exact Fin.ext this
}

theorem injective_prefix {α:Type} (u v : List α)
  (h : Function.Injective (λ i ↦ (u ++ v).get i)) : Function.Injective (λ i ↦ u.get i) := by {
  intro m n hmn
  have hm: u.get m = (u++v).get ⟨m.1,by rw [List.length_append];exact Nat.lt_add_right v.length m.2⟩
    := (List.get_append_left _ _ _).symm

  have hn: u.get n = (u++v).get ⟨n.1,by rw [List.length_append];exact Nat.lt_add_right v.length n.2⟩
    := (List.get_append_left _ _ _).symm

  simp at hmn
  rw [hm,hn] at hmn
  exact Fin.ext (Fin.mk_eq_mk.mp (h hmn))
}

theorem moves_extend' -- moves_fin_extend'
-- January 27, 5:30pm
  {α:Type} [OfNat α 0] {b : ℕ} (go : Fin b → α → α)
  {z x : List (Fin b)} (h: x <:+ z):
         (walk' go x).1 <:+ (walk' go z).1 :=
  by {
    rcases h with ⟨y,hy⟩
    rw [← hy]

    apply get_monotone

    intro x a
    have : (walk' go x).1 ≠ List.nil := by {
      intro hc
      let G := congr_arg List.length hc
      rw [moves_len' go x] at G
      contrapose G
      simp
    }
    exists go a ((walk' go x).1.head this)
  }

theorem moves_extend
-- January 28
  {α:Type} [OfNat α 0] {b : ℕ} (go : Fin b → α → α)
  {z x : List (Fin b)} (h: x <+: z):
            (walk go x) <:+ (walk go z) := moves_extend' go (List.reverse_suffix.mpr h)



theorem moves_extend_
-- January 28
  {α:Type} [OfNat α 0] {b : ℕ} (go : Fin b → α → α)
  {z x : List (Fin b)} (h: x <:+ z):
            (walk go x.reverse) <:+ (walk go z.reverse) :=

moves_extend go (List.reverse_prefix.mpr h)



def FoldScore' : MonoPred 4 := {
  P := λ w ↦ Function.Injective (λ i ↦ (walk' move_fin w).1.get i)
  Q := λ _ ↦ True
  preserved_under_suffixes := by {
    intro u v huv hiv
    have : (walk' move_fin u).1 <:+ (walk' move_fin v).1 := moves_extend' _ huv
    rcases this with ⟨t,ht⟩
    rw [← ht] at hiv
    exact injective_suffix t _ hiv
  }
}


def FoldScore {α:Type} [OfNat α 0] {b : ℕ} (go : Fin b → α → α) : MonoPred b := {
  P := λ w ↦ Function.Injective (λ i ↦ (walk' go w).1.get i)
  Q := λ _ ↦ True -- should involve score
  preserved_under_suffixes := by {
    intro u v huv hiv
    have : (walk' go u).1 <:+ (walk' go v).1 := moves_extend' _ huv
    rcases this with ⟨t,ht⟩
    rw [← ht] at hiv
    exact injective_suffix t _ hiv
  }
}
-- Can we make a "walk" rather than walk' version?
-- def FoldScore'' {α:Type} [OfNat α 0] {b : ℕ} (go : Fin b → α → α) : MonoPred b := {
--   P := λ w ↦ Function.Injective (λ i ↦ (walk go w).get i)
--   Q := λ _ ↦ True -- should involve score
--   preserved_under_suffixes := by {
--     intro u v huv hiv
--     have huvr: u.reverse.reverse <:+ v.reverse.reverse := by {
--       simp
--       exact huv
--     }
--     have : (walk go u.reverse) <:+ (walk go v.reverse) := moves_extend' _ huvr
--     rcases this with ⟨t,ht⟩
--     -- rw [← ht] at hiv
--     exact injective_prefix _ _ _
--   }
-- }





theorem fp'' : pts_at 3 phobe f₁ = 1 := by decide
-- theorem fp''' : pts_below 4 phobe f₁ = 1 := by decide
theorem first_point' : point_achieved' f₁ 0 3 phobe := by decide

instance : OfNat (Fin (List.length myfold)) 0 := ⟨0,by {unfold myfold;simp}⟩
instance : OfNat (Fin (List.length myfold)) 3 := ⟨3,by {unfold myfold;simp}⟩
theorem fpl {b₀ b₁ : Bool} :  List.length [true, b₀, b₁, true] = List.length myfold
:= by {simp;rfl}



theorem case'' {k l:ℕ}
(h₄: ¬ k < l) :
¬ k.succ < l := by {by_contra; contrapose h₄; simp; exact Nat.lt_of_succ_lt a}

-- For the optimization problem we want max over all choices of "rect_fold" here
-- howeve
def rfi : ℕ → (ℤ×ℤ) := λ n ↦ dite (n < rect_fold.length)
  (λ h ↦ rect_fold.get ⟨n,h⟩)
  (λ _ ↦ (-(n-7),0))



-- WITHOUT EXTEND_FOLD:
-- ~ ~ ~
def foldingVec {l:ℕ} (rf : Vector (ℤ×ℤ) l)
:= ∀ k : Fin l.pred, nearby'
  (rf.get ⟨k,     Nat.lt_of_lt_pred  k.2⟩)
  (rf.get ⟨k.succ,Nat.lt_pred_iff.mp k.2⟩)
def rect_foldVec : Vector (ℤ×ℤ) 8 :=
  ⟨[(0, -1), (-1, -1), (-1, -2), (0, -2), (1, -2), (1, -1), (1, 0), (0, 0)],rfl⟩
example : foldingVec rect_foldVec := by {unfold foldingVec;decide}
def rfpiVec (b:Bool) : Vector Bool 8 :=
  ⟨[true,false,true,false,true,false,b,true].reverse, rfl⟩
-- ~ ~ ~

-- WITH EXTEND_FOLD
-- / / /
-- Here we have an automated checking whether a finite sequence is a fold:
def extend_fold (rf : List (ℤ×ℤ)): ℕ → (ℤ×ℤ) := λ n ↦ dite (n < rf.length)
  (λ h ↦ rf.get ⟨n,h⟩)
  (λ _ ↦ (0,0))
def folding'' (rf : List (ℤ×ℤ))
:= ∀ k, k < rf.length.pred → nearby' (extend_fold rf k) (extend_fold rf k.succ)
theorem fr_ext : folding'' rect_fold := by {unfold folding'';decide}
def rfpi (b:Bool) : ℕ → Bool := λ n ↦ dite (n < 8)
  (λ h ↦ [true,false,true,false,true,false,b,true].reverse.get ⟨n,h⟩)
  (λ _ ↦ false)
def extendBool (p : List Bool) : ℕ → Bool := λ n ↦ dite (n < p.length)
  (λ h ↦ p.get ⟨n,h⟩) (λ _ ↦ false)
-- / / /



theorem fr_duh : folding' rfi := by {
  unfold rfi
  have hl: ∀ n, n < rect_fold.length → nearby' (rfi n) (rfi n.succ) := by decide
  have hnl: ∀ n, ¬ n < rect_fold.length → nearby' (rfi n) (rfi n.succ) := by {
    intro n hn; unfold rfi; rw [dif_neg hn]; simp
    have : ¬ n.succ < rect_fold.length := case'' hn
    rw [dif_neg this]; unfold nearby'; right; right; unfold left
    ring_nf; left
  }
  intro n; by_cases h : n < 8; exact hl _ h; exact hnl _ h
}
-- pts_below is the protein folding scoring function
def pts_below (k : ℕ) (phobic : ℕ → Bool) (fold : ℕ → (ℤ×ℤ))
:= List.sum (List.ofFn (λ i : Fin k ↦ pts_at i phobic fold))

def pts_below' (k : ℕ) (phobic : ℕ → Bool) (fold : List (ℤ×ℤ))
:= List.sum (List.ofFn (λ i : Fin k ↦ pts_at i phobic (extend_fold fold)))

def pts_below'' (k : ℕ) (phobic : List Bool) (fold : List (ℤ×ℤ))
:= List.sum (List.ofFn (λ i : Fin k             ↦ pts_at i (extendBool phobic.reverse) (extend_fold fold)))

def pts (phobic : List Bool) (fold : List (ℤ×ℤ))
:= List.sum (List.ofFn (λ i : Fin (fold.length) ↦ pts_at i (extendBool phobic.reverse) (extend_fold fold)))



theorem pts_duh' : pts_below' 8 (rfpi true) (rect_fold) = 3
:= by decide

-- #eval     pts_below' 8 (extendBool [true,false,true,false,true,false,true,true].reverse) (rect_fold)
example : pts_below' 8 (extendBool [true,false,true,false,true,false,true,true].reverse) (rect_fold) = 3 := by decide

example : pts_below'' 8 ([true,false,true,false,true,false,true,true]) (rect_fold) = 3 := by decide

def add0 : List ℕ → List ℕ := λ v ↦ 0 :: v


def extend (k:ℕ) (l: List ℕ) : List ℕ :=
ite (l.length < k)
(l ++ List.replicate (k-l.length) 0)
l



-- This shows P(010101b0) ≥ 3 in the paper page 2:
-- #eval pts_below 8 (rfpi true) rfi
theorem paper_page_2 (b:Bool) : pts_below 8 (rfpi b) rfi = 3 := by {
  have : b = true ∨ b = false := Bool.eq_false_or_eq_true b
  cases this
  rw [h]; decide
  rw [h]; decide
}
