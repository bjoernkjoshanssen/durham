import MyProject.HydrophobicPolarModel


section Some_unnecessary_group_computations

example : go_X ∘ go_W = id := by
  apply funext; intro x; unfold go_X go_W mm sp pp sm; simp only [Function.comp_apply, id_eq]; have h₁: x.2 - 1 = x.2 + -1 := rfl
  by_cases h : (Even x.2); rw [if_pos h]
  simp only [Prod.snd_add]; simp_rw [← h₁];
  rw [if_neg (Int.odd_iff_not_even.mp (Even.sub_odd h (Int.odd_iff.mpr (by exact rfl))))]
  . exact add_eq_of_eq_sub rfl
  rw [if_neg h]
  simp only [Prod.snd_add]; simp_rw [← h₁];
  rw [if_pos (Odd.sub_odd (Int.odd_iff_not_even.mpr h) (Int.odd_iff.mpr (by exact rfl)))]
  . exact add_eq_of_eq_sub rfl

example : go_Z ∘ go_E = id := by
  apply funext; intro x; unfold go_E go_Z sp sm pm; simp only [Function.comp_apply, id_eq]; have h₁: x.2 - 1 = x.2 + -1 := rfl
  by_cases h : (Even x.2); rw [if_pos h]
  simp only [Prod.snd_add]; simp_rw [← h₁];
  rw [if_neg (Int.odd_iff_not_even.mp (Even.sub_odd h (Int.odd_iff.mpr (by exact rfl))))]
  . exact add_eq_of_eq_sub rfl
  rw [if_neg h]
  simp only [Prod.snd_add];simp_rw [← h₁];
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

  cases x;
  rename_i fst snd
  simp; simp at h; have : Odd (snd + 1) := Even.add_one h
  . exact Int.odd_iff_not_even.mp this
  rw [if_neg h]; simp;

  cases x;
  rename_i fst snd
  simp; simp at h; have : Odd snd := Int.odd_iff_not_even.mpr h
  . exact Int.even_add_one.mpr h

example : go_W ∘ go_X = id := by
  apply funext; intro x; unfold go_W go_X sm mm sp pp; simp;
  by_cases h : (Even x.2); rw [if_pos h]; simp;

  cases x;
  rename_i fst snd
  simp; simp at h; have : Odd (snd + 1) := Even.add_one h
  . exact Int.odd_iff_not_even.mp this
  rw [if_neg h];

  cases x;
  rename_i fst snd
  simp at h; have : Odd snd := Int.odd_iff_not_even.mpr h
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
