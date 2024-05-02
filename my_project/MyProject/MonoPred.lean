import Mathlib.Data.Nat.Basic

structure MonoPred (b:ℕ) where
  P : List (Fin b) → Prop
  preserved_under_suffixes (u v : List (Fin b)): u <:+ v → P v → P u
  Q (l: List (Fin b)) : Prop := True -- we can specify an extra condition that is not monotone

structure MonoPred_unverified (b:ℕ) where
  P : List (Fin b) → Prop
  Q : List (Fin b) → Prop := λ _ ↦ True -- we can specify an extra condition that is not monotone
