import Game.Levels.SetWorld.L07_inter_subset_left

World "SetWorld"

Level 8

Title "If `A ⊆ S` and `A ⊆ T` then `A ⊆ S ∩ T`."

Introduction "The final level in this tutorial is one we'll need later, so we'd
better prove it now. It's a simple criterion for proving `A ⊆ S ∩ T`, namely
checking that `A ⊆ S` and `A ⊆ T`."

#check Set.subset_inter
/--
## Summary

If the goal is a true statement in pure logic, like `P → (Q → P)` or `P ∧ Q → Q ∧ P`
(where `P` and `Q` can represent any mathematical true/false statements) then
the `tauto` tactic will solve it.
-/
TacticDoc tauto

NewTactic tauto

namespace MySet

variable (𝓧 : Type)

/-- If `A ⊆ S` and `A ⊆ T` then `A ⊆ S ∩ T`. -/
TheoremDoc MySet.subset_inter as "subset_inter" in "Set"

/-- `S ∩ T ⊆ S`. -/
Statement subset_inter {A S T : Set 𝓧} (hAS : A ⊆ S) (hAT : A ⊆ T) :
  A ⊆ S ∩ T := by
  Hint "I would start with `rw [subset_def] at *`. If you find yourself
  later on with the goal `x ∈ S ∧ x ∈ T`, then
  use the `constructor` tactic to break into two goals `x ∈ S` and `x ∈ T`."
  rw [subset_def] at *
  intro x hx
  rw [MySet.mem_inter_iff]
  constructor
  · apply hAS
    exact hx
  · exact hAT _ hx

Conclusion "That's enough practice with sets. In Did you solve `a ∈ T → a ∈ S` with one tactic `apply hTS`? The reason this works
is that `T ⊆ S` is equal to `∀ x, x ∈ T → x ∈ S` *by definition*, so it is a theorem which
applies for all `x`, and in particular it applies for `x = a`, which is the goal."
