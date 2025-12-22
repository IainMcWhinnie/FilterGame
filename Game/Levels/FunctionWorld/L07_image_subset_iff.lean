import Game.Levels.FunctionWorld.L06_image_comp

World "FunctionWorld"
Level 7

Title "Relation between image and preimage"

Introduction ""

namespace MyGame

variable {𝓧 𝓨 𝓩: Type}

TheoremTab "Function"

/--
## Summary

The `specialize` tactic is

### Example

-/
TacticDoc specialize
NewTactic specialize


/--
`image_subset_iff` is the proof that...
-/
TheoremDoc MyGame.image_subset_iff as "image_subset_iff" in "Function"

/-- -/
Statement image_subset_iff {S : Set 𝓧} {T : Set 𝓨} {φ : 𝓧 → 𝓨}  : φ '' S ⊆ T ↔ S ⊆ φ ⁻¹' T := by
  rw [subset_def, subset_def]
  constructor
  . intro h
    intro x hx
    rw [mem_preimage]
    apply h
    rw [mem_image]
    use x
  . intro h
    intro x hx
    rw [mem_image] at hx
    cases' hx with w hw
    cases' hw with hwl hwr
    specialize h w hwl
    rw [mem_preimage, hwr] at h
    exact h
