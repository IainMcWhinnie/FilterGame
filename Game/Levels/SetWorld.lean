import Game.Levels.SetWorld.L01_subset_refl

World "SetWorld"
Title "Set World"

Introduction "
In this tutorial level we'll learn about sets, subsets, and the intersection of two sets.

Our sets will all be subsets of a fixed \"base set\" `𝒳`.
In particular, whenever we say \"let `S` be a set\" in this level, we mean \"let `S` be a set
of elements of `𝒮`\", and we write `S : Set 𝒳`.

In Lean the base set `𝒮` is called a *type*. If you're used to also thinking of `𝒳` as a set,
this shouldn't cause any problems, but there is one notational difference. Lean uses the notation
`x : 𝒳` to mean that `x` is an element of the base type `𝒳`, but for `S` a set, Lean uses
the notation `x ∈ S` to mean that `x` is an element `S`.

Press **TODO** to continue."
