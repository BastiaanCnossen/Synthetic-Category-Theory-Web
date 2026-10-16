# The Segal axiom and families of completions

The Segal axiom states that the actual restriction to the two short edges,
including their chosen middle-vertex identification, is an equivalence.
This is the existing manuscript axiom `axiom:B_Segal_Axiom`.

For a family of composable pairs indexed by a category `P`, its category
of completions projects equivalently to `P`: this is base change of the
Segal equivalence. In particular, the category of completions of a single
composable pair is contractible. For general `P` we assert equivalence of
the projection, not contractibility of the total category.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.SegalAxiom where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open import SCT.VolumeI.Chapter01.Section01.Terminal
  using (terminate; module Constructions)
open Constructions using (IsContractible; terminal-identification)
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (equiv-transport)
open import SCT.VolumeI.Chapter01.Section06.PullbackConstructions
  using (pullback₂-isEquiv)
open import SCT.VolumeI.Chapter02.Section01.Triangles
  using (Composable; short-edges; Composites; module Completions)

module _ {Γ : Context} where
  postulate
    segal-isEquiv : (C : CAT Γ) → IsEquiv (short-edges C)

  completion-projection-isEquiv : {P C : CAT Γ} (p : MAP P (Composable C))
    → IsEquiv (Completions.base p)
  completion-projection-isEquiv {C = C} p =
    pullback₂-isEquiv (short-edges C) p (segal-isEquiv C)

  composites-contractible : {C : CAT Γ} (p : MAP One (Composable C))
    → IsContractible (Composites p)
  composites-contractible p = equiv-transport
    (terminal-identification (Completions.base p) (terminate (Composites p)))
    (completion-projection-isEquiv p)
```

The conditional construction in `SegalComposition` continues to take its
Segal equivalence as an explicit argument. This axiom supplies that input;
the conditional construction does not acquire a new primitive dependency.
