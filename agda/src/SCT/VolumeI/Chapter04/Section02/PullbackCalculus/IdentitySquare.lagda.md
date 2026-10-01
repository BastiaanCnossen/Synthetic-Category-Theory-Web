# The identity-arrow square of a left or right fibration

For `cor:Left_Fibrations_Are_Conservative`, paste the identity-arrow
square with the endpoint evaluation square. The outer square has
equivalent vertical arrows by the identity endpoint equations.
Pullback cancellation gives the assertion.

The proof works for either endpoint and keeps the constant-diagram
naturality comparison as the matching of the final square.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section02.PullbackCalculus.IdentitySquare
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section02.PullbackCalculus.PullbackCriterion 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter02.Section04.ConstantDiagrams.ConstantExponential 𝒯 M ℱ
  using (constant-natural)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
  using (IsPullback; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P
  using (degenerate-pullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap; coneSwap-swap)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)

module IdentitySquare {A B : CAT} (f : MAP A B) where
  square : Cone (funPost {C = [1]} f) (identityArrow {B}) A
  square = record
    { left = identityArrow ; right = f ; match = constant-natural [1] f }

  module At (v : Obj-abs [1]) where
    evaluation-square : Cone (evaluate {C = B} v) f (Ar A)
    evaluation-square = record { left = funPost f ; right = evaluate v ; match = evaluate-post v f }

    module FromPullback (e : IsPullback evaluation-square) where
      module Paste = Pasting identityArrow (evaluate v) f evaluation-square e
      outer = Paste.Paste.flatten (coneSwap square)

      source-identity-equivalence : IsEquiv (evaluate {C = A} v ∘ identityArrow)
      source-identity-equivalence = equiv-transport ((evaluate-constant v) ⁻¹) (id-isEquiv A)

      target-identity-equivalence : IsEquiv (evaluate {C = B} v ∘ identityArrow)
      target-identity-equivalence = equiv-transport ((evaluate-constant v) ⁻¹) (id-isEquiv B)

      outer-isPullback : IsPullback outer
      outer-isPullback = pullback-cone-invariant (coneSwap-swap outer)
        (pullback-swap (coneSwap outer)
          (degenerate-pullback target-identity-equivalence
            (coneSwap outer) source-identity-equivalence))

      square-isPullback : IsPullback square
      square-isPullback = pullback-cone-invariant (coneSwap-swap square)
        (pullback-swap (coneSwap square) (Paste.cancel-isPullback (coneSwap square) outer-isPullback))

  left-fibration-square : IsEquiv (Evaluation.directed-ev₀ f) → IsPullback square
  left-fibration-square e = At.FromPullback.square-isPullback zero (Criterion.left-to-pullback f e)

  right-fibration-square : IsEquiv (Evaluation.directed-ev₁ f) → IsPullback square
  right-fibration-square e = At.FromPullback.square-isPullback one (Criterion.right-to-pullback f e)
```

