# The terminal category over a base

The identity category over the base is a terminal target for relative
functors. Native postcomposition by its identity map is identified with
the identity functor. The actual second projection of the chosen relative
functor-category pullback is consequently an equivalence to `One`.
No replacement of that chosen fiber or relative eta is needed.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section09.RelativeTerminal where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence using (module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (id-isEquiv; equiv-transport)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.PullbackConstructions using (pullback₂-isEquiv)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPost-id)
open import SCT.VolumeI.Chapter01.Section09.RelativeFunctorCategories

module RelativeTerminal {Γ : Context} {S : CAT Γ} (A : CategoryOverBase S) where
  private
    C : CAT Γ
    C = CategoryOverBase.category A

  terminal-base : CategoryOverBase S
  terminal-base = category-over S (id S)

  module Relative = RelativeFunctorCategory A terminal-base

  postcomposition-identity : Relative.postcomposition =₁ id (Fun C S)
  postcomposition-identity = funPost-id C S

  postcomposition-isEquiv : IsEquiv Relative.postcomposition
  postcomposition-isEquiv = equiv-transport (postcomposition-identity ⁻¹)
    (id-isEquiv (Fun C S))

  projection : MAP Relative.category One
  projection = Cone.right Relative.fiber

  projection-isEquiv : IsEquiv projection
  projection-isEquiv = pullback₂-isEquiv Relative.postcomposition Relative.point
    postcomposition-isEquiv

  equivalence : Equiv Relative.category One
  equivalence = record { functor = projection; isEquiv = projection-isEquiv }

  terminal-comparison : projection =₁ terminate Relative.category
  terminal-comparison = terminal-identification projection (terminate Relative.category)

  terminality : IsContractible Relative.category
  terminality = equiv-transport terminal-comparison projection-isEquiv
```
