# Cores preserve coproducts

The actual copair of the maps on cores induced by the two inclusions is an
equivalence. Apply `Map One` to the two coproduct universality squares and
use coproduct descent. The base case is the two-point coproduct: its core
inclusion is an equivalence by the interval-core axiom and the preceding
`CoreInclusions` argument. No primitive anima witness for the two-point
category, or closure of that predicate under equivalence, is needed.

This follows the finite proof in the original Section01.CoreCoproducts.
The private descent adapter below accepts two complete universal cones,
so the proof uses the actual mapped matchings rather than only their legs.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.CoreCoproducts where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_⊔_)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate)
open import SCT.VolumeI.Chapter01.Section02.Coherence using (module Composition)
open Composition using (_∙_; _⁻¹)
open import SCT.VolumeI.Chapter01.Section03.Equivalences
  using (equiv-transport; equiv-compose; equiv-cancel-left)
open import SCT.VolumeI.Chapter01.Section04.Functoriality using (mapPost)
open import SCT.VolumeI.Chapter01.Section04.Core
  using (Core; coreInclusion; core-of-anima)
open import SCT.VolumeI.Chapter01.Section05.Coproducts using (_⊔_; in₁; in₂)
open import SCT.VolumeI.Chapter01.Section05.Copairing
  using (copair; copair-β₁; copair-β₂; copair-cong; copair-post; copair-pre₁; copair-pre₂)
open import SCT.VolumeI.Chapter01.Section05.CoproductConstructions
  using (coproductMap; coproductMap-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.Cones using (Cone)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
  using (Pullback; pullback₂; pullback-factor; pullback-factor-β₂)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares using (IsPullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackConstructions using (pullback₂-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts
  using (coproductSquare₁; coproductSquare₂; inclusion₁-isPullback; inclusion₂-isPullback)
open import SCT.VolumeI.Chapter01.Section06.CoproductDescent
  using (module Descent)
open import SCT.VolumeI.Chapter01.Section06.MappingPullbacks
  using (mapped-cone; map-preserves-pullback)
open import SCT.VolumeI.Chapter02.Section01.CoreInclusions
  using (core-inclusion-natural; two-point-core-isEquiv)

private
  module CoproductCover {Γ : Context} {C D E T X Y : CAT Γ}
    (f : MAP C E) (g : MAP D E) (h : MAP T E)
    (s : Cone f h X) (t : Cone g h Y)
    (es : IsPullback s) (et : IsPullback t) (e : IsEquiv (copair f g)) where

    module Reassembly = Descent {C = C} {D = D} {P = E} {Q = T} f g h
      using (include₁; include₂; include₁-β₂; include₂-β₂; descent; descent-isEquiv)

    left-projection : MAP (Pullback f h) T
    left-projection = pullback₂ {f = f} {g = h}
    right-projection : MAP (Pullback g h) T
    right-projection = pullback₂ {f = g} {g = h}
    total-projection : MAP (Pullback (copair f g) h) T
    total-projection = pullback₂ {f = copair f g} {g = h}

    canonical : MAP (Pullback f h ⊔ Pullback g h) T
    canonical = copair left-projection right-projection

    left-image : (total-projection ∘ Reassembly.include₁) =₁ left-projection
    left-image = Reassembly.include₁-β₂
    right-image : (total-projection ∘ Reassembly.include₂) =₁ right-projection
    right-image = Reassembly.include₂-β₂

    reassembly-image : (total-projection ∘ Reassembly.descent) =₁ canonical
    reassembly-image = copair-cong {A = One}
      {f = total-projection ∘ Reassembly.include₁} {f′ = left-projection}
      {g = total-projection ∘ Reassembly.include₂} {g′ = right-projection}
      left-image right-image ∙
        copair-post Reassembly.include₁ Reassembly.include₂ total-projection

    canonical-isEquiv : IsEquiv canonical
    canonical-isEquiv = equiv-transport reassembly-image
      (equiv-compose Reassembly.descent pullback₂ Reassembly.descent-isEquiv
        (pullback₂-isEquiv (copair f g) h e))

    inclusion-image :
      (canonical ∘ coproductMap (pullback-factor s) (pullback-factor t)) =₁
        copair (Cone.right s) (Cone.right t)
    inclusion-image = copair-cong
      (pullback-factor-β₂ s ∙ copair-pre₁ pullback₂ pullback₂ (pullback-factor s))
      (pullback-factor-β₂ t ∙ copair-pre₂ pullback₂ pullback₂ (pullback-factor t)) ∙
        copair-post (in₁ ∘ pullback-factor s) (in₂ ∘ pullback-factor t) canonical

    copair-isEquiv : IsEquiv (copair (Cone.right s) (Cone.right t))
    copair-isEquiv = equiv-transport inclusion-image
      (equiv-compose (coproductMap (pullback-factor s) (pullback-factor t)) canonical
        (coproductMap-isEquiv (pullback-factor s) (pullback-factor t) es et)
        canonical-isEquiv)

module _ {Γ : Context} where
  coreCopair : (C D : CAT Γ) → MAP (Core C ⊔ Core D) (Core (C ⊔ D))
  coreCopair C D = copair (mapPost {C = One} in₁) (mapPost {C = One} in₂)

  inclusion-copair : (C D : CAT Γ)
    → (coreInclusion (C ⊔ D) ∘ coreCopair C D) =₁
        coproductMap (coreInclusion C) (coreInclusion D)
  inclusion-copair C D =
    copair-cong (core-inclusion-natural in₁) (core-inclusion-natural in₂) ∙
      copair-post (mapPost in₁) (mapPost in₂) (coreInclusion (C ⊔ D))

  private
    two-point-copair-isEquiv : IsEquiv (coreCopair One One)
    two-point-copair-isEquiv = equiv-cancel-left
      (coreCopair One One) (coreInclusion (One ⊔ One)) two-point-core-isEquiv
      (equiv-transport ((inclusion-copair One One) ⁻¹)
        (coproductMap-isEquiv (coreInclusion One) (coreInclusion One)
          (core-of-anima One one-isAn) (core-of-anima One one-isAn)))

  coreCopair-isEquiv : (C D : CAT Γ) → IsEquiv (coreCopair C D)
  coreCopair-isEquiv C D = CoproductCover.copair-isEquiv
    (mapPost {C = One} in₁) (mapPost {C = One} in₂)
    (mapPost {C = One} (coproductMap (terminate C) (terminate D)))
    (mapped-cone One (coproductSquare₁ (terminate C) (terminate D)))
    (mapped-cone One (coproductSquare₂ (terminate C) (terminate D)))
    (map-preserves-pullback One _ (inclusion₁-isPullback (terminate C) (terminate D)))
    (map-preserves-pullback One _ (inclusion₂-isPullback (terminate C) (terminate D)))
    two-point-copair-isEquiv
```
