# Pulling back a coproduct cover

If the copair of f and g is an equivalence, pulling them back along h gives
another coproduct cover. The result accepts two specified universal cones and
returns an equivalence for the copair of their actual right projections.

The canonical case follows directly from coproduct descent: its total category
projects equivalently to the base change along h. The two projection laws of
descent identify the resulting copair. Universal cone factorization then
transfers this to the given cones, without changing their matchings.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.CoproductCover where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_⊔_)
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (equiv-compose; equiv-transport)
open import SCT.VolumeI.Chapter01.Section05.Coproducts using (_⊔_; in₁; in₂)
open import SCT.VolumeI.Chapter01.Section05.Copairing
  using (copair; copair-cong; copair-post; copair-pre₁; copair-pre₂)
open import SCT.VolumeI.Chapter01.Section05.CoproductConstructions
  using (coproductMap; coproductMap-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.Cones using (Cone)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
  using (Pullback; pullback₂; pullback-factor; pullback-factor-β₂)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares using (IsPullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackConstructions using (pullback₂-isEquiv)
import SCT.VolumeI.Chapter01.Section06.CoproductDescent as Descent

module _ {Γ : Context} {C D E T : CAT Γ}
  (f : MAP C E) (g : MAP D E) (h : MAP T E) where

  private
    module Reassembly = Descent.Descent f g h

    canonical : MAP (Pullback f h ⊔ Pullback g h) T
    canonical = copair pullback₂ pullback₂

    projection-comparison : (pullback₂ ∘ Reassembly.descent) =₁ canonical
    projection-comparison = copair-cong Reassembly.include₁-β₂ Reassembly.include₂-β₂ ∙
      copair-post Reassembly.include₁ Reassembly.include₂ pullback₂

    canonical-isEquiv : IsEquiv (copair f g) → IsEquiv canonical
    canonical-isEquiv e = equiv-transport projection-comparison
      (equiv-compose Reassembly.descent pullback₂ Reassembly.descent-isEquiv
        (pullback₂-isEquiv (copair f g) h e))

  pullback-cover-isEquiv : {X Y : CAT Γ} (s : Cone f h X) (t : Cone g h Y)
    → IsPullback s → IsPullback t → IsEquiv (copair f g)
    → IsEquiv (copair (Cone.right s) (Cone.right t))
  pullback-cover-isEquiv s t es et e = equiv-transport comparison
    (equiv-compose (coproductMap (pullback-factor s) (pullback-factor t)) canonical
      (coproductMap-isEquiv (pullback-factor s) (pullback-factor t) es et)
      (canonical-isEquiv e))
    where
      comparison : (canonical ∘ coproductMap (pullback-factor s) (pullback-factor t))
        =₁ copair (Cone.right s) (Cone.right t)
      comparison = copair-cong
        (pullback-factor-β₂ s ∙ copair-pre₁ pullback₂ pullback₂ (pullback-factor s))
        (pullback-factor-β₂ t ∙ copair-pre₂ pullback₂ pullback₂ (pullback-factor t)) ∙
          copair-post (in₁ ∘ pullback-factor s) (in₂ ∘ pullback-factor t) canonical
```
