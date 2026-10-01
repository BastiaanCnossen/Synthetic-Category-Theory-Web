# Cancellation in normalized witness chains

A common cancellation argument compares pasted normalization chains. Its functors can themselves be points of identification animae, so the same calculation applies to higher witnesses.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
import SCT.VolumeI.Chapter05.Section01.Expressions.TermCalculus as Calculus
import SCT.VolumeI.Chapter05.Section01.Expressions.EndpointTransport as Transport

module SCT.VolumeI.Chapter05.Section01.Expressions.NormalizationPasting {l : Level} (T : Theory l l l) where
open View T
open Calculus.Local T
open Transport T using (changeEndpoints; changeEndpoints-to-square; square-to-changeEndpoints)

-- A dimension-independent cancellation lemma. The maps below may themselves
-- be points of an identification anima, so this also compares pentagonators.
opaque
  compare : {C D : CAT} {x₀ x₁ x₂ y₀ y₁ y₂ : MAP C D}
    (a : x₀ =₁ y₀) (b : x₁ =₁ y₁)
    (u : x₀ =₁ x₁) (v : y₀ =₁ y₁)
    (left : x₀ =₁ x₂) (right : y₀ =₁ y₂)
    (left' : x₁ =₁ x₂) (right' : y₁ =₁ y₂)
    → (v ∙ a) =₂ (b ∙ u)
    → left =₂ (left' ∙ u) → right =₂ (right' ∙ v)
    → (changeEndpoints left right a) =₂ (changeEndpoints left' right' b)
  compare a b u v left right left' right' middle first second =
    square-to-changeEndpoints left right a (changeEndpoints left' right' b)
      (isoComp-cong second (idIso _) then
        paste u left' v right' a b (changeEndpoints left' right' b) middle
          (changeEndpoints-to-square left' right' b (changeEndpoints left' right' b) (idIso _)) then
        isoComp-cong (idIso _) (first ⁻¹))
```
