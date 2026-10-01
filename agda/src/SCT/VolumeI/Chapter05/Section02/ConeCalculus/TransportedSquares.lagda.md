# Reflecting a transported comparison square

Several cone constructions transport each matching along comparisons of
its two endpoints. A comparison of the transported cones then gives a
square between transported matchings. When the leg comparisons are
themselves transported along naturality squares, cancelling the common
endpoint comparisons recovers the square between the original matchings.

The calculation is vertical and takes place in one theory. It uses only
the composition, cancellation and reflection laws for changing endpoints.
The proof remains transparent so that clients retain the chosen witness.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport as Endpoint

module SCT.VolumeI.Chapter05.Section02.ConeCalculus.TransportedSquares
  {c m a : Level} (𝒯 : Theory c m a) where

open Setup 𝒯
open Endpoint 𝒯 using (changeEndpoints; changeEndpoints-reflect; changeEndpoints-comp; square-to-changeEndpoints)
```

The source matching `τs` and target matching `τt` have their endpoints
changed by `fs`, `gs` and `ft`, `gt`. The raw leg comparisons `α` and
`β` correspond to the transported leg comparisons `α′` and `β′` by the
two naturality squares. The transported square is the compatibility of
the given comparison of transported cones.

```agda
reflect-transported-square : {C D : CAT} {f f′ g g′ h h′ k k′ : MAP C D}
  (fs : f =₁ f′) (gs : g =₁ g′) (ft : h =₁ h′) (gt : k =₁ k′)
  (τs : f =₁ g) (τt : h =₁ k) (α : f =₁ h) (β : g =₁ k)
  (α′ : f′ =₁ h′) (β′ : g′ =₁ k′)
  → (ft ∙ α) =₂ (α′ ∙ fs) → (gt ∙ β) =₂ (β′ ∙ gs)
  → (changeEndpoints ft gt τt ∙ α′) =₂ (β′ ∙ changeEndpoints fs gs τs)
  → (τt ∙ α) =₂ (β ∙ τs)
reflect-transported-square fs gs ft gt τs τt α β α′ β′
  left-natural right-natural transported =
  changeEndpoints-reflect fs gt (τt ∙ α) (β ∙ τs)
    (changeEndpoints-comp fs gs gt β τs ∙
    (isoComp-cong
      ((square-to-changeEndpoints gs gt β β′ right-natural) ⁻¹)
      (idIso (changeEndpoints fs gs τs)) ∙
    (transported ∙
    (isoComp-cong (idIso (changeEndpoints ft gt τt))
      (square-to-changeEndpoints fs ft α α′ left-natural) ∙
      (changeEndpoints-comp fs ft gt τt α) ⁻¹))))
```
