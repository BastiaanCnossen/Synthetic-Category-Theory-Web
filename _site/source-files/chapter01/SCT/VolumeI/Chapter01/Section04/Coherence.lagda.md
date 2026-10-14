# Coherence of the chosen composition laws

The default unitors and associator have the directly recovered evaluation
images at an anima parameter. Comparing the actual three triangle edges and
five pentagon edges transports the established recovered coherence laws.
The universal products of mapping animae satisfy the required hypothesis.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.Coherence where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; module Composition; module Boundaries)
open Composition
open Boundaries using (TriangleCommutes; PentagonCommutes; TriangleSource; TriangleTarget; PentagonSource; PentagonTarget)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp₌-cong)
import SCT.VolumeI.Chapter01.Section03.Products.BinaryFunctors as Binary
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae using (Map; map-isAn)
open import SCT.VolumeI.Chapter01.Section04.Composition using (compose; identity-map; mapComp)
open import SCT.VolumeI.Chapter01.Section04.CompositionLaws using (compositionTriangle; compositionPentagon)
open import SCT.VolumeI.Chapter01.Section04.CompositionCoherence using (recovered-triangle; recovered-pentagon)
open import SCT.VolumeI.Chapter01.Section04.CompositionLawRestriction
  using (default-unitˡ-recovered; default-unitʳ-recovered; compose-assoc-agreement)

module _ {Γ : Context} where
  opaque
    triangle : {P A B C : CAT Γ} (pAn : isAn P)
      (x : MAP P (Map A B)) (y : MAP P (Map B C))
      → TriangleCommutes (compositionTriangle x y)
    triangle {B = B} pAn x y =
      let direct-change = Binary.binary-cong₂ mapComp
            (default-unitʳ-recovered pAn y) (id₌ (id₌ x))
          first-change = compose-assoc-agreement pAn y (identity-map B) x
          second-change = Binary.binary-cong₂ mapComp
            (id₌ (id₌ y)) (default-unitˡ-recovered pAn x)
      in comp₌-cong (second-change ⁻¹) (first-change ⁻¹) ∙
        (recovered-triangle pAn x y ∙ direct-change)

    pentagon : {P A B C D E : CAT Γ} (pAn : isAn P)
      (x : MAP P (Map A B)) (y : MAP P (Map B C))
      (z : MAP P (Map C D)) (w : MAP P (Map D E))
      → PentagonCommutes (compositionPentagon x y z w)
    pentagon pAn x y z w =
      let first-short-change = compose-assoc-agreement pAn (compose w z) y x
          second-short-change = compose-assoc-agreement pAn w z (compose y x)
          first-long-change = Binary.binary-cong₂ mapComp
            (compose-assoc-agreement pAn w z y) (id₌ (id₌ x))
          middle-long-change = compose-assoc-agreement pAn w (compose z y) x
          last-long-change = Binary.binary-cong₂ mapComp
            (id₌ (id₌ w)) (compose-assoc-agreement pAn z y x)
          short-change = comp₌-cong second-short-change first-short-change
          long-change = comp₌-cong (comp₌-cong last-long-change middle-long-change) first-long-change
      in long-change ⁻¹ ∙ (recovered-pentagon pAn x y z w ∙ short-change)
```

The two mapping projections give the universal triangle. Restriction
precomposes its complete chosen routes, preserving their exact witnesses.

```agda
  module UniversalTriangle (A B C : CAT Γ) where
    parameter : CAT Γ
    parameter = Map B C × Map A B

    outer : MAP parameter (Map B C)
    outer = pr₁
    inner : MAP parameter (Map A B)
    inner = pr₂

    law : TriangleCommutes (compositionTriangle inner outer)
    law = triangle (product-isAn (map-isAn B C) (map-isAn A B)) inner outer

    restrict : {T : CAT Γ} (σ : MAP T parameter)
      → (TriangleSource (compositionTriangle inner outer) ▷ σ) =₂
          (TriangleTarget (compositionTriangle inner outer) ▷ σ)
    restrict σ = preWhisker σ ◁ law
```

The four universal mapping terms use the specified left-associated
product. Whole-route restriction requires no anima hypothesis on T.
It retains the universal diagram's routes rather than identifying them
with freshly normalized default laws at T.

```agda
  module UniversalPentagon (A B C D E : CAT Γ) where
    parameter : CAT Γ
    parameter = ((Map D E × Map C D) × Map B C) × Map A B

    fourth : MAP parameter (Map D E)
    fourth = (pr₁ ∘ pr₁) ∘ pr₁
    third : MAP parameter (Map C D)
    third = (pr₂ ∘ pr₁) ∘ pr₁
    second : MAP parameter (Map B C)
    second = pr₂ ∘ pr₁
    first : MAP parameter (Map A B)
    first = pr₂

    law : PentagonCommutes (compositionPentagon first second third fourth)
    law = pentagon
      (product-isAn
        (product-isAn
          (product-isAn (map-isAn D E) (map-isAn C D)) (map-isAn B C))
        (map-isAn A B)) first second third fourth

    restrict : {T : CAT Γ} (σ : MAP T parameter)
      → (PentagonSource (compositionPentagon first second third fourth) ▷ σ) =₂
          (PentagonTarget (compositionPentagon first second third fourth) ▷ σ)
    restrict σ = preWhisker σ ◁ law
```
