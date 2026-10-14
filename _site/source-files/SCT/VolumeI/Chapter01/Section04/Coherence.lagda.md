# Coherence of composition on mapping animae

The comparisons in `InternalCoherence` are chosen on the universal
mapping-anima parameters. Their occurrences below are the normalized
restrictions of those same choices. The triangle and pentagon therefore
compare the specified internal associators and unitors.

The calculation has two parts. `RetainedComparisonLaws` and `InternalPentagon`
prove the identities for comparisons lifted directly at a common anima
parameter. `UniversalAssociatorRestriction` and `UniversalUnitChange`
identify the restricted universal choices with those direct lifts, using
the route calculations in `UniversalCoherence`. Applying those
identifications gives the book's coherence laws.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Substitution.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as MappingAnimae
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.UniversalCoherence as UniversalCoherence
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.UniversalAssociatorRestriction as UniversalAssociatorRestriction
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.UniversalUnitChange as UniversalUnitChange

module SCT.VolumeI.Chapter01.Section04.Coherence
  {c m a : Level} (𝒯 : Theory c m a)
  (M : MappingAnimae.MappingAnimae 𝒯) where

open Setup 𝒯
open MappingAnimae.MappingAnimae M
open MapComposition 𝒯 M using (composeTerm; identityTerm)
open InternalCoherence 𝒯 M using (module Triangle; module Pentagon)
open UniversalCoherence 𝒯 M using
  (universal-triangle-from-comparisons; universal-pentagon-from-comparisons)
open UniversalAssociatorRestriction 𝒯 M using (universal-assoc)
open UniversalUnitChange 𝒯 M using (universal-unitˡ; universal-unitʳ)
```

First we allow any common anima parameter. Its anima witness is used to
reflect the evaluated identifications through the mapping-anima universal
property.

```agda
abstract
  triangle : {P A B C : CAT} (pAn : isAn P)
    (g : MAP P (Map B C)) (f : MAP P (Map A B))
    → Triangle.Statement g f
  triangle {B = B} pAn g f = universal-triangle-from-comparisons pAn g f
    (universal-unitʳ pAn g) (universal-unitˡ pAn f)
    (universal-assoc pAn g (identityTerm B) f)

  pentagon : {P A B C D E : CAT} (pAn : isAn P)
    (k : MAP P (Map D E)) (h : MAP P (Map C D))
    (g : MAP P (Map B C)) (f : MAP P (Map A B))
    → Pentagon.Statement k h g f
  pentagon pAn k h g f = universal-pentagon-from-comparisons pAn k h g f
    (universal-assoc pAn (composeTerm k h) g f)
    (universal-assoc pAn k h (composeTerm g f))
    (universal-assoc pAn k h g)
    (universal-assoc pAn k (composeTerm h g) f)
    (universal-assoc pAn h g f)
```

For the book's triangle, the parameter is the product of the two mapping
animae. Its projections represent the two composable functors jointly.

```agda
module UniversalTriangle (A B C : CAT) where
  parameter : CAT
  parameter = Map B C × Map A B

  outer : MAP parameter (Map B C)
  outer = pr₁

  inner : MAP parameter (Map A B)
  inner = pr₂

  law : Triangle.Statement outer inner
  law = triangle (product-isAn (map-isAn B C) (map-isAn A B)) outer inner

  in-context : {Γ : CAT} (σ : MAP Γ parameter)
    → (Triangle.short outer inner ▷ σ) =₂ (Triangle.long outer inner ▷ σ)
  in-context σ = preWhisker σ ◁ law
```

For the pentagon, we use a product of four mapping animae. All five edges
are restrictions to this single parameter, with the endpoint comparisons
recorded by `internalAssoc`.

```agda
module UniversalPentagon (A B C D E : CAT) where
  parameter : CAT
  parameter = ((Map D E × Map C D) × Map B C) × Map A B

  fourth : MAP parameter (Map D E)
  fourth = (pr₁ ∘ pr₁) ∘ pr₁

  third : MAP parameter (Map C D)
  third = (pr₂ ∘ pr₁) ∘ pr₁

  second : MAP parameter (Map B C)
  second = pr₂ ∘ pr₁

  first : MAP parameter (Map A B)
  first = pr₂

  law : Pentagon.Statement fourth third second first
  law = pentagon
    (product-isAn
      (product-isAn
        (product-isAn (map-isAn D E) (map-isAn C D)) (map-isAn B C))
      (map-isAn A B))
    fourth third second first

  in-context : {Γ : CAT} (σ : MAP Γ parameter)
    → (Pentagon.short fourth third second first ▷ σ) =₂
        (Pentagon.long fourth third second first ▷ σ)
  in-context σ = preWhisker σ ◁ law
```

The `in-context` declarations restrict the whole universal identity along
an arbitrary categorical parameter. Their boundaries display that
restriction explicitly. They do not use currying with a non-anima
parameter or assume additional contextual coherence.
