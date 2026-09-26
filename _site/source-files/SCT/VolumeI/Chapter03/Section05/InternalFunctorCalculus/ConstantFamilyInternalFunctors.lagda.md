# Internal functors from a constant family

For `exercise:Description_Mapping_Object_Over_Gamma`, the pullback of
`Fun(D,E) → Fun(D,Γ)` along the constant-family functor has the required
relative mapping property. A map over `Γ` first gives a functor over its
constant family; the relative exponential law then uncurries it.

We use `Γ × D → Γ` for the constant family. Interchanging the two product
factors gives the manuscript's `D × Γ → Γ`. The final comparison also
replaces `K × D` by the chosen pullback, retaining its structure functor.
The maps below specify the comparison as this composite of equivalences.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.InternalFunctorCalculus.ConstantFamilyInternalFunctors
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M using (mapPost; mapPost-isEquiv)
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProductSquares 𝒯 P using (module FirstFactor)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.Currying.EvaluatedPullbackTargets 𝒯 M ℱ P using (module PullbackTarget)
open import SCT.VolumeI.Chapter03.Section05.Currying.EvaluatedRelativeExponentialLaw 𝒯 M ℱ P using (module Law)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.SourceChange 𝒯 M ℱ P using (module Change)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.EvaluatedPrecomposition 𝒯 M ℱ P using (module Precompose)

module ConstantFamily (D : CAT) {E Γ : CAT} (q : MAP E Γ) where
  constant : MAP Γ (Fun D Γ)
  constant = funCurry pr₁
  category : CAT
  category = Pullback (funPost q) constant
  projection : MAP category Γ
  projection = pullback₂
  sections : MAP category (Fun D E)
  sections = pullback₁

  abstract
    uncurry-constant : {K : CAT} (k : MAP K Γ) →
      funUncurry (constant ∘ k) =₁ (k ∘ pr₁)
    uncurry-constant k = pair-β₁ (k ∘ pr₁) (id D ∘ pr₂) ∙
      ((funCurry-β pr₁ ▷ productMap k (id D)) ∙ funUncurry-restrict constant k)

  evaluation : FunctorOver (projection ∘ pr₁ {D = D}) q
  evaluation = record { lift = funUncurry sections
    ; comparison = uncurry-constant projection ∙
        (funUncurryIso (pullbackMatch {f = funPost q} {constant}) ∙
          (funPost-uncurry q sections) ⁻¹) }

  module At {K : CAT} (k : MAP K Γ) where
    module Target = PullbackTarget constant (funPost q) k
    module Exponential = Law q (constant ∘ k)
    module Structure = Change (uncurry-constant k) q

    functor : MAP (FunOver k projection) (FunOver (k ∘ pr₁ {D = D}) q)
    functor = Structure.functor ∘ (Exponential.functor ∘ Target.functor)
    abstract
      functor-isEquiv : IsEquiv functor
      functor-isEquiv = equiv-compose (Exponential.functor ∘ Target.functor) Structure.functor
        (equiv-compose Target.functor Exponential.functor Target.functor-isEquiv Exponential.functor-isEquiv)
        Structure.functor-isEquiv

    maps : MAP (MapOver k projection) (MapOver (k ∘ pr₁ {D = D}) q)
    maps = mapPost functor
    maps-isEquiv : IsEquiv maps
    maps-isEquiv = mapPost-isEquiv functor functor-isEquiv

    -- Replace the displayed product by the chosen pullback over Γ.
    module Domain = FirstFactor k D
    structure : MAP (Pullback k (pr₁ {Γ} {D})) Γ
    structure = k ∘ pullback₁
    inclusion : FunctorOver (k ∘ pr₁ {D = D}) structure
    inclusion = record { lift = pullbackLift Domain.square
      ; comparison = (k ◁ ConeIso.leftIso (pullbackLift-β Domain.square)) ∙
          comp-assoc (pullbackLift Domain.square) pullback₁ k }
    module Restriction = Precompose q inclusion
    abstract
      restriction-isEquiv : IsEquiv Restriction.functor
      restriction-isEquiv = Restriction.Equivalence.functor-isEquiv Domain.square-isPullback
    relative-functor : MAP (FunOver k projection) (FunOver structure q)
    relative-functor = IsEquiv.inverse restriction-isEquiv ∘ functor
    abstract
      relative-functor-isEquiv : IsEquiv relative-functor
      relative-functor-isEquiv = equiv-compose functor (IsEquiv.inverse restriction-isEquiv)
        functor-isEquiv (equiv-inverse restriction-isEquiv)
    relative-maps : MAP (MapOver k projection) (MapOver structure q)
    relative-maps = mapPost relative-functor
    relative-maps-isEquiv : IsEquiv relative-maps
    relative-maps-isEquiv = mapPost-isEquiv relative-functor relative-functor-isEquiv
```
