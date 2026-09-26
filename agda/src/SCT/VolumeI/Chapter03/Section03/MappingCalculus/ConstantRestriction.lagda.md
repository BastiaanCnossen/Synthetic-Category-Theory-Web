# Restriction to constant interval diagrams

For an anima `X`, restriction along `X × [1] → X` embeds the mapping
anima into every target. Rezk identifies constant arrows with the
collection of isomorphisms. Apply `Map(X,-)`, uncurry, and use the core
universal property. This supplies prescribed identification lifting for
the pushout description of localization.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter03.Section03.MappingCalculus.ConstantRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section04.Uncurrying 𝒯 M using (module ExponentialLaw)
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core; coreInclusion; core-universal)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P
  using (IsEmbedding; embedding-cong; equivalence-isEmbedding; module LeftCancellation)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCharacterizations 𝒯 M P using (map-preserves-embedding)
open import SCT.VolumeI.Chapter03.Section01.IsomorphismCollections 𝒯 M ℱ P I E S Q
  using (constantMap; constantMap-evaluation; isomorphismInclusion; isomorphismInclusion-isEmbedding; module WithRezk)
open WithRezk R
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.RestrictionLifting 𝒯 M P using (module Lift)

module Constants (D : CAT) where
  abstract
    embedding : IsEmbedding (constantMap D)
    embedding = embedding-cong (identityComparison-over-morphisms D)
      (LeftCancellation.compose (identityComparison D) (isomorphismInclusion D)
        (isomorphismInclusion-isEmbedding D)
        (equivalence-isEmbedding _ (identityComparison-isEquiv D)))

module Restriction (X D : CAT) (xAn : isAn X) where
  N = Map X (Core D)
  constants = constantMap D
  i = coreInclusion D
  e = mapEval {X} {Core D}
  r = Associativity.backward N X [1]
  change = productMap (id N) (pr₁ {X} {[1]})
  module Exponential = ExponentialLaw X [1] D xAn
  source = mapPost {C = X} i
  target = mapPre {D = D} (pr₁ {X} {[1]})
  route = Exponential.forward ∘ mapPost {C = X} constants

  abstract
    double-evaluation : mapUncurry (mapUncurry (mapPost {C = X} constants)) =₁ ((i ∘ e) ∘ pr₁)
    double-evaluation = (comp-assoc pr₁ e i) ⁻¹ ∙
      ((i ◁ pair-β₁ (e ∘ pr₁) (id [1] ∘ pr₂)) ∙
        (comp-assoc (productMap e (id [1])) pr₁ i ∙
          ((constantMap-evaluation D ▷ productMap e (id [1])) ∙
            (mapUncurry-restrict constants e ∙ mapUncurry-cong (mapPost-β constants)))))

    parameter : (pr₁ ∘ r) =₁ change
    parameter = (pair-cong (comp-unitˡ pr₁) (idIso (pr₁ ∘ pr₂))) ⁻¹ ∙
      pair-β₁ (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂)

    route-evaluation : mapUncurry route =₁ ((i ∘ e) ∘ change)
    route-evaluation = ((i ∘ e) ◁ parameter) ∙
      (comp-assoc r pr₁ (i ∘ e) ∙
        ((double-evaluation ▷ r) ∙ Exponential.forward-represents (mapPost constants)))

    restriction-evaluation : mapUncurry (target ∘ source) =₁ ((i ∘ e) ∘ change)
    restriction-evaluation = (mapPost-β i ▷ change) ∙ mapPre-uncurry pr₁ source

    comparison : route =₁ (target ∘ source)
    comparison = mapReflect (map-isAn X (Core D)) _ _
      ((restriction-evaluation) ⁻¹ ∙ route-evaluation)

    source-isEquiv : IsEquiv source
    source-isEquiv = core-universal X D xAn

    route-isEmbedding : IsEmbedding route
    route-isEmbedding = LeftCancellation.compose (mapPost constants) Exponential.forward
      (equivalence-isEmbedding _ Exponential.forward-isEquiv)
      (map-preserves-embedding X constants (Constants.embedding D))

    cancel-source : ((target ∘ source) ∘ IsEquiv.inverse source-isEquiv) =₁ target
    cancel-source = comp-unitʳ target ∙
      ((target ◁ (IsEquiv.retractionIso source-isEquiv) ⁻¹) ∙
        comp-assoc (IsEquiv.inverse source-isEquiv) source target)

    isEmbedding : IsEmbedding target
    isEmbedding = embedding-cong cancel-source
      (LeftCancellation.compose (IsEquiv.inverse source-isEquiv) (target ∘ source)
        (embedding-cong comparison route-isEmbedding)
        (equivalence-isEmbedding _ (equiv-inverse source-isEquiv)))

  module Identification (f g : MAP X D) (α : (f ∘ pr₁ {D = [1]}) =₁ (g ∘ pr₁)) where
    open Lift (pr₁ {X} {[1]}) isEmbedding f g α public using (lift; image; factorization)
```
