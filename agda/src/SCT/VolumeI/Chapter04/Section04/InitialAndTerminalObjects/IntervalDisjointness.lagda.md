# No morphisms from one to zero

For `cor:No_Morphisms_From_One_To_Zero`, work over the entire reverse hom
category. Its universal arrow has an inverse by the universal properties
of the endpoints. Rezk then identifies the endpoints over that category.
The interval core and disjoint coproducts force the parameter category
to be empty. All families here have an explicit absolute parameter.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk
import SCT.VolumeI.Chapter02.Section05.Recognition as Recognition

import SCT.VolumeI.Chapter01.Section05.Initial as Initial
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter02.Section01.IntervalCore as IntervalCore

module SCT.VolumeI.Chapter04.Section04.InitialAndTerminalObjects.IntervalDisjointness
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E)
  (A : Recognition.RecognitionAxiom 𝒯 M ℱ P I E R)
  (Z : Initial.InitialStructure 𝒯 M) (Zs : Initial.StrictInitial 𝒯 M Z)
  (B : Coproducts.CoproductStructure 𝒯 M)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (K : IntervalCore.IntervalCoreAxiom 𝒯 M B I) where

open import SCT.VolumeI.Chapter02.Section01.HomAndSlices 𝒯 M ℱ P I
open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.UniversalComparisons 𝒯 M ℱ P I
  using (initial-expression; initial-comparison; terminal-comparison)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionExpressions 𝒯 M ℱ P I E S
  using (compose-expression)
open import SCT.VolumeI.Chapter02.Section03.InvertibleExpressions 𝒯 M ℱ P I E S using (module LiftInverse)
open import SCT.VolumeI.Chapter02.Section03.RezkIdentification 𝒯 M ℱ P I E R using (module Identify)
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (coreInclusion)
open import SCT.VolumeI.Chapter01.Section04.Points 𝒯 M using (nameMap)
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.CoreInclusions 𝒯 M
  using (coreInclusion-name)
open import SCT.VolumeI.Chapter02.Section05.PullbackAnimae 𝒯 M ℱ P I E S Q R A
  using (coreInclusion-isEmbedding)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P
  using (IsEmbedding; embedding-reflect; module LeftCancellation; equivalence-isEmbedding)
open import SCT.VolumeI.Chapter01.Section05.Copairing 𝒯 M B using (copair-β₁; copair-β₂)
open import SCT.VolumeI.Chapter01.Section06.DisjointCoproducts 𝒯 M Z B P U
  using (disjointCone; disjoint-isPullback)
open IntervalCore 𝒯 M B I using (intervalCore)
open IntervalCore.IntervalCoreAxiom K
open Coproducts.CoproductStructure B
open Initial.InitialStructure Z
open Initial.StrictInitial Zs
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (Cone)
open Endpoints.IntervalEndpoints E

reverse-hom = Hom [1] one zero

universal-arrow : MorphismExpression (const {P = reverse-hom} one) (const zero)
universal-arrow = hom-expression (id reverse-hom)

return-arrow : MorphismExpression (const {P = reverse-hom} zero) (const one)
return-arrow = initial-expression zero zero-isInitial (const one)

abstract
  inverse-at-zero : ExpressionIso (compose-expression return-arrow universal-arrow)
    (identity-expression (const zero))
  inverse-at-zero = initial-comparison zero zero-isInitial (const zero) _ _

  inverse-at-one : ExpressionIso (compose-expression universal-arrow return-arrow)
    (identity-expression (const one))
  inverse-at-one = terminal-comparison one one-isTerminal (const one) _ _

abstract
  endpoints-identification : const {P = reverse-hom} one =₁ const zero
  endpoints-identification = Identify.identification universal-arrow
    (LiftInverse.lift universal-arrow return-arrow return-arrow inverse-at-zero inverse-at-one)

endpoint-inclusion : MAP (One ⊔ One) [1]
endpoint-inclusion = coreInclusion [1] ∘ intervalCore

abstract
  endpoint-inclusion-isEmbedding : IsEmbedding endpoint-inclusion
  endpoint-inclusion-isEmbedding = LeftCancellation.compose intervalCore (coreInclusion [1])
    (coreInclusion-isEmbedding [1]) (equivalence-isEmbedding intervalCore intervalCore-isEquiv)

  source-boundary : (endpoint-inclusion ∘ in₁) =₁ zero
  source-boundary = coreInclusion-name zero ∙
    ((coreInclusion [1] ◁ copair-β₁ (nameMap zero) (nameMap one)) ∙
      comp-assoc in₁ intervalCore (coreInclusion [1]))

  target-boundary : (endpoint-inclusion ∘ in₂) =₁ one
  target-boundary = coreInclusion-name one ∙
    ((coreInclusion [1] ◁ copair-β₂ (nameMap zero) (nameMap one)) ∙
      comp-assoc in₂ intervalCore (coreInclusion [1]))

abstract
  disjoint-matching : (in₂ ∘ terminate reverse-hom) =₁ (in₁ ∘ terminate reverse-hom)
  disjoint-matching = embedding-reflect endpoint-inclusion endpoint-inclusion-isEmbedding _ _
    (θ₀ ⁻¹ ∙ (endpoints-identification ∙ θ₁))
    where
    θ₀ : (endpoint-inclusion ∘ (in₁ ∘ terminate reverse-hom)) =₁ const zero
    θ₀ = (source-boundary ▷ terminate reverse-hom) ∙
      (comp-assoc (terminate reverse-hom) in₁ endpoint-inclusion) ⁻¹
    θ₁ : (endpoint-inclusion ∘ (in₂ ∘ terminate reverse-hom)) =₁ const one
    θ₁ = (target-boundary ▷ terminate reverse-hom) ∙
      (comp-assoc (terminate reverse-hom) in₂ endpoint-inclusion) ⁻¹

empty-cone : Cone (in₂ {One} {One}) in₁ reverse-hom
empty-cone = record { left = terminate reverse-hom ; right = terminate reverse-hom
  ; match = disjoint-matching }

reverse-hom-to-empty : MAP reverse-hom Zero
reverse-hom-to-empty = IsEquiv.inverse (disjoint-isPullback One One) ∘ pullbackLift empty-cone

abstract
  reverse-hom-isEmpty : IsEquiv reverse-hom-to-empty
  reverse-hom-isEmpty = into-zero-isEquiv reverse-hom-to-empty
```
