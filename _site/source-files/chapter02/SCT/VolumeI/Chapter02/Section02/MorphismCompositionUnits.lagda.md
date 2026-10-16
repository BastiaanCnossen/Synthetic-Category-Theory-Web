# The unit laws for framed morphism families

The universal unit triangles restrict along the arrow of a given family.
Its original endpoint identifications then change the three vertex frames.
The native identity-family restriction and endpoint-change comparisons,
together with the original left unitor of the universal arrow, identify
all three edges with the required families. The same triangle presentation
therefore supplies both unit laws for the actual chosen composition.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.MorphismCompositionUnits where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (comp-unitˡ; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase using (compatible-comp; compatible-unitˡ)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; ev₀; ev₁; MorphismFamily; MorphismFamilyIdentification; identity-family)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations
  using (family-comparison; restrict-family; retarget-family; retarget-family-comparison; module FamilyComparison)
open import SCT.VolumeI.Chapter02.Section01.IdentityFamilyTransport using (module IdentityFamilyChange)
open import SCT.VolumeI.Chapter02.Section01.IdentityFamilyRestriction using (module IdentityFamilyRestriction)
open import SCT.VolumeI.Chapter02.Section01.Triangles using (short-edges)
open import SCT.VolumeI.Chapter02.Section02.UnitTriangles using (module UniversalEdges)
open import SCT.VolumeI.Chapter02.Section02.UnitPresentations using (module UnitVertices; module UnitShortEdges)
open import SCT.VolumeI.Chapter02.Section02.FramedTrianglePresentations
  using (TrianglePresentation; triangle-presentation; presented-composition; module RestrictPresentation; module RetargetPresentation)
open import SCT.VolumeI.Chapter02.Section02.TrianglePresentationChange using (module ReplacePresentation)
import SCT.VolumeI.Chapter02.Section02.MorphismComposition as MC

private
  module _ {Γ : Context} {P C : CAT Γ} {f g : MAP P C}
    {alpha beta gamma : MorphismFamily f g} where
    compose-comparisons : MorphismFamilyIdentification One beta gamma
      → MorphismFamilyIdentification One alpha beta → MorphismFamilyIdentification One alpha gamma
    compose-comparisons second first = family-comparison alpha gamma (G.identification ∙ F.identification)
      (compatible-comp ev₀ _ _ _ G.identification F.identification G.source F.source)
      (compatible-comp ev₁ _ _ _ G.identification F.identification G.target F.target)
      where
        module F = FamilyComparison first
        module G = FamilyComparison second

module UniversalUnitPresentations {Γ : Context} (C : CAT Γ) where
  private
    module U = UniversalEdges C
    module V = UnitVertices C
    module S = UnitShortEdges C
  source : TrianglePresentation (identity-family (ev₀ {C = C})) U.universal-arrow U.universal-arrow
  source = triangle-presentation S.Source.triangle
    U.Source.First.comparison U.Source.Second.comparison U.Source.Long.comparison
    V.Source.MiddleVertex.vertex-equation V.Source.SourceVertex.vertex-equation V.Source.TargetVertex.vertex-equation
  target : TrianglePresentation U.universal-arrow (identity-family (ev₁ {C = C})) U.universal-arrow
  target = triangle-presentation S.Target.triangle
    U.Target.First.comparison U.Target.Second.comparison U.Target.Long.comparison
    V.Target.MiddleVertex.vertex-equation V.Target.SourceVertex.vertex-equation V.Target.TargetVertex.vertex-equation

module FamilyUnitPresentations {Γ : Context} {P C : CAT Γ} {f g : MAP P C}
  (alpha : MorphismFamily f g) where
  private
    module A = MorphismFamily alpha
    module U = UniversalEdges C
    module Universal = UniversalUnitPresentations C
    h = A.arrow
    p = A.source-frame
    q = A.target-frame
    universal : MorphismFamilyIdentification One
      (retarget-family (restrict-family U.universal-arrow h) p q) alpha
    universal = family-comparison _ alpha (comp-unitˡ h)
      (compatible-unitˡ ev₀ h p) (compatible-unitˡ ev₁ h q)
    source-identity : MorphismFamilyIdentification One
      (retarget-family (restrict-family (identity-family (ev₀ {C = C})) h) p p) (identity-family f)
    source-identity = compose-comparisons (IdentityFamilyChange.value p)
      (retarget-family-comparison p p (IdentityFamilyRestriction.value (ev₀ {C = C}) h))
    target-identity : MorphismFamilyIdentification One
      (retarget-family (restrict-family (identity-family (ev₁ {C = C})) h) q q) (identity-family g)
    target-identity = compose-comparisons (IdentityFamilyChange.value q)
      (retarget-family-comparison q q (IdentityFamilyRestriction.value (ev₁ {C = C}) h))
    source-triangle = RetargetPresentation.value (RestrictPresentation.value Universal.source h) p p q
    target-triangle = RetargetPresentation.value (RestrictPresentation.value Universal.target h) p q q
  source : TrianglePresentation (identity-family f) alpha alpha
  source = ReplacePresentation.value source-triangle source-identity universal universal
  target : TrianglePresentation alpha (identity-family g) alpha
  target = ReplacePresentation.value target-triangle universal target-identity universal

module MorphismCompositionUnits {Γ : Context} (C : CAT Γ) (segal : IsEquiv (short-edges C)) where
  source-unit : {P : CAT Γ} {f g : MAP P C} (alpha : MorphismFamily f g)
    → MorphismFamilyIdentification One (MC.Composition.compose C segal alpha (identity-family f)) alpha
  source-unit {f = f} alpha = presented-composition segal (identity-family f) alpha alpha
    (FamilyUnitPresentations.source alpha)
  target-unit : {P : CAT Γ} {f g : MAP P C} (alpha : MorphismFamily f g)
    → MorphismFamilyIdentification One (MC.Composition.compose C segal (identity-family g) alpha) alpha
  target-unit {g = g} alpha = presented-composition segal alpha (identity-family g) alpha
    (FamilyUnitPresentations.target alpha)
```
