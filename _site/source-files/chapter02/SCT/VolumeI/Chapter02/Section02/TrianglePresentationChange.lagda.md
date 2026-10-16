# Changing the three families of a triangle presentation

A comparison of each of the three framed edges carries a triangle
presentation to the new families. The triangle itself is unchanged.
Each corner is obtained by composing its original whole cone comparison
with the comparison of the two endpoint frames.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.TrianglePresentationChange where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications using (cone-compose)
open import SCT.VolumeI.Chapter01.Section06.ConeFramings using (framed-cone-comparison)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (MorphismFamily; MorphismFamilyIdentification; ev₀; ev₁)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations using (module FamilyComparison)
open import SCT.VolumeI.Chapter02.Section02.FramedTrianglePresentations using (TrianglePresentation; triangle-presentation; module PresentedTriangle)

module ReplacePresentation {Γ : Context} {P C : CAT Γ} {f g h : MAP P C}
  {alpha alpha′ : MorphismFamily f g} {beta beta′ : MorphismFamily g h}
  {gamma gamma′ : MorphismFamily f h}
  (given : TrianglePresentation alpha beta gamma)
  (first : MorphismFamilyIdentification One alpha alpha′)
  (second : MorphismFamilyIdentification One beta beta′)
  (long : MorphismFamilyIdentification One gamma gamma′) where
  private
    module T = PresentedTriangle given
    module A = MorphismFamily alpha
    module A′ = MorphismFamily alpha′
    module B = MorphismFamily beta
    module B′ = MorphismFamily beta′
    module G = MorphismFamily gamma
    module G′ = MorphismFamily gamma′
    module F = FamilyComparison first
    module S = FamilyComparison second
    module L = FamilyComparison long
    middle = cone-compose
      (framed-cone-comparison (ev₁ {C = C}) ev₀ A.target-frame B.source-frame A′.target-frame B′.source-frame
        F.identification S.identification F.target S.source) T.short-comparison
    source = cone-compose
      (framed-cone-comparison (ev₀ {C = C}) ev₀ G.source-frame A.source-frame G′.source-frame A′.source-frame
        L.identification F.identification L.source F.source) T.source-comparison
    target = cone-compose
      (framed-cone-comparison (ev₁ {C = C}) ev₁ G.target-frame B.target-frame G′.target-frame B′.target-frame
        L.identification S.identification L.target S.target) T.target-comparison
  value : TrianglePresentation alpha′ beta′ gamma′
  value = triangle-presentation T.triangle
    (ConeIdentification₁.left middle) (ConeIdentification₁.right middle) (ConeIdentification₁.left source)
    (ConeIdentification₁.compatible middle) (ConeIdentification₁.compatible source)
    (ConeIdentification₁.compatible target)
```
