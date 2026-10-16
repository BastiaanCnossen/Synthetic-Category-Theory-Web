# Transporting and gluing complete triangle presentations

Changing a triangle family transports its three complete corner comparisons
together. The first, second and long edge comparisons are shared across those
corners. No new triangle completion or Segal inverse is chosen.

Gluing two presentations of the same diagonal uses the actual square
restriction cone and its full beta. The two transported presentations retain
their given boundary families, and their long-edge comparisons agree across
the original native matching of that cone.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.GluedTrianglePresentations where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-cong; comp₌-assoc; comp-inv-left)
open import SCT.VolumeI.Chapter01.Section06.Cones
  using (Cone; ConeIdentification₁; cone-restrict)
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
  using (cone-action-One; cone-compose)
open import SCT.VolumeI.Chapter01.Section06.ConeFramings using (framed-cone)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre)
open import SCT.VolumeI.Chapter02.Section01.WalkingTriangle using (d₁)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (ev₀; ev₁; MorphismFamily)
open import SCT.VolumeI.Chapter02.Section01.Triangles
  using (Triangles; edge₀; edge₁; edge₂; triangle-cone)
open import SCT.VolumeI.Chapter02.Section01.SquareGluing
  using (Squares; j₀; j₁; square-cone; module Families)
open import SCT.VolumeI.Chapter02.Section02.MorphismComposition using (module ComposableFamilies)
open import SCT.VolumeI.Chapter02.Section02.TriangleCornerFrames using (module TriangleCornerFrames)
open import SCT.VolumeI.Chapter02.Section02.FramedTrianglePresentations
  using (TrianglePresentation; triangle-presentation; module PresentedTriangle)

module ChangeTriangle {Γ : Context} {P C : CAT Γ} {x y z : MAP P C}
  {alpha : MorphismFamily x y} {beta : MorphismFamily y z} {gamma : MorphismFamily x z}
  (given : TrianglePresentation alpha beta gamma)
  {sigma : MAP P (Triangles C)} (delta : sigma =₁ PresentedTriangle.triangle given) where
  module Before = PresentedTriangle given
  private
    module Alpha = MorphismFamily alpha
    module Beta = MorphismFamily beta
    module Gamma = MorphismFamily gamma
    module Corners = TriangleCornerFrames C

  triangle : MAP P (Triangles C)
  triangle = sigma

  first : (edge₂ {C = C} ∘ triangle) =₁ Alpha.arrow
  first = Before.first ∙ (edge₂ ◁ delta)
  second : (edge₀ {C = C} ∘ triangle) =₁ Beta.arrow
  second = Before.second ∙ (edge₀ ◁ delta)
  long : (edge₁ {C = C} ∘ triangle) =₁ Gamma.arrow
  long = Before.long ∙ (edge₁ ◁ delta)

  short-comparison : ConeIdentification₁ (cone-restrict triangle (triangle-cone C))
    (ComposableFamilies.cone alpha beta)
  short-comparison = cone-compose Before.short-comparison
    (cone-action-One (triangle-cone C) delta)

  source-comparison : ConeIdentification₁ (cone-restrict triangle Corners.source-cone)
    (framed-cone ev₀ ev₀ Gamma.arrow Alpha.arrow Gamma.source-frame Alpha.source-frame)
  source-comparison = cone-compose Before.source-comparison
    (cone-action-One Corners.source-cone delta)

  target-comparison : ConeIdentification₁ (cone-restrict triangle Corners.target-cone)
    (framed-cone ev₁ ev₁ Gamma.arrow Beta.arrow Gamma.target-frame Beta.target-frame)
  target-comparison = cone-compose Before.target-comparison
    (cone-action-One Corners.target-cone delta)

  value : TrianglePresentation alpha beta gamma
  value = triangle-presentation triangle first second long
    (ConeIdentification₁.compatible short-comparison)
    (ConeIdentification₁.compatible source-comparison)
    (ConeIdentification₁.compatible target-comparison)
```

The actual gluing comparison transports both entire presentations. Its
compatibility field retains the supplied diagonal matching; it is not
replaced by a separately pasted restriction-compositor word.

```agda
module Glue {Γ : Context} {P C : CAT Γ} {x y z w : MAP P C}
  {top : MorphismFamily x y} {right : MorphismFamily y z}
  {left : MorphismFamily x w} {bottom : MorphismFamily w z}
  {diagonal : MorphismFamily x z}
  (given-upper : TrianglePresentation top right diagonal)
  (given-lower : TrianglePresentation left bottom diagonal) where
  module GivenUpper = PresentedTriangle given-upper
  module GivenLower = PresentedTriangle given-lower

  triangles : Cone (funPre {D = C} d₁) (funPre d₁) P
  triangles = record
    { left = GivenUpper.triangle; right = GivenLower.triangle
    ; match = (GivenLower.long ⁻¹) ∙ GivenUpper.long }

  square : MAP P (Squares C)
  square = Families.glue C triangles

  restricted-cone : Cone (funPre {D = C} d₁) (funPre d₁) P
  restricted-cone = cone-restrict square (square-cone C)

  gluing-comparison : ConeIdentification₁ restricted-cone triangles
  gluing-comparison = Families.glue-β C triangles

  upper-triangle : MAP P (Triangles C)
  upper-triangle = funPre {D = C} j₀ ∘ square
  lower-triangle : MAP P (Triangles C)
  lower-triangle = funPre {D = C} j₁ ∘ square

  upper-identification : upper-triangle =₁ GivenUpper.triangle
  upper-identification = ConeIdentification₁.left gluing-comparison
  lower-identification : lower-triangle =₁ GivenLower.triangle
  lower-identification = ConeIdentification₁.right gluing-comparison

  module Upper = ChangeTriangle given-upper {sigma = upper-triangle} upper-identification
  module Lower = ChangeTriangle given-lower {sigma = lower-triangle} lower-identification

  upper-presentation : TrianglePresentation top right diagonal
  upper-presentation = Upper.value
  lower-presentation : TrianglePresentation left bottom diagonal
  lower-presentation = Lower.value

  upper-long : (edge₁ {C = C} ∘ upper-triangle) =₁ MorphismFamily.arrow diagonal
  upper-long = Upper.long
  lower-long : (edge₁ {C = C} ∘ lower-triangle) =₁ MorphismFamily.arrow diagonal
  lower-long = Lower.long

  specified-matching : (edge₁ {C = C} ∘ upper-triangle) =₁ (edge₁ ∘ lower-triangle)
  specified-matching = Cone.match restricted-cone

  diagonal-compatible : (lower-long ∙ specified-matching) =₂ upper-long
  diagonal-compatible = comp₌-cong
      (comp-inv-left GivenLower.long GivenUpper.long) (id₌ (edge₁ ◁ upper-identification)) ∙
    ((comp₌-assoc GivenLower.long (Cone.match triangles) (edge₁ ◁ upper-identification)) ⁻¹ ∙
      (comp₌-cong (id₌ GivenLower.long) ((ConeIdentification₁.compatible gluing-comparison) ⁻¹) ∙
        comp₌-assoc GivenLower.long (edge₁ ◁ lower-identification) specified-matching))
```
