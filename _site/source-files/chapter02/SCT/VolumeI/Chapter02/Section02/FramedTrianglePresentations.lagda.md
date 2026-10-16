# Triangle presentations with their three corner squares

A triangle presenting three framed morphism families records its three
edge comparisons and the compatibility at each vertex. The middle square
is the matching needed to recover the short-edge comparison; the outer
squares retain the specified endpoint frames of the long edge.

The constructor and named projections expose ordinary dependent-pair data.
This avoids a custom record over the large corner equations while retaining
every specified triangle, edge comparison and compatibility witness.

Restriction and changing the three endpoints act on this same data. They
do not compare arbitrary choices of a Segal inverse or discard a corner.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.FramedTrianglePresentations where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
import Agda.Builtin.Sigma as Data
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares using (replace-sides₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (restrict-triangle)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section06.ConeFramings
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (ev₀; ev₁; MorphismFamily; MorphismFamilyIdentification)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations using (restrict-family; retarget-family)
open import SCT.VolumeI.Chapter02.Section01.Triangles
  using (Triangles; edge₀; edge₁; edge₂; triangle-cone; short-edges)
open import SCT.VolumeI.Chapter02.Section02.TriangleCornerFrames using (module TriangleCornerFrames)
import SCT.VolumeI.Chapter02.Section02.MorphismComposition as MC
open MC using (module ComposableFamilies)
open import SCT.VolumeI.Chapter02.Section02.MorphismCompositionPresentation using (module CompositionPresentation)
open import SCT.VolumeI.Chapter02.Section02.TriangleEndpointComparison using (module TriangleEndpointComparison)

module _ {Γ : Context} where
  MiddleCorner : {P C : CAT Γ} {f g h : MAP P C}
    (alpha : MorphismFamily f g) (beta : MorphismFamily g h)
    (sigma : MAP P (Triangles C))
    (first : (edge₂ {C = C} ∘ sigma) =₁ MorphismFamily.arrow alpha)
    (second : (edge₀ {C = C} ∘ sigma) =₁ MorphismFamily.arrow beta) → Set m
  MiddleCorner {C = C} alpha beta sigma first second =
    (((MorphismFamily.source-frame beta) ⁻¹ ∙ MorphismFamily.target-frame alpha) ∙
      (ev₁ {C = C} ◁ first)) =₂
      ((ev₀ {C = C} ◁ second) ∙ Cone.match (cone-restrict sigma (triangle-cone C)))

  SourceCorner : {P C : CAT Γ} {f g h : MAP P C}
    (alpha : MorphismFamily f g) (gamma : MorphismFamily f h)
    (sigma : MAP P (Triangles C))
    (long : (edge₁ {C = C} ∘ sigma) =₁ MorphismFamily.arrow gamma)
    (first : (edge₂ {C = C} ∘ sigma) =₁ MorphismFamily.arrow alpha) → Set m
  SourceCorner {C = C} alpha gamma sigma long first =
    (((MorphismFamily.source-frame alpha) ⁻¹ ∙ MorphismFamily.source-frame gamma) ∙
      (ev₀ {C = C} ◁ long)) =₂
      ((ev₀ {C = C} ◁ first) ∙ Cone.match (cone-restrict sigma (TriangleCornerFrames.source-cone C)))

  TargetCorner : {P C : CAT Γ} {f g h : MAP P C}
    (beta : MorphismFamily g h) (gamma : MorphismFamily f h)
    (sigma : MAP P (Triangles C))
    (long : (edge₁ {C = C} ∘ sigma) =₁ MorphismFamily.arrow gamma)
    (second : (edge₀ {C = C} ∘ sigma) =₁ MorphismFamily.arrow beta) → Set m
  TargetCorner {C = C} beta gamma sigma long second =
    (((MorphismFamily.target-frame beta) ⁻¹ ∙ MorphismFamily.target-frame gamma) ∙
      (ev₁ {C = C} ◁ long)) =₂
      ((ev₁ {C = C} ◁ second) ∙ Cone.match (cone-restrict sigma (TriangleCornerFrames.target-cone C)))

  TrianglePresentation : {P C : CAT Γ} {f g h : MAP P C}
    (alpha : MorphismFamily f g) (beta : MorphismFamily g h) (gamma : MorphismFamily f h) → Set m
  TrianglePresentation {P} {C} alpha beta gamma =
    Data.Σ (MAP P (Triangles C)) λ triangle →
    Data.Σ ((edge₂ {C = C} ∘ triangle) =₁ MorphismFamily.arrow alpha) λ first →
    Data.Σ ((edge₀ {C = C} ∘ triangle) =₁ MorphismFamily.arrow beta) λ second →
    Data.Σ ((edge₁ {C = C} ∘ triangle) =₁ MorphismFamily.arrow gamma) λ long →
    Data.Σ (MiddleCorner alpha beta triangle first second) λ _ →
    Data.Σ (SourceCorner alpha gamma triangle long first) λ _ →
      TargetCorner beta gamma triangle long second

  triangle-presentation : {P C : CAT Γ} {f g h : MAP P C}
    {alpha : MorphismFamily f g} {beta : MorphismFamily g h} {gamma : MorphismFamily f h}
    (triangle : MAP P (Triangles C))
    (first : (edge₂ {C = C} ∘ triangle) =₁ MorphismFamily.arrow alpha)
    (second : (edge₀ {C = C} ∘ triangle) =₁ MorphismFamily.arrow beta)
    (long : (edge₁ {C = C} ∘ triangle) =₁ MorphismFamily.arrow gamma)
    → MiddleCorner alpha beta triangle first second
    → SourceCorner alpha gamma triangle long first
    → TargetCorner beta gamma triangle long second
    → TrianglePresentation alpha beta gamma
  triangle-presentation triangle first second long middle source target =
    Data._,_ triangle (Data._,_ first (Data._,_ second (Data._,_ long
      (Data._,_ middle (Data._,_ source target)))))

  module PresentedTriangle {P C : CAT Γ} {f g h : MAP P C}
    {alpha : MorphismFamily f g} {beta : MorphismFamily g h} {gamma : MorphismFamily f h}
    (given : TrianglePresentation alpha beta gamma) where
    private
      module A = MorphismFamily alpha
      module B = MorphismFamily beta
      module G = MorphismFamily gamma
      module Corners = TriangleCornerFrames C
    triangle : MAP P (Triangles C)
    triangle = Data.fst given
    first : (edge₂ {C = C} ∘ triangle) =₁ A.arrow
    first = Data.fst (Data.snd given)
    second : (edge₀ {C = C} ∘ triangle) =₁ B.arrow
    second = Data.fst (Data.snd (Data.snd given))
    long : (edge₁ {C = C} ∘ triangle) =₁ G.arrow
    long = Data.fst (Data.snd (Data.snd (Data.snd given)))
    middle-compatible : MiddleCorner alpha beta triangle first second
    middle-compatible = Data.fst (Data.snd (Data.snd (Data.snd (Data.snd given))))
    source-compatible : SourceCorner alpha gamma triangle long first
    source-compatible = Data.fst (Data.snd (Data.snd (Data.snd (Data.snd (Data.snd given)))))
    target-compatible : TargetCorner beta gamma triangle long second
    target-compatible = Data.snd (Data.snd (Data.snd (Data.snd (Data.snd (Data.snd given)))))

    short-comparison : ConeIdentification₁ (cone-restrict triangle (triangle-cone C))
      (ComposableFamilies.cone alpha beta)
    short-comparison = record { left = first; right = second; compatible = middle-compatible }
    source-comparison : ConeIdentification₁ (cone-restrict triangle Corners.source-cone)
      (framed-cone ev₀ ev₀ G.arrow A.arrow G.source-frame A.source-frame)
    source-comparison = record { left = long; right = first; compatible = source-compatible }
    target-comparison : ConeIdentification₁ (cone-restrict triangle Corners.target-cone)
      (framed-cone ev₁ ev₁ G.arrow B.arrow G.target-frame B.target-frame)
    target-comparison = record { left = long; right = second; compatible = target-compatible }

  presented-composition : {P C : CAT Γ} {f g h : MAP P C}
    (segal : IsEquiv (short-edges C)) (alpha : MorphismFamily f g)
    (beta : MorphismFamily g h) (gamma : MorphismFamily f h)
    → TrianglePresentation alpha beta gamma
    → MorphismFamilyIdentification One (MC.Composition.compose C segal beta alpha) gamma
  presented-composition {C = C} segal alpha beta gamma given =
    Chosen.comparison gamma T.long Endpoint.compatible
    where
      module T = PresentedTriangle given
      module Endpoint = TriangleEndpointComparison alpha beta gamma T.triangle T.short-comparison
        T.long T.source-compatible T.target-compatible
      module Chosen = CompositionPresentation C segal beta alpha T.triangle Endpoint.Short.identification

private
  module RestrictFramedCorner {Γ : Context} {P Q T A B C : CAT Γ}
    (f : MAP A C) (g : MAP B C) (original : Cone f g T)
    (sigma : MAP P T) (u : MAP P A) (v : MAP P B) {x : MAP P C}
    (a : (f ∘ u) =₁ x) (b : (g ∘ v) =₁ x)
    (given : ConeIdentification₁ (cone-restrict sigma original) (framed-cone f g u v a b))
    (r : MAP Q P) where
    private
      module Frames = FramedConeRestriction f g u v a b r
      original-comparison : ConeIdentification₁ (cone-restrict (sigma ∘ r) original)
        (cone-restrict r (framed-cone f g u v a b))
      original-comparison = cone-compose (cone-identification-restrict-One r given)
        (cone-inverse (cone-restrict-assoc r sigma original))
    comparison : ConeIdentification₁ (cone-restrict (sigma ∘ r) original) Frames.restricted
    comparison = record
      { left = ConeIdentification₁.left original-comparison
      ; right = ConeIdentification₁.right original-comparison
      ; compatible = replace-sides₌ (id₌ (Cone.match (cone-restrict (sigma ∘ r) original)))
          (Frames.matching ⁻¹) (ConeIdentification₁.compatible original-comparison) }

module _ {Γ : Context} where
  module RestrictPresentation {P Q C : CAT Γ} {f g h : MAP P C}
    {alpha : MorphismFamily f g} {beta : MorphismFamily g h} {gamma : MorphismFamily f h}
    (given : TrianglePresentation alpha beta gamma) (r : MAP Q P) where
    private
      module T = PresentedTriangle given
      module A = MorphismFamily alpha
      module B = MorphismFamily beta
      module G = MorphismFamily gamma
      module Corners = TriangleCornerFrames C
      module Middle = RestrictFramedCorner ev₁ ev₀ (triangle-cone C) T.triangle
        A.arrow B.arrow A.target-frame B.source-frame T.short-comparison r
      module Source = RestrictFramedCorner ev₀ ev₀ Corners.source-cone T.triangle
        G.arrow A.arrow G.source-frame A.source-frame T.source-comparison r
      module Target = RestrictFramedCorner ev₁ ev₁ Corners.target-cone T.triangle
        G.arrow B.arrow G.target-frame B.target-frame T.target-comparison r
    value : TrianglePresentation (restrict-family alpha r) (restrict-family beta r) (restrict-family gamma r)
    value = triangle-presentation (T.triangle ∘ r)
      (ConeIdentification₁.left Middle.comparison)
      (ConeIdentification₁.right Middle.comparison)
      (ConeIdentification₁.left Source.comparison)
      (ConeIdentification₁.compatible Middle.comparison)
      (ConeIdentification₁.compatible Source.comparison)
      (ConeIdentification₁.compatible Target.comparison)

  module RetargetPresentation {P C : CAT Γ} {f g h f′ g′ h′ : MAP P C}
    {alpha : MorphismFamily f g} {beta : MorphismFamily g h} {gamma : MorphismFamily f h}
    (given : TrianglePresentation alpha beta gamma) (p : f =₁ f′) (q : g =₁ g′) (r : h =₁ h′) where
    private
      module T = PresentedTriangle given
      module A = MorphismFamily alpha
      module B = MorphismFamily beta
      module G = MorphismFamily gamma
      module Middle = FramedConeEndpointChange ev₁ ev₀ A.arrow B.arrow A.target-frame B.source-frame q
      module Source = FramedConeEndpointChange ev₀ ev₀ G.arrow A.arrow G.source-frame A.source-frame p
      module Target = FramedConeEndpointChange ev₁ ev₁ G.arrow B.arrow G.target-frame B.target-frame r
    value : TrianglePresentation (retarget-family alpha p q) (retarget-family beta q r) (retarget-family gamma p r)
    value = triangle-presentation T.triangle T.first T.second T.long
      (replace-sides₌ (id₌ _) (Middle.matching ⁻¹) T.middle-compatible)
      (replace-sides₌ (id₌ _) (Source.matching ⁻¹) T.source-compatible)
      (replace-sides₌ (id₌ _) (Target.matching ⁻¹) T.target-compatible)
```
