# Invertible families and the actual isomorphism category

A lift of a morphism family to the specified isomorphism category is a
factorization through `isoArrow`, including its arrow comparison. The two
original inverse triangles give left and right inverse families with
their full endpoint laws. Conversely, inverse families present two
triangles whose original short and long edges factor through the two
pullbacks defining Iso.

These constructions use the supplied Segal equivalence explicitly. They
do not require associativity, the isomorphism embedding or Rezk.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section03.InvertibleMorphismFamilies where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (restrict-triangle; post-triangle)
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors using (functor-over)
import SCT.VolumeI.Chapter01.Section03.Factorizations as Fact
open import SCT.VolumeI.Chapter01.Section06.Cones using (Cone; ConeIdentification₁; cone-restrict)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks using (pullback-cone; pullback-factor; pullback-factor-β)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; identityArrow; identity-family; MorphismFamily; MorphismFamilyIdentification)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyComparisons
  using (compose-family-comparisons; inverse-family-comparison; id-family-comparison)
open import SCT.VolumeI.Chapter02.Section01.Triangles using (Triangles; short-edges; edge₀; edge₁; edge₂)
open import SCT.VolumeI.Chapter02.Section02.TriangleCompletionPresentation using (module CompletePair)
open import SCT.VolumeI.Chapter02.Section02.TrianglePresentationChange using (module ReplacePresentation)
open import SCT.VolumeI.Chapter02.Section02.FramedTrianglePresentations using (TrianglePresentation; module PresentedTriangle)
open import SCT.VolumeI.Chapter02.Section03.Isomorphisms
  using (Iso; InverseTriangles; firstInverseTriangle; secondInverseTriangle;
    inverseLongEdges; inverseIdentityEdges; isoArrow; isoTriangles; isoObjects)
open import SCT.VolumeI.Chapter02.Section03.InverseMorphismFamilies
  using (InverseFamily; constant-family; module ConstantIdentity; module UniversalIsoFamily;
    module RightInverseTriangle; module LeftInverseTriangle)

module _ {Γ : Context} {P C : CAT Γ} where
  IsoLift : MAP P (Ar C) → Set m
  IsoLift h = Fact.Factorization (isoArrow C) h

module FromInverseFamily {Γ : Context} {P C : CAT Γ} {x y : MAP P C}
  (segal : IsEquiv (short-edges C)) (f : MorphismFamily x y) (given : InverseFamily segal f) where
  private
    module F = MorphismFamily f
    module W = InverseFamily given
    module RightCompletion = CompletePair segal W.right-inverse f using (long-family; presentation; composite)
    module LeftCompletion = CompletePair segal f W.left-inverse using (long-family; presentation; composite)
    right-long : MorphismFamilyIdentification One RightCompletion.long-family (constant-family y)
    right-long = compose-family-comparisons (inverse-family-comparison (ConstantIdentity.value y))
      (compose-family-comparisons W.right-law (inverse-family-comparison RightCompletion.composite))
    left-long : MorphismFamilyIdentification One LeftCompletion.long-family (constant-family x)
    left-long = compose-family-comparisons (inverse-family-comparison (ConstantIdentity.value x))
      (compose-family-comparisons W.left-law (inverse-family-comparison LeftCompletion.composite))

  right-presentation : TrianglePresentation W.right-inverse f (constant-family y)
  right-presentation = ReplacePresentation.value RightCompletion.presentation
    (id-family-comparison W.right-inverse) (id-family-comparison f) right-long
  left-presentation : TrianglePresentation f W.left-inverse (constant-family x)
  left-presentation = ReplacePresentation.value LeftCompletion.presentation
    (id-family-comparison f) (id-family-comparison W.left-inverse) left-long

  private
    module Right = PresentedTriangle right-presentation using (triangle; first; second; long)
    module Left = PresentedTriangle left-presentation using (triangle; first; second; long)
    p₁ : MAP (InverseTriangles C) (Triangles C)
    p₁ = firstInverseTriangle C
    p₂ : MAP (InverseTriangles C) (Triangles C)
    p₂ = secondInverseTriangle C
    inner-cone : Cone (edge₀ {C = C}) edge₂ P
    inner-cone = record
      { left = Right.triangle; right = Left.triangle; match = Left.first ⁻¹ ∙ Right.second }
    triangles : MAP P (InverseTriangles C)
    triangles = pullback-factor inner-cone
    inner-image : ConeIdentification₁
      (cone-restrict triangles (pullback-cone (edge₀ {C = C}) edge₂)) inner-cone
    inner-image = pullback-factor-β inner-cone
    objects : MAP P (C × C)
    objects = pair x y
    first-long : ((edge₁ ∘ p₁) ∘ triangles) =₁ (identityArrow ∘ y)
    first-long = Right.long ∙
      ((edge₁ ◁ ConeIdentification₁.left inner-image) ∙ comp-assoc triangles p₁ edge₁)
    second-long : ((edge₁ ∘ p₂) ∘ triangles) =₁ (identityArrow ∘ x)
    second-long = Left.long ∙
      ((edge₁ ◁ ConeIdentification₁.right inner-image) ∙ comp-assoc triangles p₂ edge₁)
    long-pair : (inverseLongEdges C ∘ triangles) =₁ pair (identityArrow ∘ y) (identityArrow ∘ x)
    long-pair = pair⁼ first-long second-long ∙ pair-pre (edge₁ ∘ p₁) (edge₁ ∘ p₂) triangles
    identity-pair : (inverseIdentityEdges C ∘ objects) =₁ pair (identityArrow ∘ y) (identityArrow ∘ x)
    identity-pair = pair⁼
      (post-triangle identityArrow pr₂ objects (pair-β₂ x y))
      (post-triangle identityArrow pr₁ objects (pair-β₁ x y)) ∙
      pair-pre (identityArrow ∘ pr₂) (identityArrow ∘ pr₁) objects
    outer-cone : Cone (inverseLongEdges C) (inverseIdentityEdges C) P
    outer-cone = record { left = triangles; right = objects; match = identity-pair ⁻¹ ∙ long-pair }
    lift : MAP P (Iso C)
    lift = pullback-factor outer-cone
    outer-image : ConeIdentification₁
      (cone-restrict lift (pullback-cone (inverseLongEdges C) (inverseIdentityEdges C))) outer-cone
    outer-image = pullback-factor-β outer-cone

  arrow-comparison : (isoArrow C ∘ lift) =₁ F.arrow
  arrow-comparison = Right.second ∙
    ((edge₀ ◁ ConeIdentification₁.left inner-image) ∙
      (comp-assoc triangles p₁ edge₀ ∙
        (((edge₀ ∘ p₁) ◁ ConeIdentification₁.left outer-image) ∙
          comp-assoc lift (isoTriangles C) (edge₀ ∘ p₁))))
  value : IsoLift F.arrow
  value = functor-over lift arrow-comparison
```

For the converse, restrict the two original Iso triangles along the lift
and compose their original short-edge comparisons with its specified
arrow comparison. The native inverse-triangle constructors then supply
both endpoint frames and composition laws for the given family directly.

```agda
module FromLift {Γ : Context} {P C : CAT Γ} {x y : MAP P C}
  (segal : IsEquiv (short-edges C)) (f : MorphismFamily x y) (given : IsoLift (MorphismFamily.arrow f)) where
  private
    module U = UniversalIsoFamily C
      using (right-triangle; left-triangle; right-short; left-short; right-long; left-long)
    h : MAP P (Iso C)
    h = Fact.factor given
    comparison : (isoArrow C ∘ h) =₁ MorphismFamily.arrow f
    comparison = Fact.triangle given
    right-triangle left-triangle : MAP P (Triangles C)
    right-triangle = U.right-triangle ∘ h
    left-triangle = U.left-triangle ∘ h
    right-short : (edge₀ ∘ right-triangle) =₁ MorphismFamily.arrow f
    right-short = comparison ∙ restrict-triangle edge₀ U.right-triangle U.right-short h
    left-short : (edge₂ ∘ left-triangle) =₁ MorphismFamily.arrow f
    left-short = comparison ∙ restrict-triangle edge₂ U.left-triangle U.left-short h
    right-object left-object : MAP P C
    right-object = (pr₂ ∘ isoObjects C) ∘ h
    left-object = (pr₁ ∘ isoObjects C) ∘ h
    right-long : (edge₁ ∘ right-triangle) =₁ (identityArrow ∘ right-object)
    right-long = comp-assoc h (pr₂ ∘ isoObjects C) identityArrow ∙
      restrict-triangle edge₁ U.right-triangle U.right-long h
    left-long : (edge₁ ∘ left-triangle) =₁ (identityArrow ∘ left-object)
    left-long = comp-assoc h (pr₁ ∘ isoObjects C) identityArrow ∙
      restrict-triangle edge₁ U.left-triangle U.left-long h
    module Right = RightInverseTriangle {z = right-object} f right-triangle right-short right-long
      using (inverse; law)
    module Left = LeftInverseTriangle {z = left-object} f left-triangle left-short left-long
      using (inverse; law)
  value : InverseFamily segal f
  value = record
    { left-inverse = Left.inverse; right-inverse = Right.inverse
    ; left-law = Left.law segal; right-law = Right.law segal }

module _ {Γ : Context} {P C : CAT Γ} {x y : MAP P C} where
  inverse-family-lift : (segal : IsEquiv (short-edges C)) (f : MorphismFamily x y) →
    InverseFamily segal f → IsoLift (MorphismFamily.arrow f)
  inverse-family-lift = FromInverseFamily.value
  lift-inverse-family : (segal : IsEquiv (short-edges C)) (f : MorphismFamily x y) →
    IsoLift (MorphismFamily.arrow f) → InverseFamily segal f
  lift-inverse-family = FromLift.value
```
