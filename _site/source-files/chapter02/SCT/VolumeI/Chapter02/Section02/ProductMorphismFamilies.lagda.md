# Morphism families in a product

Pairing uses the specified funPair arrow. The product endpoint-frame
construction gives its source and target frames with both projected
equations. Joint identification lifting and evaluation-frame reflection
then recover a complete comparison from its two projected comparisons.

The same two projections identify the actual chosen product composite
with the actual pairing of the chosen component composites. All endpoint
transports and chosen witnesses remain part of the comparison.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.ProductMorphismFamilies where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp₌-assoc)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (cancel-left)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase using (CompatibleOver)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing using (pair₌-extensionality)
open import SCT.VolumeI.Chapter01.Section03.Products.FramedComparisons
  using (lift-paired-identifications; JointIdentificationImages; lift-paired-images;
    product-endpoint-frame; ProductEndpointImages; product-endpoint-images)
open import SCT.VolumeI.Chapter01.Section03.Identifications.EvaluationFrames using (evaluation-route; reflect-evaluation-frame)
```

## Pairing and reflection of framed morphism families

Both projections recover the original framed family after product
endpoint transport. Their joint equivalence recovers the arrow comparison;
evaluation squares recover its two endpoint equations.

```agda
open import SCT.VolumeI.Chapter01.Section07.FunctorProducts using (funPair; funPair-projection₁; funPair-projection₂; module ProductComparison)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPost)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1]; zero; one)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (Ar; evAt; ev₀; ev₁; MorphismFamily; MorphismFamilyIdentification)
open import SCT.VolumeI.Chapter02.Section01.MorphismFunctor using (map-morphism-family; evAt-post)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations using (retarget-family; retarget-family-comparison; family-comparison; module FamilyComparison)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyComparisons using (compose-family-comparisons; inverse-family-comparison)

private
  point-route : {Γ : Context} {P C D : CAT Γ} (a : MAP One ([1] {Γ = Γ}))
    (F : MAP C D) (h : MAP P (Ar C))
    → (evAt a ∘ (funPost {C = [1]} F ∘ h)) =₁ (F ∘ (evAt a ∘ h))
  point-route a F h = evaluation-route F (evAt a) (evAt a) (funPost {C = [1]} F) (evAt-post a F) h

module ProductFamily {Γ : Context} {P C D : CAT Γ}
  {x₁ y₁ : MAP P C} {x₂ y₂ : MAP P D}
  (alpha : MorphismFamily x₁ y₁) (beta : MorphismFamily x₂ y₂) where
  private
    module A = MorphismFamily alpha
    module B = MorphismFamily beta
    h : MAP P (Ar (C × D))
    h = funPair {E = [1]} A.arrow B.arrow
    left : (funPost {C = [1]} pr₁ ∘ h) =₁ A.arrow
    left = funPair-projection₁ {E = [1]} A.arrow B.arrow
    right : (funPost {C = [1]} pr₂ ∘ h) =₁ B.arrow
    right = funPair-projection₂ {E = [1]} A.arrow B.arrow
    source₁ = A.source-frame ∙ (ev₀ ◁ left)
    source₂ = B.source-frame ∙ (ev₀ ◁ right)
    target₁ = A.target-frame ∙ (ev₁ ◁ left)
    target₂ = B.target-frame ∙ (ev₁ ◁ right)
    source-frame = product-endpoint-frame (ev₀ ∘ h) x₁ x₂ (point-route zero pr₁ h) (point-route zero pr₂ h) source₁ source₂
    target-frame = product-endpoint-frame (ev₁ ∘ h) y₁ y₂ (point-route one pr₁ h) (point-route one pr₂ h) target₁ target₂
    source-images = product-endpoint-images (ev₀ ∘ h) x₁ x₂ (point-route zero pr₁ h) (point-route zero pr₂ h) source₁ source₂
    target-images = product-endpoint-images (ev₁ ∘ h) y₁ y₂ (point-route one pr₁ h) (point-route one pr₂ h) target₁ target₂

  value : MorphismFamily (pair x₁ x₂) (pair y₁ y₂)
  value = record { arrow = h ; source-frame = source-frame ; target-frame = target-frame }

  first-projection : MorphismFamilyIdentification One
    (retarget-family (map-morphism-family pr₁ value) (pair-β₁ x₁ x₂) (pair-β₁ y₁ y₂)) alpha
  first-projection = family-comparison _ _ left
    ((ProductEndpointImages.first source-images) ⁻¹) ((ProductEndpointImages.first target-images) ⁻¹)

  second-projection : MorphismFamilyIdentification One
    (retarget-family (map-morphism-family pr₂ value) (pair-β₂ x₁ x₂) (pair-β₂ y₁ y₂)) beta
  second-projection = family-comparison _ _ right
    ((ProductEndpointImages.second source-images) ⁻¹) ((ProductEndpointImages.second target-images) ⁻¹)

module _ {Γ : Context} where
  pair-morphism-family : {P C D : CAT Γ} {x₁ y₁ : MAP P C} {x₂ y₂ : MAP P D}
    → MorphismFamily x₁ y₁ → MorphismFamily x₂ y₂
    → MorphismFamily (pair x₁ x₂) (pair y₁ y₂)
  pair-morphism-family = ProductFamily.value

module ProductReflection {Γ : Context} {P C D : CAT Γ} {x y : MAP P (C × D)}
  (alpha beta : MorphismFamily x y)
  (first : MorphismFamilyIdentification One (map-morphism-family pr₁ alpha) (map-morphism-family pr₁ beta))
  (second : MorphismFamilyIdentification One (map-morphism-family pr₂ alpha) (map-morphism-family pr₂ beta)) where
  private
    module A = MorphismFamily alpha
    module B = MorphismFamily beta
    module L = FamilyComparison first
    module R = FamilyComparison second
    K₁ : MAP (Ar (C × D)) (Ar C)
    K₁ = funPost {C = [1]} pr₁
    K₂ : MAP (Ar (C × D)) (Ar D)
    K₂ = funPost {C = [1]} pr₂
    e : IsEquiv (pair K₁ K₂)
    e = ProductComparison.forward-isEquiv [1] C D

  identification : A.arrow =₁ B.arrow
  identification = lift-paired-identifications K₁ K₂ e A.arrow B.arrow L.identification R.identification

  private
    images : JointIdentificationImages K₁ K₂ L.identification R.identification identification
    images = lift-paired-images K₁ K₂ e A.arrow B.arrow L.identification R.identification
    first-image : (K₁ ◁ identification) =₂ L.identification
    first-image = JointIdentificationImages.first images
    second-image : (K₂ ◁ identification) =₂ R.identification
    second-image = JointIdentificationImages.second images

    endpoint : (a : MAP One ([1] {Γ = Γ})) {z : MAP P (C × D)}
      (p : (evAt a ∘ A.arrow) =₁ z) (q : (evAt a ∘ B.arrow) =₁ z)
      → (((pr₁ ◁ q) ∙ point-route a pr₁ B.arrow) ∙ (evAt a ◁ L.identification)) =₂
          ((pr₁ ◁ p) ∙ point-route a pr₁ A.arrow)
      → (((pr₂ ◁ q) ∙ point-route a pr₂ B.arrow) ∙ (evAt a ◁ R.identification)) =₂
          ((pr₂ ◁ p) ∙ point-route a pr₂ A.arrow)
      → CompatibleOver (evAt a) p q identification
    endpoint a p q left-square right-square = pair₌-extensionality
      (reflect-evaluation-frame pr₁ (evAt a) (evAt a) K₁ (evAt-post a pr₁)
        p q identification L.identification first-image left-square)
      (reflect-evaluation-frame pr₂ (evAt a) (evAt a) K₂ (evAt-post a pr₂)
        p q identification R.identification second-image right-square)

  comparison : MorphismFamilyIdentification One alpha beta
  comparison = family-comparison alpha beta identification
    (endpoint zero A.source-frame B.source-frame L.source R.source)
    (endpoint one A.target-frame B.target-frame L.target R.target)

module _ {Γ : Context} where
  product-family-reflect : {P C D : CAT Γ} {x y : MAP P (C × D)}
    {alpha beta : MorphismFamily x y}
    → MorphismFamilyIdentification One (map-morphism-family pr₁ alpha) (map-morphism-family pr₁ beta)
    → MorphismFamilyIdentification One (map-morphism-family pr₂ alpha) (map-morphism-family pr₂ beta)
    → MorphismFamilyIdentification One alpha beta
  product-family-reflect {alpha = alpha} {beta} = ProductReflection.comparison alpha beta
```

## Composition in a product

Apply functor preservation to each projection. After transport along the
three product endpoint triangles, congruence replaces the projected inputs
by the original component families. The long-edge projection comparison
then identifies this result with the projection of the paired component
composites. Joint reflection gives the comparison of the actual chosen
composite with the actual paired composite, with both endpoint equations.

```agda
open import SCT.VolumeI.Chapter02.Section01.Triangles using (short-edges)
open import SCT.VolumeI.Chapter02.Section02.MorphismCompositionPostcomposition using (module FunctorComposition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCompositionTransport using (module CompositionTransport)
open import SCT.VolumeI.Chapter02.Section02.MorphismCompositionComparisons using (module CompositionComparisons)
import SCT.VolumeI.Chapter02.Section02.MorphismComposition as MC

private
  module _ {Γ : Context} where
    retarget-reflect : {P C : CAT Γ} {x y x′ y′ : MAP P C}
      {alpha beta : MorphismFamily x y} (p : x =₁ x′) (q : y =₁ y′)
      → MorphismFamilyIdentification One (retarget-family alpha p q) (retarget-family beta p q)
      → MorphismFamilyIdentification One alpha beta
    retarget-reflect {alpha = alpha} {beta} p q given = family-comparison alpha beta Q.identification
      (cancel-left p (Q.source ∙ (comp₌-assoc p (MorphismFamily.source-frame beta) (ev₀ ◁ Q.identification)) ⁻¹))
      (cancel-left q (Q.target ∙ (comp₌-assoc q (MorphismFamily.target-frame beta) (ev₁ ◁ Q.identification)) ⁻¹))
      where module Q = FamilyComparison given

module _ {Γ : Context} where
  abstract
    projected-composition : {P U E : CAT Γ} (F : MAP U E)
      (source-segal : IsEquiv (short-edges U)) (target-segal : IsEquiv (short-edges E))
      {x₀ y₀ z₀ : MAP P U} {x y z : MAP P E}
      (A : MorphismFamily x₀ y₀) (B : MorphismFamily y₀ z₀) (H : MorphismFamily x₀ z₀)
      (p : (F ∘ x₀) =₁ x) (q : (F ∘ y₀) =₁ y) (r : (F ∘ z₀) =₁ z)
      (a : MorphismFamily x y) (b : MorphismFamily y z)
      (first : MorphismFamilyIdentification One (retarget-family (map-morphism-family F A) p q) a)
      (second : MorphismFamilyIdentification One (retarget-family (map-morphism-family F B) q r) b)
      (long : MorphismFamilyIdentification One (retarget-family (map-morphism-family F H) p r)
        (MC.Composition.compose E target-segal b a))
      → MorphismFamilyIdentification One
          (map-morphism-family F (MC.Composition.compose U source-segal B A)) (map-morphism-family F H)
    projected-composition {E = E} F source-segal target-segal A B H p q r a b first second long =
      retarget-reflect p r
        (compose-family-comparisons (inverse-family-comparison long)
          (compose-family-comparisons (CompositionComparisons.composition-comparison E target-segal second first)
            (compose-family-comparisons
              (CompositionTransport.retarget-composition E target-segal
                (map-morphism-family F B) (map-morphism-family F A) p q r)
              (retarget-family-comparison p r
                (FunctorComposition.preserves-composition F source-segal target-segal B A)))))
```

## The actual two composites and their projections

The actual chosen product composite and the actual paired component
composites are named once as fully framed families. Each projection theorem
applies the generic projected-composition argument to these fixed values
and its three original framed projection comparisons.

```agda
module ProductComposition {Γ : Context} (C D : CAT Γ)
  (product-segal : IsEquiv (short-edges (C × D)))
  (left-segal : IsEquiv (short-edges C)) (right-segal : IsEquiv (short-edges D)) where
  private
    module Joint = MC.Composition (C × D) product-segal
    module Left = MC.Composition C left-segal
    module Right = MC.Composition D right-segal

  module _ {P : CAT Γ} {x₁ y₁ z₁ : MAP P C} {x₂ y₂ z₂ : MAP P D}
    (beta₁ : MorphismFamily y₁ z₁) (alpha₁ : MorphismFamily x₁ y₁)
    (beta₂ : MorphismFamily y₂ z₂) (alpha₂ : MorphismFamily x₂ y₂) where

    first-input : MorphismFamily (pair x₁ x₂) (pair y₁ y₂)
    first-input = pair-morphism-family alpha₁ alpha₂
    second-input : MorphismFamily (pair y₁ y₂) (pair z₁ z₂)
    second-input = pair-morphism-family beta₁ beta₂
    left-composite : MorphismFamily x₁ z₁
    left-composite = Left.compose beta₁ alpha₁
    right-composite : MorphismFamily x₂ z₂
    right-composite = Right.compose beta₂ alpha₂

    chosen-product-composite : MorphismFamily (pair x₁ x₂) (pair z₁ z₂)
    chosen-product-composite = Joint.compose second-input first-input
    paired-component-composite : MorphismFamily (pair x₁ x₂) (pair z₁ z₂)
    paired-component-composite = pair-morphism-family left-composite right-composite

    private
      abstract
        first-input-image : MorphismFamilyIdentification One
          (retarget-family (map-morphism-family pr₁ first-input) (pair-β₁ x₁ x₂) (pair-β₁ y₁ y₂)) alpha₁
        first-input-image = ProductFamily.first-projection alpha₁ alpha₂

        second-input-image : MorphismFamilyIdentification One
          (retarget-family (map-morphism-family pr₁ second-input) (pair-β₁ y₁ y₂) (pair-β₁ z₁ z₂)) beta₁
        second-input-image = ProductFamily.first-projection beta₁ beta₂

        long-image : MorphismFamilyIdentification One
          (retarget-family (map-morphism-family pr₁ paired-component-composite) (pair-β₁ x₁ x₂) (pair-β₁ z₁ z₂))
          left-composite
        long-image = ProductFamily.first-projection left-composite right-composite

        first-input-image₂ : MorphismFamilyIdentification One
          (retarget-family (map-morphism-family pr₂ first-input) (pair-β₂ x₁ x₂) (pair-β₂ y₁ y₂)) alpha₂
        first-input-image₂ = ProductFamily.second-projection alpha₁ alpha₂

        second-input-image₂ : MorphismFamilyIdentification One
          (retarget-family (map-morphism-family pr₂ second-input) (pair-β₂ y₁ y₂) (pair-β₂ z₁ z₂)) beta₂
        second-input-image₂ = ProductFamily.second-projection beta₁ beta₂

        long-image₂ : MorphismFamilyIdentification One
          (retarget-family (map-morphism-family pr₂ paired-component-composite) (pair-β₂ x₁ x₂) (pair-β₂ z₁ z₂))
          right-composite
        long-image₂ = ProductFamily.second-projection left-composite right-composite

    abstract
      first-projected-product-composition : MorphismFamilyIdentification One
        (map-morphism-family pr₁ chosen-product-composite) (map-morphism-family pr₁ paired-component-composite)
      first-projected-product-composition =
        projected-composition {P = P} {U = C × D} {E = C} pr₁ product-segal left-segal
          first-input second-input paired-component-composite
          (pair-β₁ x₁ x₂) (pair-β₁ y₁ y₂) (pair-β₁ z₁ z₂)
          alpha₁ beta₁ first-input-image second-input-image long-image

      second-projected-product-composition : MorphismFamilyIdentification One
        (map-morphism-family pr₂ chosen-product-composite) (map-morphism-family pr₂ paired-component-composite)
      second-projected-product-composition =
        projected-composition {P = P} {U = C × D} {E = D} pr₂ product-segal right-segal
          first-input second-input paired-component-composite
          (pair-β₂ x₁ x₂) (pair-β₂ y₁ y₂) (pair-β₂ z₁ z₂)
          alpha₂ beta₂ first-input-image₂ second-input-image₂ long-image₂
```

## Full product composition with explicit families

Reflection receives the same two named actual families explicitly and the
two proved concrete projected comparisons. Each comparison retains the
original coordinate projection witnesses and both endpoint laws.

```agda
    product-composition : MorphismFamilyIdentification One chosen-product-composite paired-component-composite
    product-composition = product-family-reflect
      {alpha = chosen-product-composite} {beta = paired-component-composite}
      first-projected-product-composition
      second-projected-product-composition
```

