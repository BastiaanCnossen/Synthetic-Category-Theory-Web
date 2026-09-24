# The universal degenerate triangle

We use the universal arrow on `Ar C` and the actual identity expression.
The three edge comparisons are lifted directly from evaluation diagrams.
Their uncurried and evaluated images are retained. `DirectUnitEndpoints`
normalizes these images, and `DirectUnitPresentations` proves the three
vertex equations and the endpoint-preserving universal unit comparisons.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.DirectUnitTriangles
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.DegenerateCocones 𝒯 M ℱ P I E public
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯 using (productRestriction-comp)
open import SCT.VolumeI.Chapter01.Section07.IsomorphismLifting 𝒯 M ℱ
  using (funIsoReflect; funIsoReflect-β)

open import SCT.VolumeI.Chapter02.Section01.EndpointNaturality 𝒯 M ℱ using (module Evaluation)
import SCT.VolumeI.Chapter02.Section02.UniversalArrowEvaluation as UniversalEvaluation
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

-- The prescribed uncurried image also prescribes the evaluated image.
module ReflectedEndpoint {Γ A C : CAT} (x : Obj-abs A)
  (h k : MAP Γ (Fun A C)) {H : MAP (Γ × A) C}
  (β : (funUncurry k) =₁ H) (θ : (funUncurry h) =₁ H)
  (δ : h =₁ k) (image : (funUncurryIso δ) =₂ (β ⁻¹ ∙ θ)) where
  i = insert {X = Γ} x

  abstract
    raw-endpoint : ((β ▷ i) ∙ (funUncurryIso δ ▷ i)) =₂ (θ ▷ i)
    raw-endpoint = (preWhisker i ◁
      (cancel-inverse β θ ∙ isoComp-cong (idIso β) image)) ∙
      (preWhisker-isoComp-at β (funUncurryIso δ) i) ⁻¹

    endpoint : (((β ▷ i) ∙ evaluate-uncurry x k) ∙ (evaluate x ◁ δ)) =₂
      ((θ ▷ i) ∙ evaluate-uncurry x h)
    endpoint = isoComp-cong raw-endpoint (idIso (evaluate-uncurry x h)) ∙
      ((isoComp-assoc-at (β ▷ i) (funUncurryIso δ ▷ i) (evaluate-uncurry x h)) ⁻¹ ∙
      (isoComp-cong (idIso (β ▷ i)) (Evaluation.natural x δ) ∙
        isoComp-assoc-at (β ▷ i) (evaluate-uncurry x k) (evaluate x ◁ δ)))

module Universal (C : CAT) where
  X = Ar C

  arrow : MorphismExpression (ev₀ {C}) ev₁
  arrow = record
    { arrow = id X
    ; source-frame = comp-unitʳ ev₀
    ; target-frame = comp-unitʳ ev₁ }

  -- A constant restriction evaluates the universal arrow at its endpoint.
  constant-insertion : (x : Obj-abs [1]) →
    (productMap (id X) (const x)) =₁ (insert x ∘ pr₁)
  constant-insertion x = (pair-pre (id X) (const x) pr₁) ⁻¹ ∙
    pair-cong (idIso (id X ∘ pr₁))
      ((comp-assoc pr₁ (terminate X) x) ⁻¹ ∙
        ((x ◁ terminal-iso (terminate [1] ∘ pr₂) (terminate X ∘ pr₁)) ∙
          comp-assoc pr₂ (terminate [1]) x))

  constant-evaluation : (x : Obj-abs [1]) →
    (funEval ∘ productMap (id X) (const x)) =₁ (evaluate x ∘ pr₁)
  constant-evaluation x = (comp-assoc pr₁ (insert x) funEval) ⁻¹ ∙
    (funEval ◁ constant-insertion x)

  identity-evaluation : (funEval ∘ productMap (id X) (id [1])) =₁ funEval
  identity-evaluation = comp-unitʳ funEval ∙ (funEval ◁ productMap-id X [1])

  module Degeneracy (s : MAP [2] [1]) where
    triangle : MAP X (Fun [2] C)
    triangle = funPre s

    edge-image : (d : MAP [1] [2]) →
      (funUncurry (funPre d ∘ triangle)) =₁
        (funEval ∘ productMap (id X) (s ∘ d))
    edge-image d = (funEval ◁ productRestriction-comp X d s) ∙
      (comp-assoc (productMap (id X) d) (productMap (id X) s) funEval ∙
        ((funPre-β s ▷ productMap (id X) d) ∙ funPre-uncurry d triangle))

    module IdentityEdge (d : MAP [1] [2]) (α : (s ∘ d) =₁ (id [1])) where
      diagram-image : (funUncurry (funPre d ∘ triangle)) =₁ funEval
      diagram-image = identity-evaluation ∙
        ((funEval ◁ productMap-cong (idIso (id X)) α) ∙ edge-image d)

      raw : (funUncurry (funPre d ∘ triangle)) =₁ (funUncurry (id X))
      raw = (funUncurry-id [1] C) ⁻¹ ∙ diagram-image

      comparison : (funPre d ∘ triangle) =₁ (id X)
      comparison = funIsoReflect _ _ raw

      retained-image : (funUncurryIso comparison) =₂ raw
      retained-image = funIsoReflect-β _ _ raw

      abstract
        endpoint : (x : Obj-abs [1]) →
          (comp-unitʳ (evaluate {C = C} x) ∙ (evaluate x ◁ comparison)) =₂
          ((diagram-image ▷ insert x) ∙ evaluate-uncurry x (funPre d ∘ triangle))
        endpoint x = ReflectedEndpoint.endpoint x (funPre d ∘ triangle) (id X)
          (funUncurry-id [1] C) diagram-image comparison retained-image ∙
          isoComp-cong ((UniversalEvaluation.Universal.endpoint 𝒯 M ℱ {C = C} x) ⁻¹)
            (idIso (evaluate x ◁ comparison))

    module ConstantEdge (d : MAP [1] [2]) (x : Obj-abs [1])
      (α : (s ∘ d) =₁ (const x)) where
      diagram-image : (funUncurry (funPre d ∘ triangle)) =₁ (evaluate x ∘ pr₁)
      diagram-image = constant-evaluation x ∙
        ((funEval ◁ productMap-cong (idIso (id X)) α) ∙ edge-image d)

      raw : (funUncurry (funPre d ∘ triangle)) =₁
        (funUncurry (MorphismExpression.arrow (identity-expression (evaluate x))))
      raw = (funCurry-β (evaluate x ∘ pr₁)) ⁻¹ ∙ diagram-image

      comparison : (funPre d ∘ triangle) =₁
        (MorphismExpression.arrow (identity-expression (evaluate x)))
      comparison = funIsoReflect _ _ raw

      retained-image : (funUncurryIso comparison) =₂ raw
      retained-image = funIsoReflect-β _ _ raw

      abstract
        endpoint : (y : Obj-abs [1]) →
          (evaluate-curry y (evaluate x ∘ pr₁) ∙ (evaluate y ◁ comparison)) =₂
          ((diagram-image ▷ insert y) ∙ evaluate-uncurry y (funPre d ∘ triangle))
        endpoint y = ReflectedEndpoint.endpoint y (funPre d ∘ triangle)
          (MorphismExpression.arrow (identity-expression (evaluate x)))
          (funCurry-β (evaluate x ∘ pr₁)) diagram-image comparison retained-image

        source-image :
          (MorphismExpression.source-frame (identity-expression (evaluate x)) ∙
            (ev₀ ◁ comparison)) =₂
          (identity-boundary zero (evaluate x) ∙
            ((diagram-image ▷ insert zero) ∙ evaluate-uncurry zero (funPre d ∘ triangle)))
        source-image = isoComp-cong (idIso (identity-boundary zero (evaluate x))) (endpoint zero) ∙
          isoComp-assoc-at (identity-boundary zero (evaluate x))
            (evaluate-curry zero (evaluate x ∘ pr₁)) (ev₀ ◁ comparison)

        target-image :
          (MorphismExpression.target-frame (identity-expression (evaluate x)) ∙
            (ev₁ ◁ comparison)) =₂
          (identity-boundary one (evaluate x) ∙
            ((diagram-image ▷ insert one) ∙ evaluate-uncurry one (funPre d ∘ triangle)))
        target-image = isoComp-cong (idIso (identity-boundary one (evaluate x))) (endpoint one) ∙
          isoComp-assoc-at (identity-boundary one (evaluate x))
            (evaluate-curry one (evaluate x ∘ pr₁)) (ev₁ ◁ comparison)

  module Left where
    module Triangle = Degeneracy s₀
    module First = Triangle.ConstantEdge d₂ zero s₀-d₂
    module Second = Triangle.IdentityEdge d₀ s₀-d₀
    module Long = Triangle.IdentityEdge d₁ s₀-d₁

  module Right where
    module Triangle = Degeneracy s₁
    module First = Triangle.IdentityEdge d₂ s₁-d₂
    module Second = Triangle.ConstantEdge d₀ one s₁-d₀
    module Long = Triangle.IdentityEdge d₁ s₁-d₁
```
