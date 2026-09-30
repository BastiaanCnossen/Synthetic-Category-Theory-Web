# Presenting transformations by framed diagrams

A diagram presentation records an uncurried diagram and its specified
endpoint identifications, together with their compatibility with an
expression. The operations below retain this information while replacing
diagrams. This packages the comparisons used in currying calculations.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionDiagramPresentations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
  using (expressionIso-compose)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.DiagramExpressionIdentifications as Diagrams
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurriedPostcompositionComparisons as Post
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurriedProductExpressions as Products
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurriedRestrictionExpressions as Restriction
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions 𝒯 M ℱ I using (pair-expression)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PC
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (pair-pre-natural-inputs; cancel-right)
open PC vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-comp; pair-cong-Iso₂)
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open Structural vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at)

record Presentation {Γ C : CAT} {f g : MAP Γ C} (α : MorphismExpression f g) : Set m where
  private module A = MorphismExpression α
  field
    diagram : MAP (Γ × [1]) C
    source-frame : (diagram ∘ insert zero) =₁ f
    target-frame : (diagram ∘ insert one) =₁ g
    comparison : funUncurry A.arrow =₁ diagram
    source-compatible : (source-frame ∙ (comparison ▷ insert zero)) =₂
      (A.source-frame ∙ (evaluate-uncurry zero A.arrow) ⁻¹)
    target-compatible : (target-frame ∙ (comparison ▷ insert one)) =₂
      (A.target-frame ∙ (evaluate-uncurry one A.arrow) ⁻¹)

module Recovery {Γ C : CAT} {f g : MAP Γ C} {α : MorphismExpression f g} (W : Presentation α) where
  module W = Presentation W
  module A = Diagrams.Recovery 𝒯 M ℱ P I E α
  value : ExpressionIso α (expression W.diagram W.source-frame W.target-frame)
  value = expressionIso-compose
    (Diagrams.At.comparison 𝒯 M ℱ P I E A.H W.diagram W.comparison A.p A.q
      W.source-frame W.target-frame W.source-compatible W.target-compatible)
    A.comparison

module Postcompose {Γ C D : CAT} {f g : MAP Γ C} {α : MorphismExpression f g}
  (F : MAP C D) (W : Presentation α) where
  module A = MorphismExpression α
  module W = Presentation W
  H = funUncurry A.arrow
  K = W.diagram
  δ = W.comparison
  β = funPost-uncurry F A.arrow
  comparison : funUncurry (MorphismExpression.arrow (post-expression F α)) =₁ (F ∘ K)
  comparison = (F ◁ δ) ∙ β

  module Endpoint (z : Obj-abs [1]) {h : MAP Γ C}
    (p : (evaluate z ∘ A.arrow) =₁ h) (q : (K ∘ insert z) =₁ h)
    (same : (q ∙ (δ ▷ insert z)) =₂ (p ∙ (evaluate-uncurry z A.arrow) ⁻¹)) where
    i = insert {X = Γ} z
    front = p ∙ (evaluate-uncurry z A.arrow) ⁻¹
    frame : ((F ∘ K) ∘ i) =₁ (F ∘ h)
    frame = (F ◁ q) ∙ comp-assoc i K F

    abstract
      first : (frame ∙ ((F ◁ δ) ▷ i)) =₂ ((F ◁ front) ∙ comp-assoc i H F)
      first = isoComp-cong
          ((postWhisker F ◁ same) ∙ (postWhisker-isoComp-at F q (δ ▷ i)) ⁻¹)
          (idIso (comp-assoc i H F)) ∙
        (isoComp-assoc-at (F ◁ q) (F ◁ (δ ▷ i)) (comp-assoc i H F)) ⁻¹ ∙
        isoComp-cong (idIso (F ◁ q)) (whisker-mixed-at δ i F) ∙
        isoComp-assoc-at (F ◁ q) (comp-assoc i K F) ((F ◁ δ) ▷ i)

      compatible : (frame ∙ (comparison ▷ i)) =₂
        (post-boundary z F A.arrow p ∙ (evaluate-uncurry z (funPost F ∘ A.arrow)) ⁻¹)
      compatible = (Post.post-diagram-frame 𝒯 M ℱ P I E F z A.arrow p) ⁻¹ ∙
        isoComp-assoc-at (F ◁ front) (comp-assoc i H F) (β ▷ i) ∙
        isoComp-cong first (idIso (β ▷ i)) ∙
        (isoComp-assoc-at frame ((F ◁ δ) ▷ i) (β ▷ i)) ⁻¹ ∙
        isoComp-cong (idIso frame) (preWhisker-isoComp-at (F ◁ δ) β i)

  value : Presentation (post-expression F α)
  value = record
    { diagram = F ∘ K
    ; source-frame = Endpoint.frame zero A.source-frame W.source-frame W.source-compatible
    ; target-frame = Endpoint.frame one A.target-frame W.target-frame W.target-compatible
    ; comparison = comparison
    ; source-compatible = Endpoint.compatible zero A.source-frame W.source-frame W.source-compatible
    ; target-compatible = Endpoint.compatible one A.target-frame W.target-frame W.target-compatible }
```

Pairing arbitrary presentations uses naturality of product pairing before
applying the checked endpoint equations. Identity and restricted
expressions use their literal constant and restricted diagrams.

```agda
module Pairing {Γ C D : CAT} {f g : MAP Γ C} {h k : MAP Γ D}
  {α : MorphismExpression f g} {β : MorphismExpression h k}
  (A : Presentation α) (B : Presentation β) where
  module A = Presentation A
  module B = Presentation B
  module Product = Products.At 𝒯 M ℱ P I E α β
  comparison = pair-cong A.comparison B.comparison ∙ Product.comparison

  module Endpoint (z : Obj-abs [1]) {x : MAP Γ C} {y : MAP Γ D}
    (p : (A.diagram ∘ insert z) =₁ x) (q : (B.diagram ∘ insert z) =₁ y)
    (p₀ : (Product.H ∘ insert z) =₁ x) (q₀ : (Product.K ∘ insert z) =₁ y)
    (a₀ : (p ∙ (A.comparison ▷ insert z)) =₂ p₀)
    (b₀ : (q ∙ (B.comparison ▷ insert z)) =₂ q₀) where
    i = insert {X = Γ} z
    old = pair-cong p₀ q₀ ∙ pair-pre Product.H Product.K i
    frame = pair-cong p q ∙ pair-pre A.diagram B.diagram i
    abstract
      compatible : (frame ∙ (pair-cong A.comparison B.comparison ▷ i)) =₂ old
      compatible = isoComp-cong (pair-cong-Iso₂ a₀ b₀) (idIso (pair-pre Product.H Product.K i)) ∙
        isoComp-cong ((pair-cong-comp p (A.comparison ▷ i) q (B.comparison ▷ i)) ⁻¹)
          (idIso (pair-pre Product.H Product.K i)) ∙
        (isoComp-assoc-at (pair-cong p q) (pair-cong (A.comparison ▷ i) (B.comparison ▷ i))
          (pair-pre Product.H Product.K i)) ⁻¹ ∙
        isoComp-cong (idIso (pair-cong p q)) ((pair-pre-natural-inputs A.comparison B.comparison i) ⁻¹) ∙
        isoComp-assoc-at (pair-cong p q) (pair-pre A.diagram B.diagram i)
          (pair-cong A.comparison B.comparison ▷ i)

  module Source = Endpoint zero A.source-frame B.source-frame
    Product.Source.frontF Product.Source.frontG A.source-compatible B.source-compatible
  module Target = Endpoint one A.target-frame B.target-frame
    Product.Target.frontF Product.Target.frontG A.target-compatible B.target-compatible

  endpoint : (z : Obj-abs [1]) {v : MAP Γ (C × D)}
    (p : (pair A.diagram B.diagram ∘ insert z) =₁ v)
    (q : (pair Product.H Product.K ∘ insert z) =₁ v)
    (r : (Product.original ∘ insert z) =₁ v) →
    (p ∙ (pair-cong A.comparison B.comparison ▷ insert z)) =₂ q →
    (q ∙ (Product.comparison ▷ insert z)) =₂ r →
    (p ∙ (comparison ▷ insert z)) =₂ r
  endpoint z p q r left right = right ∙ isoComp-cong left (idIso (Product.comparison ▷ insert z)) ∙
    (isoComp-assoc-at p (pair-cong A.comparison B.comparison ▷ insert z) (Product.comparison ▷ insert z)) ⁻¹ ∙
    isoComp-cong (idIso p) (preWhisker-isoComp-at (pair-cong A.comparison B.comparison) Product.comparison (insert z))

  value : Presentation (pair-expression α β)
  value = record
    { diagram = pair A.diagram B.diagram
    ; source-frame = Source.frame
    ; target-frame = Target.frame
    ; comparison = comparison
    ; source-compatible = endpoint zero Source.frame Product.Source.frame Product.Source.front
        Source.compatible Product.Source.compatible
    ; target-compatible = endpoint one Target.frame Product.Target.frame Product.Target.front
        Target.compatible Product.Target.compatible }

module Identity {Γ C : CAT} (f : MAP Γ C) where
  H = f ∘ pr₁ {Γ} {[1]}
  β = funCurry-β H
  abstract
    endpoint : (z : Obj-abs [1]) →
      (identity-boundary z f ∙ (β ▷ insert z)) =₂
        ((identity-boundary z f ∙ evaluate-curry z H) ∙ (evaluate-uncurry z (funCurry H)) ⁻¹)
    endpoint z =
      (cancel-right Q (p ∙ b) ∙
        isoComp-cong ((isoComp-assoc-at p b Q) ⁻¹) (idIso (Q ⁻¹))) ⁻¹
      where
      p : (H ∘ insert z) =₁ f
      p = identity-boundary z f
      b : (funUncurry (funCurry H) ∘ insert z) =₁ (H ∘ insert z)
      b = β ▷ insert z
      Q : (evaluate z ∘ funCurry H) =₁ (funUncurry (funCurry H) ∘ insert z)
      Q = evaluate-uncurry z (funCurry H)
  value : Presentation (identity-expression f)
  value = record { diagram = H
    ; source-frame = identity-boundary zero f ; target-frame = identity-boundary one f
    ; comparison = β ; source-compatible = endpoint zero ; target-compatible = endpoint one }

module Restricted {Γ Δ C : CAT} {f g : MAP Γ C} (α : MorphismExpression f g) (r : MAP Δ Γ) where
  module R = Restriction.At 𝒯 M ℱ I α r
  value : Presentation (restrict-expression α r)
  value = record { diagram = R.H ∘ R.step
    ; source-frame = R.Source.frame ; target-frame = R.Target.frame
    ; comparison = R.comparison
    ; source-compatible = R.Source.compatible ; target-compatible = R.Target.compatible }

module Evaluation {Γ X C : CAT} {f g : MAP Γ (Fun X C)} (α : MorphismExpression f g) where
  restricted = Restricted.value α (pr₁ {Γ} {X})
  fixed = Identity.value (id X ∘ pr₂ {Γ} {X})
  paired = Pairing.value restricted fixed
  value = Postcompose.value funEval paired
```
