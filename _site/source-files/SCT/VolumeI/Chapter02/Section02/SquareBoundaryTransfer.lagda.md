# Transferring the boundary of a square

Four comparisons of whole corner cones identify a square's boundary
with four specified morphism expressions. The same four vertex maps
retarget both triangle presentations, so their diagonal comparisons
continue to preserve the original endpoints.

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

module SCT.VolumeI.Chapter02.Section02.SquareBoundaryTransfer
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.TriangleVertices 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.CompositionIdentifications 𝒯 M ℱ P I E S using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.FramedConeRestriction 𝒯 M ℱ P using (framed-cone)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section04.ProductAssociativity 𝒯 M using (cancel-inverse-tail)
import SCT.VolumeI.Chapter02.Section02.SquareCompositePresentations as Geometry
import SCT.VolumeI.Chapter02.Section02.PresentationSubstitution as Presentations

vertex-change : {Γ A C : CAT} (e : MAP A C) {f g : MAP Γ A} {z z′ : MAP Γ C}
  (p : (e ∘ f) =₁ z) (q : (e ∘ g) =₁ z′) (α : f =₁ g) → z =₁ z′
vertex-change e p q α = q ∙ ((e ◁ α) ∙ p ⁻¹)

abstract
  endpoint : {Γ A C : CAT} (e : MAP A C) {f g : MAP Γ A} {z z′ : MAP Γ C}
    (p : (e ∘ f) =₁ z) (q : (e ∘ g) =₁ z′) (α : f =₁ g) →
    (q ∙ (e ◁ α)) =₂ (vertex-change e p q α ∙ p)
  endpoint e p q α = (isoComp-cong (idIso q) (cancel-inverse-tail (e ◁ α) p) ∙
    isoComp-assoc-at q ((e ◁ α) ∙ p ⁻¹) p) ⁻¹

  endpoint-from-corner : {Γ A B C : CAT} {f : MAP A C} {g : MAP B C}
    {l l′ : MAP Γ A} {r r′ : MAP Γ B} {z z′ : MAP Γ C}
    (p : (f ∘ l) =₁ z) (q : (g ∘ r) =₁ z)
    (p′ : (f ∘ l′) =₁ z′) (q′ : (g ∘ r′) =₁ z′)
    (Φ : ConeIso (framed-cone l r p q) (framed-cone l′ r′ p′ q′)) →
    (p′ ∙ (f ◁ ConeIso.leftIso Φ)) =₂
      (vertex-change g q q′ (ConeIso.rightIso Φ) ∙ p)
  endpoint-from-corner {f = f} {g} p q p′ q′ Φ =
    (isoComp-assoc-at q′ ((g ◁ ConeIso.rightIso Φ) ∙ q ⁻¹) p) ⁻¹ ∙
    isoComp-cong (idIso q′) ((isoComp-assoc-at (g ◁ ConeIso.rightIso Φ) (q ⁻¹) p) ⁻¹) ∙
    vertex-from-corner q′ p′ (f ◁ ConeIso.leftIso Φ)
      ((g ◁ ConeIso.rightIso Φ) ∙ (q ⁻¹ ∙ p)) (ConeIso.compatible Φ)

module At {Γ C : CAT} (W : MAP Γ (Fun ([1] × [1]) C))
  {x y z w : MAP Γ C}
  (top : MorphismExpression x y) (right : MorphismExpression y z)
  (left : MorphismExpression x w) (bottom : MorphismExpression w z) where
  module G = Geometry.At 𝒯 M ℱ P I E S W
  module T = MorphismExpression top
  module R = MorphismExpression right
  module L = MorphismExpression left
  module B = MorphismExpression bottom
  module GT = MorphismExpression G.top
  module GR = MorphismExpression G.right
  module GL = MorphismExpression G.left
  module GB = MorphismExpression G.bottom

  module Identified
    (α : GT.arrow =₁ T.arrow) (β : GR.arrow =₁ R.arrow)
    (γ : GL.arrow =₁ L.arrow) (δ : GB.arrow =₁ B.arrow)
    (source-top : (T.source-frame ∙ (ev₀ ◁ α)) =₂
      (vertex-change ev₀ GL.source-frame L.source-frame γ ∙ GT.source-frame))
    (target-top : (T.target-frame ∙ (ev₁ ◁ α)) =₂
      (vertex-change ev₀ GR.source-frame R.source-frame β ∙ GT.target-frame))
    (source-bottom : (B.source-frame ∙ (ev₀ ◁ δ)) =₂
      (vertex-change ev₁ GL.target-frame L.target-frame γ ∙ GB.source-frame))
    (target-bottom : (B.target-frame ∙ (ev₁ ◁ δ)) =₂
      (vertex-change ev₁ GR.target-frame R.target-frame β ∙ GB.target-frame)) where
    x-change = vertex-change ev₀ GL.source-frame L.source-frame γ
    y-change = vertex-change ev₀ GR.source-frame R.source-frame β
    w-change = vertex-change ev₁ GL.target-frame L.target-frame γ
    z-change = vertex-change ev₁ GR.target-frame R.target-frame β
    module Upper = Presentations.Retarget 𝒯 M ℱ P I E S G.upper x-change y-change z-change
    module Lower = Presentations.Retarget 𝒯 M ℱ P I E S G.lower x-change w-change z-change

    top-comparison : ExpressionIso (retarget-expression G.top x-change y-change) top
    top-comparison = record { comparison = α ; source-compatible = source-top ; target-compatible = target-top }
    bottom-comparison : ExpressionIso (retarget-expression G.bottom w-change z-change) bottom
    bottom-comparison = record { comparison = δ ; source-compatible = source-bottom ; target-compatible = target-bottom }
    left-comparison : ExpressionIso (retarget-expression G.left x-change w-change) left
    left-comparison = record { comparison = γ
      ; source-compatible = endpoint ev₀ GL.source-frame L.source-frame γ
      ; target-compatible = endpoint ev₁ GL.target-frame L.target-frame γ }
    right-comparison : ExpressionIso (retarget-expression G.right y-change z-change) right
    right-comparison = record { comparison = β
      ; source-compatible = endpoint ev₀ GR.source-frame R.source-frame β
      ; target-compatible = endpoint ev₁ GR.target-frame R.target-frame β }

    comparison : ExpressionIso (compose-expression top right) (compose-expression left bottom)
    comparison = expressionIso-compose (compose-expression-cong left-comparison bottom-comparison)
      (expressionIso-compose
        (expressionIso-compose (expressionIso-inverse (recognize-composite Lower.value))
          (recognize-composite Upper.value))
        (expressionIso-inverse (compose-expression-cong top-comparison right-comparison)))
```
