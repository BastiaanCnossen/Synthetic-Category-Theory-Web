# Lifting interval diagrams through a pullback

An interval cone with whole cone comparisons at its endpoints lifts to
a morphism expression in any pullback cone. Both projected expressions
are identified with the original diagrams, with the prescribed endpoint
frames. Compatibility with the matching isomorphism is required in the
input cone comparisons, rather than inferred from separate projections.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PullbackDiagramLifting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I using (expressionIso-compose)
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.UniversalConeLifting as Lifting
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting as ChosenLifting
open Laws.PullbackStructure P using (Pullback; pullbackCone; pullbackLift; pullbackLift-β)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.DiagramExpressionIdentifications as Diagrams
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Postcomposition.CurryPostcomposition as Post

module IntervalCone {C D B T Γ : CAT} {f : MAP C B} {g : MAP D B}
  (t : Cone f g T) (L : Cone f g (Γ × [1]))
  (H : MAP (Γ × [1]) T) (β : ConeIso (conePre H t) L) where

  module Endpoint (z : Obj-abs [1]) (x : MAP Γ T)
    (Φ : ConeIso (conePre (insert z) L) (conePre x t)) where
    i = insert {X = Γ} z
    prescribed : ConeIso (conePre (H ∘ i) t) (conePre x t)
    prescribed = coneIso-compose Φ (coneIso-compose (coneIso-pre i β)
      (coneIso-inverse (conePre-assoc i H t)))

    record Frame : Set m where
      field
        value : (H ∘ i) =₁ x
        left-frame : ((Cone.left t ◁ value) ∙ comp-assoc i H (Cone.left t)) =₂
          (ConeIso.leftIso Φ ∙ (ConeIso.leftIso β ▷ i))
        right-frame : ((Cone.right t ◁ value) ∙ comp-assoc i H (Cone.right t)) =₂
          (ConeIso.rightIso Φ ∙ (ConeIso.rightIso β ▷ i))

    module FromLift (δ : (H ∘ i) =₁ x)
      (left-image : (Cone.left t ◁ δ) =₂ ConeIso.leftIso prescribed)
      (right-image : (Cone.right t ◁ δ) =₂ ConeIso.rightIso prescribed) where
      private
        cancel : {A : CAT} {j k l n : MAP Γ A}
          (a : l =₁ n) (b : k =₁ l) (d : k =₁ j) →
          ((a ∙ (b ∙ d ⁻¹)) ∙ d) =₂ (a ∙ b)
        cancel a b d = cancel-inverse-tail (a ∙ b) d ∙
          isoComp-cong ((isoComp-assoc-at a b (d ⁻¹)) ⁻¹) (idIso d)

      abstract
        left-frame : ((Cone.left t ◁ δ) ∙ comp-assoc i H (Cone.left t)) =₂
          (ConeIso.leftIso Φ ∙ (ConeIso.leftIso β ▷ i))
        left-frame = cancel (ConeIso.leftIso Φ) (ConeIso.leftIso β ▷ i)
          (comp-assoc i H (Cone.left t)) ∙
          isoComp-cong left-image (idIso (comp-assoc i H (Cone.left t)))

        right-frame : ((Cone.right t ◁ δ) ∙ comp-assoc i H (Cone.right t)) =₂
          (ConeIso.rightIso Φ ∙ (ConeIso.rightIso β ▷ i))
        right-frame = cancel (ConeIso.rightIso Φ) (ConeIso.rightIso β ▷ i)
          (comp-assoc i H (Cone.right t)) ∙
          isoComp-cong right-image (idIso (comp-assoc i H (Cone.right t)))

      frame : Frame
      frame = record { value = δ ; left-frame = left-frame ; right-frame = right-frame }

  module Framed (x y : MAP Γ T)
    (source : ConeIso (conePre (insert zero) L) (conePre x t))
    (target : ConeIso (conePre (insert one) L) (conePre y t))
    (source-frame : Endpoint.Frame zero x source)
    (target-frame : Endpoint.Frame one y target) where
    private
      module Source = Endpoint.Frame {z = zero} {x = x} {Φ = source} source-frame
      module Target = Endpoint.Frame {z = one} {x = y} {Φ = target} target-frame
    value : MorphismExpression x y
    value = expression H Source.value Target.value

    left : MorphismExpression (Cone.left t ∘ x) (Cone.left t ∘ y)
    left = expression (Cone.left L) (ConeIso.leftIso source) (ConeIso.leftIso target)
    right : MorphismExpression (Cone.right t ∘ x) (Cone.right t ∘ y)
    right = expression (Cone.right L) (ConeIso.rightIso source) (ConeIso.rightIso target)

    private
      module LeftPost = Post.At 𝒯 M ℱ P I E (Cone.left t) H Source.value Target.value using (comparison)
      module RightPost = Post.At 𝒯 M ℱ P I E (Cone.right t) H Source.value Target.value using (comparison)
      module LeftDiagram = Diagrams.At 𝒯 M ℱ P I E (Cone.left t ∘ H) (Cone.left L) (ConeIso.leftIso β)
        ((Cone.left t ◁ Source.value) ∙ comp-assoc (insert zero) H (Cone.left t))
        ((Cone.left t ◁ Target.value) ∙ comp-assoc (insert one) H (Cone.left t))
        (ConeIso.leftIso source) (ConeIso.leftIso target)
        (Source.left-frame ⁻¹) (Target.left-frame ⁻¹) using (comparison)
      module RightDiagram = Diagrams.At 𝒯 M ℱ P I E (Cone.right t ∘ H) (Cone.right L) (ConeIso.rightIso β)
        ((Cone.right t ◁ Source.value) ∙ comp-assoc (insert zero) H (Cone.right t))
        ((Cone.right t ◁ Target.value) ∙ comp-assoc (insert one) H (Cone.right t))
        (ConeIso.rightIso source) (ConeIso.rightIso target)
        (Source.right-frame ⁻¹) (Target.right-frame ⁻¹) using (comparison)
    abstract
      left-image : ExpressionIso (post-expression (Cone.left t) value) left
      left-image = expressionIso-compose LeftDiagram.comparison LeftPost.comparison
      right-image : ExpressionIso (post-expression (Cone.right t) value) right
      right-image = expressionIso-compose RightDiagram.comparison RightPost.comparison
```

The general construction retains its existing universal-cone factor and
endpoint lifts. The chosen-pullback specialization instead uses the primitive
pullback lifts and exposes their complete endpoint computations as `image`,
including compatibility with the matching identification. Both constructions
use the same projection calculation.

```agda

module At {C D B T Γ : CAT} {f : MAP C B} {g : MAP D B}
  (t : Cone f g T) (et : IsPullback t) (L : Cone f g (Γ × [1])) where
  module U = UniversalCone t et using (factor; factor-β)
  H : MAP (Γ × [1]) T
  H = U.factor L
  β : ConeIso (conePre H t) L
  β = U.factor-β L
  private
    module Core = IntervalCone t L H β using (module Endpoint; module Framed)

  module Endpoint (z : Obj-abs [1]) (x : MAP Γ T)
    (Φ : ConeIso (conePre (insert z) L) (conePre x t)) where
    i = insert {X = Γ} z
    prescribed : ConeIso (conePre (H ∘ i) t) (conePre x t)
    prescribed = Core.Endpoint.prescribed z x Φ
    module Lift = Lifting.UniversalLift 𝒯 P t et (H ∘ i) x prescribed
      using (lift; left-image; right-image)
    value : (H ∘ i) =₁ x
    value = Lift.lift
    private
      module Projection = Core.Endpoint.FromLift z x Φ value Lift.left-image Lift.right-image
        using (frame; left-frame; right-frame)
    frame : Core.Endpoint.Frame z x Φ
    frame = Projection.frame

    left-frame : ((Cone.left t ◁ value) ∙ comp-assoc i H (Cone.left t)) =₂
      (ConeIso.leftIso Φ ∙ (ConeIso.leftIso β ▷ i))
    left-frame = Projection.left-frame
    right-frame : ((Cone.right t ◁ value) ∙ comp-assoc i H (Cone.right t)) =₂
      (ConeIso.rightIso Φ ∙ (ConeIso.rightIso β ▷ i))
    right-frame = Projection.right-frame

  module WithEndpoints (x y : MAP Γ T)
    (source : ConeIso (conePre (insert zero) L) (conePre x t))
    (target : ConeIso (conePre (insert one) L) (conePre y t)) where
    module Source = Endpoint zero x source using (value; frame; left-frame; right-frame)
    module Target = Endpoint one y target using (value; frame; left-frame; right-frame)
    private
      module Result = Core.Framed x y source target Source.frame Target.frame
        using (value; left; right; left-image; right-image)
    value : MorphismExpression x y
    value = Result.value
    left : MorphismExpression (Cone.left t ∘ x) (Cone.left t ∘ y)
    left = Result.left
    right : MorphismExpression (Cone.right t ∘ x) (Cone.right t ∘ y)
    right = Result.right
    left-image : ExpressionIso (post-expression (Cone.left t) value) left
    left-image = Result.left-image
    right-image : ExpressionIso (post-expression (Cone.right t) value) right
    right-image = Result.right-image

module Chosen {C D B Γ : CAT} (f : MAP C B) (g : MAP D B)
  (L : Cone f g (Γ × [1])) where
  private
    t = pullbackCone f g
  H : MAP (Γ × [1]) (Pullback f g)
  H = pullbackLift L
  β : ConeIso (conePre H t) L
  β = pullbackLift-β L
  private
    module Core = IntervalCone t L H β using (module Endpoint; module Framed)

  module Endpoint (z : Obj-abs [1]) (x : MAP Γ (Pullback f g))
    (Φ : ConeIso (conePre (insert z) L) (conePre x t)) where
    i = insert {X = Γ} z
    prescribed : ConeIso (conePre (H ∘ i) t) (conePre x t)
    prescribed = Core.Endpoint.prescribed z x Φ
    private
      module Lift = ChosenLifting.Lift 𝒯 P (H ∘ i) x prescribed
        using (lift; left-image; right-image; comparison-image)
    value : (H ∘ i) =₁ x
    value = Lift.lift
    private
      module Projection = Core.Endpoint.FromLift z x Φ value Lift.left-image Lift.right-image
        using (frame; left-frame; right-frame)
    frame : Core.Endpoint.Frame z x Φ
    frame = Projection.frame

    left-frame : ((Cone.left t ◁ value) ∙ comp-assoc i H (Cone.left t)) =₂
      (ConeIso.leftIso Φ ∙ (ConeIso.leftIso β ▷ i))
    left-frame = Projection.left-frame
    right-frame : ((Cone.right t ◁ value) ∙ comp-assoc i H (Cone.right t)) =₂
      (ConeIso.rightIso Φ ∙ (ConeIso.rightIso β ▷ i))
    right-frame = Projection.right-frame

    image : ConeIso₂ (cone-action t value) prescribed
    image = Lift.comparison-image

  module WithEndpoints (x y : MAP Γ (Pullback f g))
    (source : ConeIso (conePre (insert zero) L) (conePre x t))
    (target : ConeIso (conePre (insert one) L) (conePre y t)) where
    module Source = Endpoint zero x source using (value; frame; left-frame; right-frame; image)
    module Target = Endpoint one y target using (value; frame; left-frame; right-frame; image)
    private
      module Result = Core.Framed x y source target Source.frame Target.frame
        using (value; left; right; left-image; right-image)
    value : MorphismExpression x y
    value = Result.value
    left : MorphismExpression (Cone.left t ∘ x) (Cone.left t ∘ y)
    left = Result.left
    right : MorphismExpression (Cone.right t ∘ x) (Cone.right t ∘ y)
    right = Result.right
    left-image : ExpressionIso (post-expression (Cone.left t) value) left
    left-image = Result.left-image
    right-image : ExpressionIso (post-expression (Cone.right t) value) right
    right-image = Result.right-image
```
