# Naturality with a constant source

For a transformation from a constant functor to a target functor, its
naturality square is a triangle: the constant side is an identity.
The result below retains both endpoint frames and permits arbitrary
absolute parameter categories.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ConstantSourceNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (retarget-id; retarget-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
  using (expressionIso-compose; expressionIso-inverse; expressionIso-id; retarget-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.ExpressionUnitLaws 𝒯 M ℱ P I E S using (left-unit)
open import SCT.VolumeI.Chapter02.Section02.Naturality 𝒯 M ℱ P I E S using (naturality)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ConstantFunctorExpressions as Constant

open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse)

abstract
  constant-frame : {Γ B C : CAT} (x : Obj-abs C) (h : MAP Γ B) →
    Constant.Change.frame 𝒯 M ℱ P I E x h =₂ const-pre x h
  constant-frame {B = B} x h = isoComp-cong (idIso (x ◁ terminal-iso _ _))
    (inverse-inverse A ∙ (＝-inv ◁ normalized))
    where
    A : ((x ∘ terminate B) ∘ h) =₁ (x ∘ (terminate B ∘ h))
    A = comp-assoc h (terminate B) x
    normalized : ((idIso (const x) ▷ h) ∙ A ⁻¹) =₂ (A ⁻¹)
    normalized = isoComp-unitˡ-at (A ⁻¹) ∙
      isoComp-cong (preWhisker-idIso (const x) h) (idIso (A ⁻¹))

module At {Γ B C : CAT} (x : Obj-abs C) {q : MAP B C}
  (α : MorphismExpression (const x) q) {a b : MAP Γ B}
  (u : MorphismExpression a b) where
  private
    A = const-pre x a
    B₀ = const-pre x b
    Z = idIso (q ∘ b)
    Y = idIso (q ∘ a)
    f = restrict-expression α a
    g = post-expression q u
    h = post-expression (const x) u
    k = restrict-expression α b

  source-component : MorphismExpression (const x) (q ∘ a)
  source-component = retarget-expression f A Y

  target-component : MorphismExpression (const x) (q ∘ b)
  target-component = retarget-expression k B₀ Z

  private
    left-reframed = retarget-expression (compose-expression f g) A Z
    right-reframed = retarget-expression (compose-expression h k) A Z
    middle = retarget-expression h A B₀

    abstract
      reframe-left : ExpressionIso (compose-expression source-component g) left-reframed
      reframe-left = expressionIso-compose (retarget-composition f g A Y Z)
        (compose-expression-cong (expressionIso-id source-component) (expressionIso-inverse (retarget-id g)))

      raw-naturality : ExpressionIso (compose-expression f g) (compose-expression h k)
      raw-naturality = naturality α u

      constant-comparison : ExpressionIso middle (identity-expression (const x))
      constant-comparison = expressionIso-compose (Constant.At.comparison 𝒯 M ℱ P I E x u)
        (retarget-cong h ((constant-frame x a) ⁻¹) ((constant-frame x b) ⁻¹))

      use-naturality : ExpressionIso left-reframed right-reframed
      use-naturality = retarget-expressionIso raw-naturality A Z

      reframe-right : ExpressionIso right-reframed (compose-expression middle target-component)
      reframe-right = expressionIso-inverse (retarget-composition h k A B₀ Z)

      remove-constant : ExpressionIso (compose-expression middle target-component) target-component
      remove-constant = expressionIso-compose (left-unit target-component)
        (compose-expression-cong constant-comparison (expressionIso-id target-component))

  abstract
    triangle : ExpressionIso (compose-expression source-component g) target-component
    triangle = expressionIso-compose remove-constant
      (expressionIso-compose reframe-right (expressionIso-compose use-naturality reframe-left))
```
