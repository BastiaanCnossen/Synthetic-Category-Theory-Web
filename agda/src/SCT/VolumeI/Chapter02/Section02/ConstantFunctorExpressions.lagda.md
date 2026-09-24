# Constant functors give identity expressions

Factor a constant functor through the terminal category. All expressions
in that category agree, including their endpoint frames. Preservation of
identity expressions and postcomposition pasting then give the comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.ConstantFunctorExpressions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-cong; retarget-assoc; post-retarget)
open import SCT.VolumeI.Chapter02.Section02.ExpressionPostcomposition 𝒯 M ℱ I using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.IdentityExpressionPostcomposition 𝒯 M ℱ P I E using (post-identity)
open import SCT.VolumeI.Chapter01.Section07.Contractible 𝒯 M ℱ using (fun-terminal-contractible)
open import SCT.VolumeI.Chapter01.Section05.Initial 𝒯 M using (contractible-compare)
open import SCT.VolumeI.Chapter01.Section04.IdentityParameterChange 𝒯 M using (terminal-Iso₂)
open import SCT.VolumeI.Chapter01.Section04.ProductAssociativity 𝒯 M using (cancel-inverse-tail)
import SCT.VolumeI.Chapter02.Section02.ExpressionPostcompositionPasting as Pasting
import SCT.VolumeI.Chapter02.Section02.IdentityExpressionRetargeting as IdChange

terminal-expression-unique : {Γ : CAT} {x y : MAP Γ One}
  (f g : MorphismExpression x y) → ExpressionIso f g
terminal-expression-unique f g = record
  { comparison = contractible-compare (fun-terminal-contractible [1]) (MorphismExpression.arrow f) (MorphismExpression.arrow g)
  ; source-compatible = terminal-Iso₂ _ _ ; target-compatible = terminal-Iso₂ _ _ }

module Change {Γ C D : CAT} (y : Obj-abs D) (x : MAP Γ C) where
  ρ : (y ∘ (terminate C ∘ x)) =₁ (const y ∘ x)
  ρ = (idIso (const y) ▷ x) ∙ (comp-assoc x (terminate C) y) ⁻¹
  τ : (terminate C ∘ x) =₁ terminate Γ
  τ = terminal-iso _ _
  frame : (const y ∘ x) =₁ const y
  frame = (y ◁ τ) ∙ ρ ⁻¹

module At {Γ C D : CAT} (y : Obj-abs D) {x x′ : MAP Γ C} (f : MorphismExpression x x′) where
  module Source = Change y x
  module Target = Change y x′
  module Paste = Pasting.At 𝒯 M ℱ P I E (terminate C) y (const y) (idIso (const y)) f
  terminal-expression = post-expression (terminate C) f
  adjusted = retarget-expression terminal-expression Source.τ Target.τ
  double = post-expression y terminal-expression

  terminal-comparison : ExpressionIso adjusted (identity-expression (terminate Γ))
  terminal-comparison = terminal-expression-unique adjusted (identity-expression (terminate Γ))
  reduced : ExpressionIso
    (retarget-expression double (y ◁ Source.τ) (y ◁ Target.τ)) (identity-expression (const y))
  reduced = expressionIso-compose (post-identity y (terminate Γ))
    (expressionIso-compose (post-expressionIso y terminal-comparison)
      (expressionIso-inverse (post-retarget y terminal-expression Source.τ Target.τ)))

  comparison : ExpressionIso
    (retarget-expression (post-expression (const y) f) Source.frame Target.frame)
    (identity-expression (const y))
  comparison = expressionIso-compose reduced
    (expressionIso-compose
      (retarget-cong double (cancel-inverse-tail (y ◁ Source.τ) Source.ρ) (cancel-inverse-tail (y ◁ Target.τ) Target.ρ))
      (expressionIso-compose (retarget-assoc double Source.ρ Target.ρ Source.frame Target.frame)
        (expressionIso-inverse (retarget-expressionIso Paste.comparison Source.frame Target.frame))))

point-frame : {D : CAT} (y : Obj-abs D) → const {P = One} y =₁ y
point-frame y = comp-unitʳ y ∙ (y ◁ terminal-iso (terminate One) (id One))

constant-point-frame : {C D : CAT} (y : Obj-abs D) (x : Obj-abs C) → (const y ∘ x) =₁ y
constant-point-frame y x = point-frame y ∙ Change.frame y x

module Absolute {C D : CAT} (y : Obj-abs D) {x x′ : Obj-abs C} (f : MorphismExpression x x′) where
  module Family = At y f
  comparison : ExpressionIso
    (retarget-expression (post-expression (const y) f) (constant-point-frame y x) (constant-point-frame y x′))
    (identity-expression y)
  comparison = expressionIso-compose (IdChange.At.comparison 𝒯 M ℱ P I E (point-frame y))
    (expressionIso-compose (retarget-expressionIso Family.comparison (point-frame y) (point-frame y))
      (expressionIso-inverse (retarget-assoc (post-expression (const y) f)
        (Change.frame y x) (Change.frame y x′) (point-frame y) (point-frame y))))
```
