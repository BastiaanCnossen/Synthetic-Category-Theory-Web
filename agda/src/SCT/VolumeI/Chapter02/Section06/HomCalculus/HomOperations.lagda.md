# Realized operations on hom categories

An operation on endpoint families over the terminal category defines a
functor between hom categories. Its computation on an arbitrary family
is obtained by normalizing the base projection to the terminal map.
The endpoint-change law of the operation supplies the whole comparison;
no pointwise detection principle is used.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section06.HomCalculus.HomOperations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section06.HomCalculus.HomNormalization 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberOperations 𝒯 M ℱ P I
  using (ExpressionOperation; module Realize; module Fiber; module Lifts)

module Apply {C D : CAT} {x y : Obj-abs C} {u v : Obj-abs D}
  (operation : ExpressionOperation x y u v) where
  private
    module O = ExpressionOperation operation
    module Source = Fiber x y using (read; decode-comparison; decode-encode)
    module Result = Realize operation using (functor; on-family)
    module Target = Lifts u v using (lift-change)
  functor : MAP (Hom C x y) (Hom D u v)
  functor = Result.functor

  module AtFamily {Γ : CAT} (h : MAP Γ (Hom C x y)) where
    private
      b = EndpointFiber.base x y ∘ h
      τ = terminal-iso b (terminate Γ)
      raw = Source.read h
      normalized = hom-expression h
      image = O.apply (terminate Γ) normalized

      normalize : ExpressionIso (retarget-expression raw (x ◁ τ) (y ◁ τ)) normalized
      normalize = expressionIso-compose (Source.decode-encode (terminate Γ) normalized)
        (Source.decode-comparison (Normalize.comparison h))

      change : ExpressionIso
        (retarget-expression (O.apply b raw) (u ◁ τ) (v ◁ τ)) image
      change = expressionIso-compose (O.on-comparison (terminate Γ) normalize) (O.on-change raw τ)

    abstract
      comparison : (functor ∘ h) =₁ hom-intro image
      comparison = Target.lift-change (O.apply b raw) image τ change ∙ Result.on-family h
      computation : ExpressionIso (hom-expression (functor ∘ h)) image
      computation = expressionIso-compose (hom-β image) (hom-expression-cong comparison)
```
