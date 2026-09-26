# Dependent products give equivalences of relative functor categories

The universal property initially concerns mapping animae. Testing it
on all category parameters strengthens it to the corresponding functor
categories. Parameterized pullbacks compare the evaluation of a whole
family with native relative currying. Factorization and reflection then
construct the inverse and its two identifications.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.ProductCalculus.FunctorCategoryUncurrying
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.FamilyReflection 𝒯 M ℱ P using (reflect-family)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P using (module Curry)
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.Currying.DependentUncurryingFamilies 𝒯 M ℱ P using (module Evaluation)
open import SCT.VolumeI.Chapter03.Section05.Currying.RelativeCurrying 𝒯 M ℱ P using (module Currying)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Identifications 𝒯 M ℱ P using (module Change)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.RestrictionEquivalences 𝒯 M ℱ P using (module Restriction)

module Uncurrying {S T C K : CAT} (p : MAP S T) (f : MAP C S)
  (Π : DependentProduct p f) (k : MAP K T) where
  g = DependentProduct.projection Π
  ε = DependentProduct.evaluation Π
  k′ : MAP (Pullback k p) S
  k′ = pullback₂
  module Evaluated = Evaluation p f Π k using (functor; module At)
  module Native = Currying p f Π using (evaluate; module Native)
  functor : MAP (FunOver k g) (FunOver k′ f)
  functor = Evaluated.functor

  abstract
    evaluate-identification : {A : CAT} {t : MAP A T} {u v : FunctorOver t g} →
      FunctorOverIso u v → FunctorOverIso (Native.evaluate u) (Native.evaluate v)
    evaluate-identification Φ = postwhisker-over ε (Change.Identification.comparison p Φ)

  module At (X : CAT) where
    module Family = Evaluated.At X using (inclusion; inclusion-isEquiv; family-comparison)
    t = k ∘ pr₂ {C = X}
    r : MAP (Pullback t p) S
    r = pullback₂
    module Restricted = Restriction r f Family.inclusion Family.inclusion-isEquiv using (module Factor; module Reflect)

    module Factor (v : MAP X (FunOver k′ f)) where
      module Lifted = Restricted.Factor (family k′ f v) using (value; comparison)
      u : FunctorOver t g
      u = Native.Native.factor t Lifted.value
      value : MAP X (FunOver k g)
      value = Curry.functor k g (FunctorLift.lift u) (FunctorLift.comparison u)
      abstract
        curried-family : FunctorOverIso (family k g value) u
        curried-family = curried-beta k g u

        evaluated-family : FunctorOverIso (Native.evaluate (family k g value)) (Native.evaluate u)
        evaluated-family = evaluate-identification {t = t} {u = family k g value} {v = u} curried-family

        evaluated-factor : FunctorOverIso (Native.evaluate u) Lifted.value
        evaluated-factor = Native.Native.factor-β t Lifted.value

        restricted-family : FunctorOverIso
          (compose-over (Native.evaluate (family k g value)) Family.inclusion)
          (compose-over (Native.evaluate u) Family.inclusion)
        restricted-family = prewhisker-over {f = k′ ∘ pr₂ {C = X}} {g = r} {h = f}
          {v = Native.evaluate (family k g value)} {w = Native.evaluate u} Family.inclusion evaluated-family

        restricted-factor : FunctorOverIso
          (compose-over (Native.evaluate u) Family.inclusion)
          (compose-over Lifted.value Family.inclusion)
        restricted-factor = prewhisker-over {f = k′ ∘ pr₂ {C = X}} {g = r} {h = f}
          {v = Native.evaluate u} {w = Lifted.value} Family.inclusion evaluated-factor

        family-evaluation : FunctorOverIso (family k′ f (functor ∘ value))
          (compose-over (Native.evaluate (family k g value)) Family.inclusion)
        family-evaluation = Family.family-comparison value

        evaluated-comparison : FunctorOverIso (family k′ f (functor ∘ value))
          (compose-over (Native.evaluate u) Family.inclusion)
        evaluated-comparison = compose-iso-over {f = k′ ∘ pr₂ {C = X}} {g = f} restricted-family family-evaluation

        factor-comparison : FunctorOverIso (family k′ f (functor ∘ value))
          (compose-over Lifted.value Family.inclusion)
        factor-comparison = compose-iso-over {f = k′ ∘ pr₂ {C = X}} {g = f} restricted-factor evaluated-comparison

        compared-family : FunctorOverIso (family k′ f (functor ∘ value)) (family k′ f v)
        compared-family = compose-iso-over {f = k′ ∘ pr₂ {C = X}} {g = f} Lifted.comparison factor-comparison

        comparison : (functor ∘ value) =₁ v
        comparison = reflect-family k′ f (functor ∘ value) v compared-family

    abstract
      reflect : (F G : MAP X (FunOver k g)) → (functor ∘ F) =₁ (functor ∘ G) → F =₁ G
      reflect F G α = reflect-family k g F G
        (Native.Native.reflect t (family k g F) (family k g G)
          (Restricted.Reflect.comparison (Native.evaluate (family k g F)) (Native.evaluate (family k g G))
            (compose-iso-over (Family.family-comparison G)
              (compose-iso-over (family-identification k′ f α)
                (inverse-iso-over (Family.family-comparison F))))))

  inverse : MAP (FunOver k′ f) (FunOver k g)
  inverse = At.Factor.value (FunOver k′ f) (id (FunOver k′ f))
  abstract
    right-inverse : (functor ∘ inverse) =₁ id (FunOver k′ f)
    right-inverse = At.Factor.comparison (FunOver k′ f) (id (FunOver k′ f))

    left-inverse : (inverse ∘ functor) =₁ id (FunOver k g)
    left-inverse = At.reflect (FunOver k g) _ _
      ((comp-unitʳ functor) ⁻¹ ∙
        (comp-unitˡ functor ∙ ((right-inverse ▷ functor) ∙
          (comp-assoc functor inverse functor) ⁻¹)))

    functor-isEquiv : IsEquiv functor
    functor-isEquiv = record { inverse = inverse
      ; sectionIso = left-inverse ⁻¹ ; retractionIso = right-inverse ⁻¹ }
```
