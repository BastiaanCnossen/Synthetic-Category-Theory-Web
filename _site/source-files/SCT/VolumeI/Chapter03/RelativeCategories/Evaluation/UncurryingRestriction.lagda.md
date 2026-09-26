# Uncurrying commutes with restricting a triangle

Restrict a triangle before uncurrying, or uncurry it and restrict along
the corresponding product map. The standard substitution comparison
identifies the resulting triangles, including their specified matching.
This lemma does not assume the source structure is a constant family.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurryingRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.MappingSubstitution 𝒯 M ℱ using (funPost-uncurry-restrict)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurrying 𝒯 M ℱ using (paste-iso-squares)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-composite; pre-inverse)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Uncurrying 𝒯 M ℱ P using (module Triangle)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square; cancel-left)

module Restrict {K L S C B : CAT} (r : MAP C B) (f : MAP K (Fun S B))
  (s : MAP L K) (v : FunctorOver f (funPost r)) where
  h = FunctorLift.lift v
  θ = FunctorLift.comparison v
  R = productMap s (id S)
  a′ = comp-assoc s h (funPost r)
  b = funPost-uncurry r h
  bs = funPost-uncurry r (h ∘ s)
  bf = funUncurry-restrict (funPost r ∘ h) s
  ρ = funUncurry-restrict f s
  ℓ = funUncurry-restrict h s
  A = comp-assoc R (funUncurry h) r
  Ef = bs ∙ funUncurryIso a′
  Ef′ = A ∙ (b ▷ R)
  τs = funUncurryIso (θ ▷ s)
  τr = funUncurryIso θ ▷ R
  first = r ◁ ℓ

  restricted : FunctorOver (f ∘ s) (funPost r)
  restricted = record { lift = h ∘ s ; comparison = (θ ▷ s) ∙ a′ ⁻¹ }
  insertion : FunctorOver (funUncurry (f ∘ s)) (funUncurry f)
  insertion = record { lift = R ; comparison = ρ ⁻¹ }
  source = Triangle.value r (f ∘ s) restricted
  target = compose-over (Triangle.value r f v) insertion
  raw-source = τs ∙ Ef ⁻¹
  raw-target = ρ ⁻¹ ∙ (τr ∙ Ef′ ⁻¹)

  abstract
    source-normal : FunctorLift.comparison source =₂ raw-source
    source-normal = isoComp-cong (idIso τs) ((inverse-composite bs (funUncurryIso a′)) ⁻¹) ∙
      (isoComp-assoc-at τs ((funUncurryIso a′) ⁻¹) (bs ⁻¹) ∙
        (isoComp-cong (isoComp-cong (idIso τs) (funUncurryIso-inverse a′)) (idIso (bs ⁻¹)) ∙
          isoComp-cong (funUncurryIso-comp (θ ▷ s) (a′ ⁻¹)) (idIso (bs ⁻¹))))

    target-normal : FunctorLift.comparison target =₂ raw-target
    target-normal = isoComp-cong (idIso (ρ ⁻¹))
      (isoComp-cong (idIso τr) ((inverse-composite A (b ▷ R)) ⁻¹) ∙
        (isoComp-assoc-at τr ((b ▷ R) ⁻¹) (A ⁻¹) ∙
          (isoComp-cong (isoComp-cong (idIso τr) (pre-inverse b R)) (idIso (A ⁻¹)) ∙
            isoComp-cong (preWhisker-isoComp-at (funUncurryIso θ) (b ⁻¹) R) (idIso (A ⁻¹)))))

    raw-square : ((τr ∙ Ef′ ⁻¹) ∙ first) =₂ (ρ ∙ raw-source)
    raw-square = paste-iso-squares (Ef ⁻¹) (Ef′ ⁻¹) τs τr first bf ρ
      (move-square Ef′ bf first Ef ((funPost-uncurry-restrict r h s) ⁻¹ ∙
        isoComp-assoc-at A (b ▷ R) bf))
      ((funUncurry-restrict-inputs θ s) ⁻¹)

    matching : (raw-target ∙ first) =₂ raw-source
    matching = cancel-left ρ raw-source ∙
      (isoComp-cong (idIso (ρ ⁻¹)) raw-square ∙
        isoComp-assoc-at (ρ ⁻¹) (τr ∙ Ef′ ⁻¹) first)

    comparison : FunctorOverIso source target
    comparison = record { underlying = ℓ
      ; compatible = source-normal ⁻¹ ∙
          (matching ∙ isoComp-cong target-normal (idIso first)) }
    comparison-underlying : FunctorOverIso.underlying comparison =₂ ℓ
    comparison-underlying = idIso ℓ
```
