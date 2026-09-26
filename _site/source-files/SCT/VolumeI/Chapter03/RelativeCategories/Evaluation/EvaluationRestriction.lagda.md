# Restricting a relative evaluation triangle

Uncurrying a restricted relative cone agrees with restricting its
uncurried triangle. Both the product projection witness and the original
matching identification are retained. This is the restriction bridge
between the local currying beta rule and the universal evaluation family.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ConstantNameRestriction as ConstantRestriction

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.EvaluationRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
  hiding (funUncurryIso-comp; funUncurryIso-inverse; funUncurry-restrict-inputs)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurrying 𝒯 M ℱ using (paste-iso-squares)
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.MappingSubstitution 𝒯 M ℱ using (funPost-uncurry-restrict)
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.MappingProofs 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurryingNormalization 𝒯 M ℱ using (endpoints-iterated)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯 using (changeEndpoints)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ParameterSecondCoordinate 𝒯 M using (parameter-over)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P using (uncurry-constant-name)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeUncurrying 𝒯 M ℱ P using (evalMatch)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

module Restriction {X Y C D S : CAT} {f : MAP C S} {g : MAP D S}
  (r : MAP Y X) (s : Cone (funPost g) (nameFun f) X) where
  p = Cone.left s
  q = Cone.right s
  τ = Cone.match s
  F = funPost {C = C} g
  G = nameFun f
  R = productMap r (id C)
  af = comp-assoc r p F
  ag = comp-assoc r q G
  bf = funUncurry-restrict (F ∘ p) r
  bg = funUncurry-restrict (G ∘ q) r
  fs = funPost-uncurry g p
  gs = uncurry-constant-name f q
  Ef = funPost-uncurry g (p ∘ r) ∙ funUncurryIso af
  Eg = uncurry-constant-name f (q ∘ r) ∙ funUncurryIso ag
  Ef′ = comp-assoc R (funUncurry p) g ∙ (fs ▷ R)
  Eg′ = parameter-over r f ∙ (gs ▷ R)
  ℓ = funUncurry-restrict p r
  source = evalMatch (conePre r s)
  target = parameter-over r f ∙ ((evalMatch s ▷ R) ∙ (comp-assoc R (funUncurry p) g) ⁻¹)
  rawSource = changeEndpoints Ef Eg (funUncurryIso (τ ▷ r))
  rawTarget = changeEndpoints Ef′ Eg′ (funUncurryIso τ ▷ R)

  abstract
    source-normal : source =₂ rawSource
    source-normal = endpoints-iterated (funUncurryIso af) (funUncurryIso ag)
        (funPost-uncurry g (p ∘ r)) (uncurry-constant-name f (q ∘ r)) (funUncurryIso (τ ▷ r)) ∙
      isoComp-cong (idIso (uncurry-constant-name f (q ∘ r)))
        (isoComp-cong
          (isoComp-cong (idIso (funUncurryIso ag))
            (isoComp-cong (idIso (funUncurryIso (τ ▷ r))) (funUncurryIso-inverse af) ∙
              funUncurryIso-comp (τ ▷ r) (af ⁻¹)) ∙
            funUncurryIso-comp ag ((τ ▷ r) ∙ af ⁻¹))
          (idIso ((funPost-uncurry g (p ∘ r)) ⁻¹)))

    target-normal : target =₂ rawTarget
    target-normal = endpoints-iterated (fs ▷ R) (gs ▷ R)
        (comp-assoc R (funUncurry p) g) (parameter-over r f) (funUncurryIso τ ▷ R) ∙
      isoComp-cong (idIso (parameter-over r f))
        (isoComp-cong
          (isoComp-cong (idIso (gs ▷ R))
            (isoComp-cong (idIso (funUncurryIso τ ▷ R)) (pre-inverse fs R) ∙
              preWhisker-isoComp-at (funUncurryIso τ) (fs ⁻¹) R) ∙
            preWhisker-isoComp-at gs (funUncurryIso τ ∙ fs ⁻¹) R)
          (idIso ((comp-assoc R (funUncurry p) g) ⁻¹)))

    right-square : (Eg′ ∙ bg) =₂ (idIso (f ∘ pr₂) ∙ Eg)
    right-square = (isoComp-unitˡ-at Eg) ⁻¹ ∙
      ((ConstantRestriction.Restriction.comparison 𝒯 M ℱ P f q r) ⁻¹ ∙
        isoComp-assoc-at (parameter-over r f) (gs ▷ R) bg)

    raw-square : (rawTarget ∙ (g ◁ ℓ)) =₂ rawSource
    raw-square = isoComp-unitˡ-at rawSource ∙
      paste-iso-squares
        (funUncurryIso (τ ▷ r) ∙ Ef ⁻¹) ((funUncurryIso τ ▷ R) ∙ Ef′ ⁻¹)
        Eg Eg′ (g ◁ ℓ) bg (idIso (f ∘ pr₂))
        (paste-iso-squares (Ef ⁻¹) (Ef′ ⁻¹) (funUncurryIso (τ ▷ r)) (funUncurryIso τ ▷ R)
          (g ◁ ℓ) bf bg
          (move-square Ef′ bf (g ◁ ℓ) Ef ((funPost-uncurry-restrict g p r) ⁻¹ ∙
            isoComp-assoc-at (comp-assoc R (funUncurry p) g) (fs ▷ R) bf))
          ((funUncurry-restrict-inputs τ r) ⁻¹)) right-square

    comparison : (target ∙ (g ◁ ℓ)) =₂ source
    comparison = source-normal ⁻¹ ∙
      (raw-square ∙ isoComp-cong target-normal (idIso (g ◁ ℓ)))
```
