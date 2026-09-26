# Restricting the uncurried identity comparison

The identity comparison has three stages: uncurrying, normalization of the
constant identity term, and application. We compare each stage under the
same change of parameter, using the original chosen comparisons throughout.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Substitution.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Substitution.MappingProofCalculus as MappingProofCalculus
import SCT.VolumeI.Chapter01.Section04.Currying as Currying
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.CompositionNaturality as CompositionNaturality
import SCT.VolumeI.Chapter01.Section04.Substitution.ApplicationRestriction as ApplicationRestriction
import SCT.VolumeI.Chapter01.Section04.Substitution.EvaluationParameterChange as EvaluationParameterChange
import SCT.VolumeI.Chapter01.Section04.Substitution.IdentityParameterChange as IdentityParameterChange

module SCT.VolumeI.Chapter01.Section04.Substitution.UncurriedIdentityParameterChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open Currying 𝒯 M hiding (mapUncurry-actions-agree)
open MapComposition 𝒯 M
open InternalCoherence 𝒯 M using (uncurry-identity)
open MappingProofCalculus 𝒯 M using
  (apply-cong-Iso₂; apply-cong-comp; mapUncurry-as-apply-natural; binary-pre-inputs;
   combine-apply; post-iterated-comparison; mapUncurry-as-apply-parameter-change; mapUncurry-actions-agree)
open IdentityParameterChange 𝒯 M using (terminal-Iso₂; const-pre-change; apply-identity-change)

abstract
  const-pre-iterated : {Q R X A : CAT} (x : Obj-abs A) (h : MAP R X) (t : MAP Q R)
    → (const-pre x (h ∘ t) ∙ comp-assoc t h (const x)) =₂
        (const-pre x t ∙ (const-pre x h ▷ t))
  const-pre-iterated {Q} {R} {X} x h t =
    let u = terminal-iso (terminate X ∘ h) (terminate R)
        v = terminal-iso (terminate R ∘ t) (terminate Q)
        w = terminal-iso (terminate X ∘ (h ∘ t)) (terminate Q)
        z = idIso (terminate Q)
        tail = const-pre x t ∙ (const-pre x h ▷ t)
    in isoComp-unitˡ-at tail ∙
      (isoComp-cong (postWhisker-idIso x (terminate Q)) (idIso tail) ∙
        post-iterated-comparison x (terminate X) h t u v w z (terminal-Iso₂ _ _))

abstract
  combine-first : {X C D : CAT}
    {f₀ f₁ f₂ : MAP X (Map C D)} {x₀ x₁ : MAP X C} {source : MAP X D}
    (α : f₁ =₁ f₂) (γ : f₀ =₁ f₁) (β : x₀ =₁ x₁)
    (base : source =₁ (applyTerm f₀ x₀))
    → (applyTerm-cong α (idIso x₁) ∙ (applyTerm-cong γ β ∙ base)) =₂
        (applyTerm-cong (α ∙ γ) β ∙ base)
  combine-first α γ β base =
    isoComp-cong (apply-cong-Iso₂ (idIso (α ∙ γ)) (isoComp-unitˡ-at β)) (idIso base) ∙
      combine-apply α (idIso _) γ β base

module IdentityRestriction {P Q C : CAT} (σ : MAP Q P) where

  s : MAP (Q × C) (P × C)
  s = productMap σ (id C)
  J : MAP P (Map C C)
  J = identityTerm C
  J′ : MAP Q (Map C C)
  J′ = identityTerm C
  change = const-pre (mapId C) σ
  old = mapUncurry-as-apply J
  new = mapUncurry-as-apply J′
  middle = mapUncurry-as-apply (J ∘ σ)
  uncurryingChange = mapUncurry-restrict J σ

  constantBefore = const-pre (mapId C) (pr₁ {P} {C})
  constantAfter = const-pre (mapId C) (pr₁ {Q} {C})
  b = comp-unitˡ pr₂ ∙ pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂)
  first = (J ◁ pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)) ∙ comp-assoc s pr₁ J
  A = comp-assoc (pr₁ {Q} {C}) σ J
  constantAlongComposite = const-pre (mapId C) (σ ∘ pr₁ {Q} {C})
  constantChange = const-pre (mapId C) s
  pre = applyTerm-pre (J ∘ pr₁) pr₂ s
  tail = (old ▷ s) ∙ uncurryingChange
  base = pre ∙ tail

  left = applyTerm-cong constantAfter (idIso pr₂) ∙ (new ∙ mapUncurryIso change)
  right = applyTerm-cong (constantChange ∙ (constantBefore ▷ s)) b ∙ base

  abstract
    constant-normalization : left =₂ right
    constant-normalization =
      let input = mapUncurry-as-apply-natural change ∙
            isoComp-cong (idIso new) (mapUncurry-actions-agree change)
          combine = combine-first constantAfter (change ▷ pr₁) (idIso pr₂) middle
          constants = isoComp-cong
            (apply-cong-Iso₂ ((const-pre-iterated (mapId C) σ pr₁) ⁻¹) (idIso (idIso pr₂)))
            (idIso middle)
          separate = (combine-first constantAlongComposite A (idIso pr₂) middle) ⁻¹
          substitute = isoComp-cong (idIso (applyTerm-cong constantAlongComposite (idIso pr₂)))
            (mapUncurry-as-apply-parameter-change J σ)
          combineAgain = combine-first constantAlongComposite first b base
          compareConstants = const-pre-change (mapId C) pr₁ s (σ ∘ pr₁)
            (pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂))
      in isoComp-cong (apply-cong-Iso₂ compareConstants (idIso b)) (idIso base) ∙
        (combineAgain ∙ (substitute ∙ (separate ∙ (constants ∙
          (combine ∙ isoComp-cong (idIso (applyTerm-cong constantAfter (idIso pr₂))) input)))))

  abstract
    comparison : ((uncurry-identity Q C) ∙ mapUncurryIso change) =₂
      (b ∙ ((uncurry-identity P C ▷ s) ∙ uncurryingChange))
    comparison =
      let identityOld = apply-identity (pr₂ {P} {C})
          identityNew = apply-identity (pr₂ {Q} {C})
          oldNormalization = applyTerm-cong constantBefore (idIso pr₂)
          newNormalization = applyTerm-cong constantAfter (idIso pr₂)
          normPre = oldNormalization ▷ s
          oldPre = old ▷ s
          identityPre = identityOld ▷ s
          identityChange = applyTerm-cong constantChange b
          normalizedPre = applyTerm-pre (identityTerm C) (pr₂ {P} {C}) s
          q = applyTerm-cong (constantBefore ▷ s) (idIso (pr₂ ∘ s))

          source = isoComp-cong (idIso identityNew)
              (isoComp-assoc-at newNormalization new (mapUncurryIso change)) ∙
            isoComp-assoc-at identityNew (newNormalization ∙ new) (mapUncurryIso change)
          factor = apply-cong-comp constantChange (constantBefore ▷ s) b (idIso (pr₂ ∘ s)) ∙
            (apply-cong-Iso₂ (idIso (constantChange ∙ (constantBefore ▷ s))) (isoComp-unitʳ-at b)) ⁻¹
          moveNormalization =
            (isoComp-cong (apply-cong-Iso₂ (idIso (constantBefore ▷ s)) (preWhisker-idIso pr₂ s)) (idIso pre) ∙
              binary-pre-inputs mapEval constantBefore (idIso pr₂) s) ⁻¹
          moveInside = isoComp-assoc-at normalizedPre normPre tail ∙
            (isoComp-cong moveNormalization (idIso tail) ∙
              (isoComp-assoc-at q pre tail) ⁻¹)
          regroup = (isoComp-assoc-at identityNew (identityChange ∙ normalizedPre) (normPre ∙ tail)) ⁻¹ ∙
            isoComp-cong (idIso identityNew)
              ((isoComp-assoc-at identityChange normalizedPre (normPre ∙ tail)) ⁻¹ ∙
                (isoComp-cong (idIso identityChange) moveInside ∙
                  isoComp-assoc-at identityChange q base))
          evaluate = isoComp-cong (apply-identity-change (pr₂ {P} {C}) s b)
            (idIso (normPre ∙ tail))

          splitOld = isoComp-cong (idIso identityPre)
              (preWhisker-isoComp-at oldNormalization old s) ∙
            preWhisker-isoComp-at identityOld (oldNormalization ∙ old) s
          joinOld = isoComp-cong (splitOld ⁻¹) (idIso uncurryingChange) ∙
            ((isoComp-assoc-at identityPre (normPre ∙ oldPre) uncurryingChange) ⁻¹ ∙
              isoComp-cong (idIso identityPre) ((isoComp-assoc-at normPre oldPre uncurryingChange) ⁻¹))
          finish = isoComp-cong (idIso b) joinOld ∙
            isoComp-assoc-at b identityPre (normPre ∙ tail)
      in finish ∙ (evaluate ∙ (regroup ∙
        (isoComp-cong (idIso identityNew) (isoComp-cong factor (idIso base)) ∙
        (isoComp-cong (idIso identityNew) constant-normalization ∙ source))))

uncurry-identity-parameter-change : {P Q C : CAT} (σ : MAP Q P)
  → let s = productMap σ (id C)
        b = comp-unitˡ pr₂ ∙ pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂)
    in ((uncurry-identity Q C) ∙ mapUncurryIso (const-pre (mapId C) σ)) =₂
      (b ∙ ((uncurry-identity P C ▷ s) ∙ mapUncurry-restrict (identityTerm C) σ))
uncurry-identity-parameter-change = IdentityRestriction.comparison
```
