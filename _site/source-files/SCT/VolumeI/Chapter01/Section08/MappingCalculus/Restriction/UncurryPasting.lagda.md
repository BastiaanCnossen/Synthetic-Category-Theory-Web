# Uncurrying a pasted restriction cone

The mapping cone is pasted before uncurrying. The resulting cocone is
compared with the paste after uncurrying, retaining the matchings and
the compositor on the composite upper arrow.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.UncurryPasting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Substitution.ParameterChange 𝒯 M using (mapUncurryIso-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
  using (inverse-composite; inverse-inverse; inverse-identity)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConePasting 𝒯 using (module PasteCones)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePasting 𝒯 using (module PasteCocones)
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconeArrowRestriction 𝒯 using (restrict)
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductRestrictionPasting 𝒯 M using (module Action)
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares 𝒯 M P
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.MapRestrictionCones 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.MapSquareEvaluation 𝒯 M P
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Restriction.PrecompositionComposition 𝒯 M using (module CompositorEvaluation)
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left; cancel-right)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-inverse)
open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯 using (changeEndpoints-to-square)

module Uncurry {A₁ A₂ A₃ B₁ B₂ E X : CAT}
  {g₁ : MAP A₁ A₂} (g₂ : MAP A₂ A₃)
  {h₁ : MAP B₁ B₂} {f₁ : MAP A₁ B₁} {f₂ : MAP A₂ B₂}
  (left : Square g₁ f₁ f₂ h₁)
  (s : Cone (mapPre {D = E} g₂) (mapPre f₂) X) where

  L = productRestriction X
  κ = mapPre-comp {D = E} g₁ g₂
  κp = productRestriction-comp X g₁ g₂
  t = mappingOut left E
  module CP = PasteCones (mapPre {D = E} g₂) (mapPre g₁) t
  module DP = PasteCocones (L g₁) (L g₂) (Action.image-square X left)
  flat = CP.flatten s
  changed = changeLeft κ flat
  source = restrict κp (uncurryRestriction {u = g₂ ∘ g₁} {v = f₁} changed)
  target = DP.flatten (uncurryRestriction {u = g₂} {v = f₂} s)
  k = Cone.left s
  h = Cone.right s
  τ = Cone.match s
  n = Cone.match (conePre h t)
  module Eval = Evaluation left h
    (CompositorEvaluation.comparison g₁ f₂ h)
    (CompositorEvaluation.comparison f₁ h₁ h)
  W = Cocone.match (restrictionCocone left (mapUncurry h))
  q₀ = mapPre-uncurry g₁ (mapPre g₂ ∘ k)
  q₁ = mapPre-uncurry g₁ (mapPre f₂ ∘ h)
  q₂ = mapPre-uncurry f₁ (mapPre h₁ ∘ h)
  qK = mapPre-uncurry g₂ k
  qH = mapPre-uncurry f₂ h
  bK = qK ▷ L g₁
  bH = qH ▷ L g₁
  d = mapPre-uncurry h₁ h ▷ L f₁
  un = mapUncurryIso n
  V = mapUncurryIso (mapPre g₁ ◁ τ)
  UA = mapUncurryIso (comp-assoc k (mapPre g₂) (mapPre g₁))
  raw = mapUncurryIso (Cone.match flat)
  us = Cocone.match (uncurryRestriction {u = g₂} {v = f₂} s)
  us-pre = us ▷ L g₁
  ut = mapUncurryIso τ
  ut-pre = ut ▷ L g₁
  ap = comp-assoc (L g₁) (L g₂) (mapUncurry k)
  T = ap ∙ (bK ∙ (q₀ ∙ UA))
  q = mapPre-uncurry (g₂ ∘ g₁) k
  K = mapUncurryIso (κ ▷ k)
  χ = mapUncurry k ◁ κp
  changed-raw = mapUncurryIso (Cone.match changed)
  target-match = Cocone.match target
  identity-left = idIso (mapUncurry k) ▷ (L g₂ ∘ L g₁)

  abstract
    raw-normal : raw =₂ (un ∙ (V ∙ UA))
    raw-normal = isoComp-cong (idIso un)
      (mapUncurryIso-comp (mapPre g₁ ◁ τ) (comp-assoc k (mapPre g₂) (mapPre g₁))) ∙
      mapUncurryIso-comp n ((mapPre g₁ ◁ τ) ∙ comp-assoc k (mapPre g₂) (mapPre g₁))

    source-square : (us-pre ∙ bK) =₂ (bH ∙ ut-pre)
    source-square = preWhisker-isoComp-at qH ut (L g₁) ∙
      ((preWhisker (L g₁) ◁
        ((changeEndpoints-to-square qK qH ut us (idIso us)) ⁻¹)) ∙
        (preWhisker-isoComp-at us qK (L g₁)) ⁻¹)

    left-square : ((W ∙ bH) ∙ q₁) =₂ ((d ∙ q₂) ∙ un)
    left-square = ((isoComp-assoc-at (d) (q₂) (un)) ⁻¹ ∙ ((((isoComp-cong (idIso (d)) ((isoComp-cong (idIso
      (q₂)) (((isoComp-unitʳ-at (un) ∙ isoComp-cong (idIso (un)) (isoComp-inverseˡ-at (q₁))) ∙
      isoComp-assoc-at (un) ((q₁) ⁻¹) (q₁))) ∙ isoComp-assoc-at (q₂) ((un ∙ (q₁) ⁻¹)) (q₁))) ∙
      isoComp-assoc-at (d) ((q₂ ∙ (un ∙ (q₁) ⁻¹))) (q₁)) ∙ isoComp-cong (Eval.comparison-compatibility) (idIso
      (q₁))) ∙ (isoComp-assoc-at (W) (bH) (q₁)) ⁻¹) ∙ isoComp-assoc-at (W) (bH) (q₁)))

    whole : (target-match ∙ T) =₂ ((d ∙ q₂) ∙ raw)
    whole = ((isoComp-assoc-at (d) (q₂) (raw)) ⁻¹ ∙ (isoComp-cong (idIso (d)) (isoComp-cong (idIso (q₂))
      (raw-normal ⁻¹)) ∙ ((((isoComp-cong (idIso (d)) (isoComp-assoc-at (q₂) (un) ((V ∙ UA))) ∙
      isoComp-assoc-at (d) ((q₂ ∙ un)) ((V ∙ UA))) ∙ isoComp-cong (((isoComp-assoc-at (d) (q₂) (un) ∙
      left-square) ∙ (isoComp-assoc-at (W) (bH) (q₁)) ⁻¹)) (idIso ((V ∙ UA)))) ∙ ((isoComp-cong (idIso (W))
      (isoComp-assoc-at (bH) (q₁) ((V ∙ UA))) ∙ isoComp-assoc-at (W) ((bH ∙ q₁)) ((V ∙ UA)))) ⁻¹) ∙
      (((isoComp-cong (idIso (W)) (isoComp-cong (idIso (bH)) (isoComp-assoc-at (q₁) (V) (UA))) ∙ isoComp-cong
      (idIso (W)) (isoComp-cong (idIso (bH)) (isoComp-cong ((mapPre-uncurry-natural g₁ τ) ⁻¹) (idIso (UA)))))
      ∙ (isoComp-cong (idIso (W)) (isoComp-cong (idIso (bH)) (isoComp-assoc-at (ut-pre) (q₀) (UA)))) ⁻¹) ∙
      (((isoComp-cong (idIso (W)) (isoComp-assoc-at (bH) (ut-pre) ((q₀ ∙ UA))) ∙ isoComp-cong (idIso (W))
      (isoComp-cong (source-square) (idIso ((q₀ ∙ UA))))) ∙ (isoComp-cong (idIso (W)) (isoComp-assoc-at
      (us-pre) (bK) ((q₀ ∙ UA)))) ⁻¹) ∙ (isoComp-cong (idIso (W)) ((isoComp-cong (idIso (us-pre)) (cancel-left
      (ap) ((bK ∙ (q₀ ∙ UA)))) ∙ isoComp-assoc-at (us-pre) ((ap) ⁻¹) ((ap ∙ (bK ∙ (q₀ ∙ UA)))))) ∙
      isoComp-assoc-at (W) ((us-pre ∙ (ap) ⁻¹)) ((ap ∙ (bK ∙ (q₀ ∙ UA))))))))))

    changed-normal : changed-raw =₂ (raw ∙ K ⁻¹)
    changed-normal = isoComp-cong (idIso raw) (mapUncurryIso-inverse (κ ▷ k)) ∙
      mapUncurryIso-comp (Cone.match flat) ((κ ▷ k) ⁻¹)

    compositor : (q ∙ K) =₂ (χ ∙ T)
    compositor = CompositorEvaluation.comparison g₁ g₂ k

    source-normal : (Cocone.match source) =₂ (q₂ ∙ (raw ∙ T ⁻¹))
    source-normal = ((isoComp-cong (idIso (q₂)) (isoComp-cong (idIso (raw)) ((((isoComp-cong (idIso ((UA) ⁻¹))
      (isoComp-assoc-at ((q₀) ⁻¹) ((bK) ⁻¹) ((ap) ⁻¹)) ∙ isoComp-assoc-at ((UA) ⁻¹) (((q₀) ⁻¹ ∙ (bK) ⁻¹))
      ((ap) ⁻¹)) ∙ isoComp-cong (((isoComp-assoc-at ((UA) ⁻¹) ((q₀) ⁻¹) ((bK) ⁻¹) ∙ isoComp-cong
      (inverse-composite (q₀) (UA)) (idIso ((bK) ⁻¹))) ∙ inverse-composite (bK) ((q₀ ∙ UA)))) (idIso ((ap)
      ⁻¹))) ∙ inverse-composite (ap) ((bK ∙ (q₀ ∙ UA))))))) ⁻¹ ∙ (((isoComp-cong (idIso (q₂)) (isoComp-cong
      (idIso (raw)) ((isoComp-cong (idIso ((UA) ⁻¹)) ((isoComp-cong (idIso ((q₀) ⁻¹)) ((isoComp-cong (idIso
      ((bK) ⁻¹)) (((isoComp-unitʳ-at ((ap) ⁻¹) ∙ isoComp-cong (idIso ((ap) ⁻¹)) (isoComp-inverseˡ-at (χ))) ∙
      isoComp-assoc-at ((ap) ⁻¹) ((χ) ⁻¹) (χ))) ∙ isoComp-assoc-at ((bK) ⁻¹) (((ap) ⁻¹ ∙ (χ) ⁻¹)) (χ))) ∙
      isoComp-assoc-at ((q₀) ⁻¹) (((bK) ⁻¹ ∙ ((ap) ⁻¹ ∙ (χ) ⁻¹))) (χ))) ∙ isoComp-assoc-at ((UA) ⁻¹) (((q₀) ⁻¹
      ∙ ((bK) ⁻¹ ∙ ((ap) ⁻¹ ∙ (χ) ⁻¹)))) (χ)))) ∙ isoComp-cong (idIso (q₂)) (isoComp-cong (idIso (raw))
      (isoComp-cong ((((((isoComp-cong (idIso ((UA) ⁻¹)) ((isoComp-cong (idIso ((q₀) ⁻¹)) (isoComp-assoc-at
      ((bK) ⁻¹) ((ap) ⁻¹) ((χ) ⁻¹)) ∙ isoComp-assoc-at ((q₀) ⁻¹) (((bK) ⁻¹ ∙ (ap) ⁻¹)) ((χ) ⁻¹))) ∙
      isoComp-assoc-at ((UA) ⁻¹) (((q₀) ⁻¹ ∙ ((bK) ⁻¹ ∙ (ap) ⁻¹))) ((χ) ⁻¹)) ∙ isoComp-cong ((((isoComp-cong
      (idIso ((UA) ⁻¹)) (isoComp-assoc-at ((q₀) ⁻¹) ((bK) ⁻¹) ((ap) ⁻¹)) ∙ isoComp-assoc-at ((UA) ⁻¹) (((q₀)
      ⁻¹ ∙ (bK) ⁻¹)) ((ap) ⁻¹)) ∙ isoComp-cong (((isoComp-assoc-at ((UA) ⁻¹) ((q₀) ⁻¹) ((bK) ⁻¹) ∙
      isoComp-cong (inverse-composite (q₀) (UA)) (idIso ((bK) ⁻¹))) ∙ inverse-composite (bK) ((q₀ ∙ UA))))
      (idIso ((ap) ⁻¹))) ∙ inverse-composite (ap) ((bK ∙ (q₀ ∙ UA))))) (idIso ((χ) ⁻¹))) ∙ inverse-composite
      (χ) ((ap ∙ (bK ∙ (q₀ ∙ UA))))) ∙ (＝-inv ◁ compositor)) ∙ (inverse-composite (q) (K)) ⁻¹)) (idIso (χ)))))
      ∙ (isoComp-cong (idIso (q₂)) (isoComp-cong (idIso (raw)) (isoComp-assoc-at ((K) ⁻¹) ((q) ⁻¹) (χ)))) ⁻¹)
      ∙ ((isoComp-cong (idIso (q₂)) (isoComp-assoc-at (raw) ((K) ⁻¹) (((q) ⁻¹ ∙ χ))) ∙ isoComp-cong (idIso
      (q₂)) (isoComp-cong (changed-normal) (idIso (((q) ⁻¹ ∙ χ))))) ∙ (isoComp-cong (idIso (q₂))
      (isoComp-assoc-at (changed-raw) ((q) ⁻¹) (χ)) ∙ isoComp-assoc-at (q₂) ((changed-raw ∙ (q) ⁻¹)) (χ)))))

  middle : Cocone (L g₂ ∘ L g₁) (L f₁) E
  middle = record { left = mapUncurry k ; right = mapUncurry (mapPre h₁ ∘ h)
    ; match = q₂ ∙ (raw ∙ T ⁻¹) }

  middle-comparison : CoconeIso middle target
  middle-comparison = record
    { leftIso = idIso (mapUncurry k) ; rightIso = mapPre-uncurry h₁ h
    ; compatible = ((isoComp-cong (idIso (d)) (isoComp-cong (idIso (q₂)) (isoComp-cong (idIso (raw))
      ((((isoComp-cong (idIso ((UA) ⁻¹)) (isoComp-assoc-at ((q₀) ⁻¹) ((bK) ⁻¹) ((ap) ⁻¹)) ∙ isoComp-assoc-at
      ((UA) ⁻¹) (((q₀) ⁻¹ ∙ (bK) ⁻¹)) ((ap) ⁻¹)) ∙ isoComp-cong (((isoComp-assoc-at ((UA) ⁻¹) ((q₀) ⁻¹) ((bK)
      ⁻¹) ∙ isoComp-cong (inverse-composite (q₀) (UA)) (idIso ((bK) ⁻¹))) ∙ inverse-composite (bK) ((q₀ ∙
      UA)))) (idIso ((ap) ⁻¹))) ∙ inverse-composite (ap) ((bK ∙ (q₀ ∙ UA)))))))) ⁻¹ ∙ ((((isoComp-cong (idIso
      (d)) (isoComp-assoc-at (q₂) (raw) (((UA) ⁻¹ ∙ ((q₀) ⁻¹ ∙ ((bK) ⁻¹ ∙ (ap) ⁻¹))))) ∙ isoComp-assoc-at (d)
      ((q₂ ∙ raw)) (((UA) ⁻¹ ∙ ((q₀) ⁻¹ ∙ ((bK) ⁻¹ ∙ (ap) ⁻¹))))) ∙ isoComp-cong (isoComp-assoc-at (d) (q₂)
      (raw)) ((((isoComp-cong (idIso ((UA) ⁻¹)) (isoComp-assoc-at ((q₀) ⁻¹) ((bK) ⁻¹) ((ap) ⁻¹)) ∙
      isoComp-assoc-at ((UA) ⁻¹) (((q₀) ⁻¹ ∙ (bK) ⁻¹)) ((ap) ⁻¹)) ∙ isoComp-cong (((isoComp-assoc-at ((UA) ⁻¹)
      ((q₀) ⁻¹) ((bK) ⁻¹) ∙ isoComp-cong (inverse-composite (q₀) (UA)) (idIso ((bK) ⁻¹))) ∙ inverse-composite
      (bK) ((q₀ ∙ UA)))) (idIso ((ap) ⁻¹))) ∙ inverse-composite (ap) ((bK ∙ (q₀ ∙ UA)))))) ∙ isoComp-cong
      whole (idIso (T ⁻¹)) ∙ (cancel-right T target-match) ⁻¹) ∙ ((isoComp-cong (idIso (W)) (isoComp-cong
      (idIso (us-pre)) (isoComp-unitʳ-at ((ap) ⁻¹))) ∙ isoComp-cong (idIso (W)) (isoComp-cong (idIso (us-pre))
      (isoComp-cong (idIso ((ap) ⁻¹)) (preWhisker-idIso (mapUncurry k) (L g₂ ∘ L g₁))))) ∙ (isoComp-cong
      (idIso (W)) (isoComp-assoc-at (us-pre) ((ap) ⁻¹) (identity-left)) ∙ isoComp-assoc-at (W) ((us-pre ∙ (ap)
      ⁻¹)) (identity-left))))) }

  comparison : CoconeIso source target
  comparison = coconeIso-compose middle-comparison
    (cocone-match-change _ _ _ _ source-normal)
```
