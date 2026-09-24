# Normalizing a nested application after restriction

The following pasting is stated for arbitrary terms and endpoint
comparisons. It uses the supplied restriction square for application of
composition and the already proved naturality of that application.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.MappingProofCalculus as MappingProof
import SCT.VolumeI.Chapter01.Section04.CompositionRestrictionCalculus as Restriction

module SCT.VolumeI.Chapter01.Section04.NestedApplicationRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where
open Setup 𝒯
open Mapping.MappingAnimae M
open MapComposition 𝒯 M
open MappingProof 𝒯 M
open Restriction 𝒯 M using (apply-compose-natural)

module Assembly {Γ R C D E : CAT}
  (g₀ : MAP Γ (Map D E)) (f₀ : MAP Γ (Map C D)) (x₀ : MAP Γ C)
  (s : MAP R Γ)
  {g′ : MAP R (Map D E)} {f′ : MAP R (Map C D)} {x′ : MAP R C}
  (ag : (g₀ ∘ s) =₁ g′) (af : (f₀ ∘ s) =₁ f′) (b : (x₀ ∘ s) =₁ x′)
  {K : MAP Γ (Map C E)} (d : K =₁ (composeTerm g₀ f₀))
  {S : MAP Γ E} {T : MAP R E}
  (A₀ : S =₁ (applyTerm K x₀)) (B₀ : T =₁ (S ∘ s))
  (C₀ : (applyTerm (composeTerm g₀ f₀) x₀) =₁ (applyTerm g₀ (applyTerm f₀ x₀)))
  (C₁ : (applyTerm (composeTerm (g₀ ∘ s) (f₀ ∘ s)) (x₀ ∘ s)) =₁
    (applyTerm (g₀ ∘ s) (applyTerm (f₀ ∘ s) (x₀ ∘ s))))
  (C₂ : (applyTerm (composeTerm g′ f′) x′) =₁ (applyTerm g′ (applyTerm f′ x′))) where

  source-coordinate = composeTerm-cong ag af ∙
    (composeTerm-pre g₀ f₀ s ∙ (d ▷ s))
  before = applyTerm-cong ag (applyTerm-cong af b ∙ applyTerm-pre f₀ x₀ s) ∙
    (applyTerm-pre g₀ (applyTerm f₀ x₀) s ∙
      (((C₀ ∙ (applyTerm-cong d (idIso x₀) ∙ A₀)) ▷ s) ∙ B₀))
  after = C₂ ∙
    (applyTerm-cong source-coordinate b ∙
      (applyTerm-pre K x₀ s ∙ ((A₀ ▷ s) ∙ B₀)))

  module Calculation
    (restriction :
      (C₁ ∙ (applyTerm-cong (composeTerm-pre g₀ f₀ s) (idIso (x₀ ∘ s)) ∙
        applyTerm-pre (composeTerm g₀ f₀) x₀ s)) =₂
      ((applyTerm-cong (idIso (g₀ ∘ s)) (applyTerm-pre f₀ x₀ s) ∙
          applyTerm-pre g₀ (applyTerm f₀ x₀) s) ∙ (C₀ ▷ s)))
    (naturality : (C₂ ∙ applyTerm-cong (composeTerm-cong ag af) b) =₂
      (applyTerm-cong ag (applyTerm-cong af b) ∙ C₁)) where
    Pf = applyTerm-pre f₀ x₀ s
    Pg = applyTerm-pre g₀ (applyTerm f₀ x₀) s
    N = applyTerm-cong ag (applyTerm-cong af b ∙ Pf)
    changed = applyTerm-cong ag (applyTerm-cong af b)
    restricted = applyTerm-cong (idIso (g₀ ∘ s)) Pf
    D₀ = applyTerm-cong d (idIso x₀)
    tail = (A₀ ▷ s) ∙ B₀
    rest = (D₀ ▷ s) ∙ tail
    e = composeTerm-pre g₀ f₀ s
    Ract = applyTerm-cong e (idIso (x₀ ∘ s))
    Pmid = applyTerm-pre (composeTerm g₀ f₀) x₀ s
    middle-route = Ract ∙ Pmid
    Qact = applyTerm-cong (composeTerm-cong ag af) b
    Psource = applyTerm-pre K x₀ s
    Uact = applyTerm-cong (d ▷ s) (idIso (x₀ ∘ s))
    base = Psource ∙ tail

    opaque
      expandV : (((C₀ ∙ (D₀ ∙ A₀)) ▷ s) ∙ B₀) =₂ ((C₀ ▷ s) ∙ rest)
      expandV = isoComp-cong (idIso (C₀ ▷ s)) (isoComp-assoc-at (D₀ ▷ s) (A₀ ▷ s) B₀) ∙
        (isoComp-assoc-at (C₀ ▷ s) ((D₀ ▷ s) ∙ (A₀ ▷ s)) B₀ ∙
          isoComp-cong
            (isoComp-cong (idIso (C₀ ▷ s)) (preWhisker-isoComp-at D₀ A₀ s) ∙
              preWhisker-isoComp-at C₀ (D₀ ∙ A₀) s) (idIso B₀))
    opaque
      splitN : N =₂ (changed ∙ restricted)
      splitN = apply-cong-comp ag (idIso (g₀ ∘ s)) (applyTerm-cong af b) Pf ∙
        (apply-cong-Iso₂ (isoComp-unitʳ-at ag) (idIso (applyTerm-cong af b ∙ Pf))) ⁻¹
    opaque
      useRestriction : (restricted ∙ (Pg ∙ ((C₀ ▷ s) ∙ rest))) =₂ (C₁ ∙ (middle-route ∙ rest))
      useRestriction = isoComp-assoc-at C₁ middle-route rest ∙
        (isoComp-cong (restriction ⁻¹) (idIso rest) ∙
          ((isoComp-assoc-at (restricted ∙ Pg) (C₀ ▷ s) rest) ⁻¹ ∙
            (isoComp-assoc-at restricted Pg ((C₀ ▷ s) ∙ rest)) ⁻¹))
    opaque
      useNaturality : (changed ∙ (C₁ ∙ (middle-route ∙ rest))) =₂ (C₂ ∙ (Qact ∙ (middle-route ∙ rest)))
      useNaturality = isoComp-assoc-at C₂ Qact (middle-route ∙ rest) ∙
        (isoComp-cong (naturality ⁻¹) (idIso (middle-route ∙ rest)) ∙
          (isoComp-assoc-at changed C₁ (middle-route ∙ rest)) ⁻¹)
    opaque
      projectionNatural : (Pmid ∙ (D₀ ▷ s)) =₂ (Uact ∙ Psource)
      projectionNatural = isoComp-cong
          (apply-cong-Iso₂ (idIso (d ▷ s)) (preWhisker-idIso x₀ s)) (idIso Psource) ∙
        binary-pre-inputs mapEval d (idIso x₀) s
    opaque
      exchange : (Pmid ∙ rest) =₂ (Uact ∙ base)
      exchange = isoComp-assoc-at Uact Psource tail ∙
        (isoComp-cong projectionNatural (idIso tail) ∙
          (isoComp-assoc-at Pmid (D₀ ▷ s) tail) ⁻¹)
    opaque
      useProjection : (middle-route ∙ rest) =₂ (Ract ∙ (Uact ∙ base))
      useProjection = isoComp-cong (idIso Ract) exchange ∙
        isoComp-assoc-at Ract Pmid rest
    opaque
      combineInner : (Ract ∙ (Uact ∙ base)) =₂ (applyTerm-cong (e ∙ (d ▷ s)) (idIso (x₀ ∘ s)) ∙ base)
      combineInner = isoComp-cong
          (apply-cong-Iso₂ (idIso (e ∙ (d ▷ s))) (isoComp-unitˡ-at (idIso (x₀ ∘ s))))
          (idIso base) ∙
        combine-apply e (idIso (x₀ ∘ s)) (d ▷ s) (idIso (x₀ ∘ s)) base
    opaque
      combineOuter : (Qact ∙ (applyTerm-cong (e ∙ (d ▷ s)) (idIso (x₀ ∘ s)) ∙ base)) =₂ (applyTerm-cong source-coordinate b ∙ base)
      combineOuter = isoComp-cong
          (apply-cong-Iso₂ (idIso source-coordinate) (isoComp-unitʳ-at b)) (idIso base) ∙
        combine-apply (composeTerm-cong ag af) b (e ∙ (d ▷ s)) (idIso (x₀ ∘ s)) base
    opaque
      finish : (C₂ ∙ (Qact ∙ (middle-route ∙ rest))) =₂ after
      finish = isoComp-cong (idIso C₂)
        (combineOuter ∙
          isoComp-cong (idIso Qact) (combineInner ∙ useProjection))
    opaque
      begin : before =₂ (changed ∙ (restricted ∙ (Pg ∙ ((C₀ ▷ s) ∙ rest))))
      begin = isoComp-assoc-at changed restricted (Pg ∙ ((C₀ ▷ s) ∙ rest)) ∙
        isoComp-cong splitN (isoComp-cong (idIso Pg) expandV)
    opaque
      result : before =₂ after
      result = finish ∙ (useNaturality ∙ (isoComp-cong (idIso changed) useRestriction ∙ begin))
  opaque
    comparison :
      (C₁ ∙
        (applyTerm-cong (composeTerm-pre g₀ f₀ s) (idIso (x₀ ∘ s)) ∙
          applyTerm-pre (composeTerm g₀ f₀) x₀ s)) =₂
      ((applyTerm-cong (idIso (g₀ ∘ s)) (applyTerm-pre f₀ x₀ s) ∙
          applyTerm-pre g₀ (applyTerm f₀ x₀) s) ∙ (C₀ ▷ s))
      → (C₂ ∙ applyTerm-cong (composeTerm-cong ag af) b) =₂
        (applyTerm-cong ag (applyTerm-cong af b) ∙ C₁)
      → before =₂ after
    comparison = Calculation.result
```