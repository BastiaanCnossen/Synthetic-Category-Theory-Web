# Normalizing a nested application after restriction

The following pasting is stated for arbitrary terms and endpoint
comparisons. It uses the supplied restriction square for application of
composition and the already proved naturality of that application.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section03.MappingProofCalculus as MappingProof
import SCT.VolumeI.Chapter01.Section03.CompositionRestrictionCalculus as Restriction

module SCT.VolumeI.Chapter01.Section03.NestedApplicationRestriction
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
  (ag : =₁ (g₀ ∘ s) g′) (af : =₁ (f₀ ∘ s) f′) (b : =₁ (x₀ ∘ s) x′)
  {K : MAP Γ (Map C E)} (d : =₁ K (composeTerm g₀ f₀))
  {S : MAP Γ E} {T : MAP R E}
  (A₀ : =₁ S (applyTerm K x₀)) (B₀ : =₁ T (S ∘ s))
  (C₀ : =₁ (applyTerm (composeTerm g₀ f₀) x₀) (applyTerm g₀ (applyTerm f₀ x₀)))
  (C₁ : =₁ (applyTerm (composeTerm (g₀ ∘ s) (f₀ ∘ s)) (x₀ ∘ s))
    (applyTerm (g₀ ∘ s) (applyTerm (f₀ ∘ s) (x₀ ∘ s))))
  (C₂ : =₁ (applyTerm (composeTerm g′ f′) x′) (applyTerm g′ (applyTerm f′ x′))) where

  source-coordinate = composeTerm-cong ag af ∙
    (composeTerm-pre g₀ f₀ s ∙ (d ▷ s))
  before = applyTerm-cong ag (applyTerm-cong af b ∙ applyTerm-pre f₀ x₀ s) ∙
    (applyTerm-pre g₀ (applyTerm f₀ x₀) s ∙
      (((C₀ ∙ (applyTerm-cong d (idIso x₀) ∙ A₀)) ▷ s) ∙ B₀))
  after = C₂ ∙
    (applyTerm-cong source-coordinate b ∙
      (applyTerm-pre K x₀ s ∙ ((A₀ ▷ s) ∙ B₀)))

  module Calculation
    (restriction : =₂
      (C₁ ∙ (applyTerm-cong (composeTerm-pre g₀ f₀ s) (idIso (x₀ ∘ s)) ∙
        applyTerm-pre (composeTerm g₀ f₀) x₀ s))
      ((applyTerm-cong (idIso (g₀ ∘ s)) (applyTerm-pre f₀ x₀ s) ∙
          applyTerm-pre g₀ (applyTerm f₀ x₀) s) ∙ (C₀ ▷ s)))
    (naturality : =₂ (C₂ ∙ applyTerm-cong (composeTerm-cong ag af) b)
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
      expandV : =₂ (((C₀ ∙ (D₀ ∙ A₀)) ▷ s) ∙ B₀) ((C₀ ▷ s) ∙ rest)
      expandV = isoComp-cong (idIso (C₀ ▷ s)) (isoComp-assoc-at (D₀ ▷ s) (A₀ ▷ s) B₀) ∙
        (isoComp-assoc-at (C₀ ▷ s) ((D₀ ▷ s) ∙ (A₀ ▷ s)) B₀ ∙
          isoComp-cong
            (isoComp-cong (idIso (C₀ ▷ s)) (preWhisker-isoComp-at D₀ A₀ s) ∙
              preWhisker-isoComp-at C₀ (D₀ ∙ A₀) s) (idIso B₀))
    opaque
      splitN : =₂ N (changed ∙ restricted)
      splitN = apply-cong-comp ag (idIso (g₀ ∘ s)) (applyTerm-cong af b) Pf ∙
        invIso (apply-cong-Iso₂ (isoComp-unitʳ-at ag) (idIso (applyTerm-cong af b ∙ Pf)))
    opaque
      useRestriction : =₂ (restricted ∙ (Pg ∙ ((C₀ ▷ s) ∙ rest))) (C₁ ∙ (middle-route ∙ rest))
      useRestriction = isoComp-assoc-at C₁ middle-route rest ∙
        (isoComp-cong (invIso restriction) (idIso rest) ∙
          (invIso (isoComp-assoc-at (restricted ∙ Pg) (C₀ ▷ s) rest) ∙
            invIso (isoComp-assoc-at restricted Pg ((C₀ ▷ s) ∙ rest))))
    opaque
      useNaturality : =₂ (changed ∙ (C₁ ∙ (middle-route ∙ rest))) (C₂ ∙ (Qact ∙ (middle-route ∙ rest)))
      useNaturality = isoComp-assoc-at C₂ Qact (middle-route ∙ rest) ∙
        (isoComp-cong (invIso naturality) (idIso (middle-route ∙ rest)) ∙
          invIso (isoComp-assoc-at changed C₁ (middle-route ∙ rest)))
    opaque
      projectionNatural : =₂ (Pmid ∙ (D₀ ▷ s)) (Uact ∙ Psource)
      projectionNatural = isoComp-cong
          (apply-cong-Iso₂ (idIso (d ▷ s)) (preWhisker-idIso x₀ s)) (idIso Psource) ∙
        binary-pre-inputs mapEval d (idIso x₀) s
    opaque
      exchange : =₂ (Pmid ∙ rest) (Uact ∙ base)
      exchange = isoComp-assoc-at Uact Psource tail ∙
        (isoComp-cong projectionNatural (idIso tail) ∙
          invIso (isoComp-assoc-at Pmid (D₀ ▷ s) tail))
    opaque
      useProjection : =₂ (middle-route ∙ rest) (Ract ∙ (Uact ∙ base))
      useProjection = isoComp-cong (idIso Ract) exchange ∙
        isoComp-assoc-at Ract Pmid rest
    opaque
      combineInner : =₂ (Ract ∙ (Uact ∙ base)) (applyTerm-cong (e ∙ (d ▷ s)) (idIso (x₀ ∘ s)) ∙ base)
      combineInner = isoComp-cong
          (apply-cong-Iso₂ (idIso (e ∙ (d ▷ s))) (isoComp-unitˡ-at (idIso (x₀ ∘ s))))
          (idIso base) ∙
        combine-apply e (idIso (x₀ ∘ s)) (d ▷ s) (idIso (x₀ ∘ s)) base
    opaque
      combineOuter : =₂ (Qact ∙ (applyTerm-cong (e ∙ (d ▷ s)) (idIso (x₀ ∘ s)) ∙ base)) (applyTerm-cong source-coordinate b ∙ base)
      combineOuter = isoComp-cong
          (apply-cong-Iso₂ (idIso source-coordinate) (isoComp-unitʳ-at b)) (idIso base) ∙
        combine-apply (composeTerm-cong ag af) b (e ∙ (d ▷ s)) (idIso (x₀ ∘ s)) base
    opaque
      finish : =₂ (C₂ ∙ (Qact ∙ (middle-route ∙ rest))) after
      finish = isoComp-cong (idIso C₂)
        (combineOuter ∙
          isoComp-cong (idIso Qact) (combineInner ∙ useProjection))
    opaque
      begin : =₂ before (changed ∙ (restricted ∙ (Pg ∙ ((C₀ ▷ s) ∙ rest))))
      begin = isoComp-assoc-at changed restricted (Pg ∙ ((C₀ ▷ s) ∙ rest)) ∙
        isoComp-cong splitN (isoComp-cong (idIso Pg) expandV)
    opaque
      result : =₂ before after
      result = finish ∙ (useNaturality ∙ (isoComp-cong (idIso changed) useRestriction ∙ begin))
  opaque
    comparison : =₂
      (C₁ ∙
        (applyTerm-cong (composeTerm-pre g₀ f₀ s) (idIso (x₀ ∘ s)) ∙
          applyTerm-pre (composeTerm g₀ f₀) x₀ s))
      ((applyTerm-cong (idIso (g₀ ∘ s)) (applyTerm-pre f₀ x₀ s) ∙
          applyTerm-pre g₀ (applyTerm f₀ x₀) s) ∙ (C₀ ▷ s))
      → =₂ (C₂ ∙ applyTerm-cong (composeTerm-cong ag af) b)
        (applyTerm-cong ag (applyTerm-cong af b) ∙ C₁)
      → =₂ before after
    comparison = Calculation.result
```