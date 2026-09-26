# Lifting cocones through restriction equivalences

If restriction into the target is an equivalence at each vertex of a
map of spans, it lifts cocones and their comparisons. The comparison
lift retains both prescribed leg images, and reflection of higher
identifications verifies the matching square.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeRestrictionLifting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Decoding.DecodingCalculus 𝒯 M using (decodePre)
open import SCT.VolumeI.Chapter01.Section06.EmbeddingCalculus.EmbeddingCalculus 𝒯 P using (equivalence-isEmbedding)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 using (untransport; reflect-transport-square)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.RestrictionLifting 𝒯 M P using (module Lift)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.RestrictionReflection 𝒯 M using (restriction-reflect-Iso₂)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconeSpanRestriction 𝒯 using (module Restriction)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

module FunctorFactor {A B E : CAT} (i : MAP A B) (ei : IsEquiv (mapPre {D = E} i)) (f : MAP A E) where
  chosen = equiv-lift ei (nameMap f)
  point = FunctorLift.lift chosen
  abstract
    functor : MAP B E
    functor = decodeMap point
    comparison : (functor ∘ i) =₁ f
    comparison = decode-name f ∙ (decodeMapIso (FunctorLift.comparison chosen) ∙ (decodePre i point) ⁻¹)

abstract
  lift-restriction : {A B E : CAT} (i : MAP A B) → IsEquiv (mapPre {D = E} i) →
    (f g : MAP B E) (α : (f ∘ i) =₁ (g ∘ i)) → FunctorLift (preWhisker i) α
  lift-restriction i ei f g α = Lift.factorization i (equivalence-isEmbedding (mapPre i) ei) f g α

module Lifting {A B C A′ B′ C′ E : CAT}
  (u : MAP A B) (v : MAP A C) (u′ : MAP A′ B′) (v′ : MAP A′ C′)
  (i : MAP A A′) (j : MAP B B′) (k : MAP C C′)
  (α : (u′ ∘ i) =₁ (j ∘ u)) (β : (v′ ∘ i) =₁ (k ∘ v))
  (ei : IsEquiv (mapPre {D = E} i)) (ej : IsEquiv (mapPre {D = E} j)) (ek : IsEquiv (mapPre {D = E} k)) where
  module Restrict = Restriction u v u′ v′ i j k α β

  module Factor (s : Cocone u v E) where
    module F = FunctorFactor j ej (Cocone.left s)
    module G = FunctorFactor k ek (Cocone.right s)
    retargeted = coconeRetarget s (F.functor ∘ j) (G.functor ∘ k) (F.comparison ⁻¹) (G.comparison ⁻¹)
    L = Restrict.Left.value F.functor
    R = Restrict.Right.value G.functor
    raw = R ∙ (Cocone.match retargeted ∙ L ⁻¹)
    chosen-match = lift-restriction i ei (F.functor ∘ u′) (G.functor ∘ v′) raw
    value : Cocone u′ v′ E
    value = record { left = F.functor ; right = G.functor ; match = FunctorLift.lift chosen-match }

    abstract
      matching : Cocone.match (Restrict.value value) =₂ Cocone.match retargeted
      matching = untransport L R (Cocone.match retargeted) ∙
        isoComp-cong (idIso (R ⁻¹)) (isoComp-cong (FunctorLift.comparison chosen-match) (idIso L))

      comparison : CoconeIso (Restrict.value value) s
      comparison = coconeIso-compose
        (coconeIso-inverse (coconeRetarget-β s (F.functor ∘ j) (G.functor ∘ k) (F.comparison ⁻¹) (G.comparison ⁻¹)))
        (cocone-match-change _ _ _ _ matching)

  module Compare (s t : Cocone u′ v′ E) (Φ : CoconeIso (Restrict.value s) (Restrict.value t)) where
    chosen-left = lift-restriction j ej (Cocone.left s) (Cocone.left t) (CoconeIso.leftIso Φ)
    chosen-right = lift-restriction k ek (Cocone.right s) (Cocone.right t) (CoconeIso.rightIso Φ)
    δ = FunctorLift.lift chosen-left
    ε = FunctorLift.lift chosen-right
    adjusted = coconeIso-adjust Φ (δ ▷ j) (ε ▷ k) ((FunctorLift.comparison chosen-left) ⁻¹) ((FunctorLift.comparison chosen-right) ⁻¹)
    L₀ = Restrict.Left.value (Cocone.left s)
    L₁ = Restrict.Left.value (Cocone.left t)
    R₀ = Restrict.Right.value (Cocone.right s)
    R₁ = Restrict.Right.value (Cocone.right t)
    τ₀ = Cocone.match s ▷ i
    τ₁ = Cocone.match t ▷ i

    abstract
      normal : (q : Cocone u′ v′ E) →
        ((Restrict.Right.value (Cocone.right q)) ⁻¹ ∙
          ((Cocone.match q ▷ i) ∙ ((Restrict.Left.value (Cocone.left q)) ⁻¹) ⁻¹)) =₂
        Cocone.match (Restrict.value q)
      normal q = isoComp-cong (idIso ((Restrict.Right.value (Cocone.right q)) ⁻¹))
        (isoComp-cong (idIso (Cocone.match q ▷ i)) (inverse-inverse (Restrict.Left.value (Cocone.left q))))

      raw-square : (τ₁ ∙ ((δ ▷ u′) ▷ i)) =₂ (((ε ▷ v′) ▷ i) ∙ τ₀)
      raw-square = reflect-transport-square (L₀ ⁻¹) (L₁ ⁻¹) (R₀ ⁻¹) (R₁ ⁻¹) τ₀ τ₁
        ((δ ▷ u′) ▷ i) ((ε ▷ v′) ▷ i) ((δ ▷ j) ▷ u) ((ε ▷ k) ▷ v)
        (move-square L₁ ((δ ▷ j) ▷ u) ((δ ▷ u′) ▷ i) L₀ (Restrict.Left.natural δ))
        (move-square R₁ ((ε ▷ k) ▷ v) ((ε ▷ v′) ▷ i) R₀ (Restrict.Right.natural ε))
        (isoComp-cong (idIso ((ε ▷ k) ▷ v)) ((normal s) ⁻¹) ∙
          (CoconeIso.compatible adjusted ∙ isoComp-cong (normal t) (idIso ((δ ▷ j) ▷ u))))

      matching : (Cocone.match t ∙ (δ ▷ u′)) =₂ ((ε ▷ v′) ∙ Cocone.match s)
      matching = restriction-reflect-Iso₂ i ei _ _
        ((preWhisker-isoComp-at (ε ▷ v′) (Cocone.match s) i) ⁻¹ ∙
          (raw-square ∙ preWhisker-isoComp-at (Cocone.match t) (δ ▷ u′) i))

    comparison : CoconeIso s t
    comparison = record { leftIso = δ ; rightIso = ε ; compatible = matching }
    left-image : (CoconeIso.leftIso comparison ▷ j) =₂ CoconeIso.leftIso Φ
    left-image = (FunctorLift.comparison chosen-left)
    right-image : (CoconeIso.rightIso comparison ▷ k) =₂ CoconeIso.rightIso Φ
    right-image = (FunctorLift.comparison chosen-right)
```
