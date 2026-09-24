# Restriction of isomorphisms along the coproduct inclusions

The restriction functor is an equivalence on the entire isomorphism
anima. We first decode the corresponding statement for mapping animae,
then transport its endpoints to the given functors.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts

module SCT.VolumeI.Chapter01.Section05.IsomorphismRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Coproducts.CoproductStructure B
open import SCT.VolumeI.Chapter01.Section05.RestrictionCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section04.DecodingNaturality 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.CoherenceTransport 𝒯

coproductIsoRestriction : {C D E : CAT} (h k : MAP (C ⊔ D) E) →
  MAP (h ＝ k) (((h ∘ in₁) ＝ (k ∘ in₁)) × ((h ∘ in₂) ＝ (k ∘ in₂)))
coproductIsoRestriction h k = pair (preWhisker in₁) (preWhisker in₂)

decode-restriction-square : {C D E : CAT} (i : MAP C D) (u v : Obj-abs (Map D E)) →

    (const (decodePre i v) ∙ (decodeMap-isoMap (mapPre i ∘ u) (mapPre i ∘ v) ∘ postWhisker (mapPre i))) =₁
    ((preWhisker i ∘ decodeMap-isoMap u v) ∙ const (decodePre i u))
decode-restriction-square i u v =
  isoComp-cong (preWhisker i ◁ comp-unitʳ (decodeMap-isoMap u v)) (idIso (const (decodePre i u))) ∙
    (decodePre-natural i (id (u ＝ v)) ∙
      isoComp-cong (idIso (const (decodePre i v)))
        (decodeMap-isoMap _ _ ◁ (comp-unitʳ (postWhisker (mapPre i))) ⁻¹))

decoded-restriction-isEquiv : {C D E : CAT} (u v : Obj-abs (Map (C ⊔ D) E)) →
  IsEquiv (coproductIsoRestriction (decodeMap u) (decodeMap v))
decoded-restriction-isEquiv {C} {D} {E} u v =
  equiv-cancel-right (decodeMap-isoMap u v) (coproductIsoRestriction (decodeMap u) (decodeMap v))
    (decodeMap-isoMap-isEquiv u v)
    (equiv-transport ((pair-pre (preWhisker in₁) (preWhisker in₂) (decodeMap-isoMap u v)) ⁻¹)
      (pair-squares-isEquiv (decodePre in₁ u) (decodePre in₁ v) (decodePre in₂ u) (decodePre in₂ v)
        (D₁ ∘ postWhisker F) (D₂ ∘ postWhisker G)
        (preWhisker in₁ ∘ decodeMap-isoMap u v) (preWhisker in₂ ∘ decodeMap-isoMap u v)
        (decode-restriction-square in₁ u v) (decode-restriction-square in₂ u v)
        (pair-after-isEquiv D₁ D₂ (postWhisker F) (postWhisker G)
          (decodeMap-isoMap-isEquiv (F ∘ u) (F ∘ v)) (decodeMap-isoMap-isEquiv (G ∘ u) (G ∘ v))
          (paired-post-isEquiv F G (coproductRestriction-isEquiv C D E) u v))))
  where
  F = mapPre (in₁ {C} {D})
  G = mapPre (in₂ {C} {D})
  D₁ = decodeMap-isoMap (F ∘ u) (F ∘ v)
  D₂ = decodeMap-isoMap (G ∘ u) (G ∘ v)

restriction-change-square : {A C D : CAT} {f f′ g g′ : MAP C D}
  (i : MAP A C) (p : f =₁ f′) (q : g =₁ g′) →
  (const (q ▷ i) ∙ preWhisker i) =₁
    ((preWhisker i ∘ changeEndpoints-map p q) ∙ const (p ▷ i))
restriction-change-square {f = f} {g = g} i p q =
  pre-family-square i p q (id (f ＝ g)) (changeEndpoints-map p q)
    (isoComp-cong (comp-unitʳ (changeEndpoints-map p q)) (idIso (const p)) ∙
      change-map-square p q (id (f ＝ g))) ∙
    isoComp-cong (idIso (const (q ▷ i))) ((comp-unitʳ (preWhisker i)) ⁻¹)

coproductIsoRestriction-isEquiv : {C D E : CAT} (h k : MAP (C ⊔ D) E) →
  IsEquiv (coproductIsoRestriction h k)
coproductIsoRestriction-isEquiv h k = equiv-cancel-right change (coproductIsoRestriction h k)
  (changeEndpoints-map-isEquiv p q)
  (equiv-transport ((pair-pre (preWhisker in₁) (preWhisker in₂) change) ⁻¹)
    (pair-squares-isEquiv (p ▷ in₁) (q ▷ in₁) (p ▷ in₂) (q ▷ in₂)
      (preWhisker in₁) (preWhisker in₂) (preWhisker in₁ ∘ change) (preWhisker in₂ ∘ change)
      (restriction-change-square in₁ p q) (restriction-change-square in₂ p q)
      (decoded-restriction-isEquiv (nameMap h) (nameMap k))))
  where
  p = decode-name h
  q = decode-name k
  change = changeEndpoints-map p q

module RestrictionLift {C D E : CAT} (h k : MAP (C ⊔ D) E)
  (α : (h ∘ in₁) =₁ (k ∘ in₁)) (β : (h ∘ in₂) =₁ (k ∘ in₂)) where

  chosen = equiv-lift (coproductIsoRestriction-isEquiv h k) (pair α β)

  abstract
    lift : h =₁ k
    lift = FunctorLift.lift chosen

    image : (coproductIsoRestriction h k ∘ lift) =₁ (pair α β)
    image = FunctorLift.comparison chosen

  left-image : (lift ▷ in₁) =₂ α
  left-image = pair-β₁ α β ∙ ((pr₁ ◁ image) ∙
    (project-pair₁ (preWhisker in₁) (preWhisker in₂) lift) ⁻¹)

  right-image : (lift ▷ in₂) =₂ β
  right-image = pair-β₂ α β ∙ ((pr₂ ◁ image) ∙
    (project-pair₂ (preWhisker in₁) (preWhisker in₂) lift) ⁻¹)
```
