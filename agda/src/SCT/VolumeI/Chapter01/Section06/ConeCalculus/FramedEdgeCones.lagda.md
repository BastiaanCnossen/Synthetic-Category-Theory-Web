# Framed edge cones

Expanding a specified factorization of a cospan arrow gives an edge
cone. Its matching keeps the factorization comparison and associator.
The construction respects entire cone comparisons and parameter
restriction. These operations support pasting without discarding the
matching of the original square.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section06.ConeCalculus.FramedEdgeCones
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 public
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CompositeCones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeArrowChange 𝒯
  using (changeLeft; changeLeft-iso; changeLeft-pre; cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
  using (inverse-inverse; pre-inverse; inverse-identity)

module At {W Y B A : CAT} (r : MAP W Y) (b : MAP Y B) {c₀ : MAP W B}
  (κ : (b ∘ r) =₁ c₀) (f : MAP A B) where
  edge : {V : CAT} → Cone c₀ f V → Cone b f V
  edge q = record { left = r ∘ Cone.left q ; right = Cone.right q
    ; match = Cone.match q ∙ ((κ ▷ Cone.left q) ∙ (comp-assoc (Cone.left q) r b) ⁻¹) }

  raw : {V : CAT} → Cone c₀ f V → Cone b f V
  raw q = compositeCone r b (changeLeft (κ ⁻¹) q)

  normalized : {V : CAT} (q : Cone c₀ f V) → ConeIso (raw q) (edge q)
  normalized q = cone-match-change _ _ _ _
    (isoComp-assoc-at (Cone.match q) (κ ▷ Cone.left q) ((comp-assoc (Cone.left q) r b) ⁻¹) ∙
      isoComp-cong
        (isoComp-cong (idIso (Cone.match q))
          (inverse-inverse (κ ▷ Cone.left q) ∙ (＝-inv ◁ pre-inverse κ (Cone.left q))))
        (idIso ((comp-assoc (Cone.left q) r b) ⁻¹)))

  action : {V : CAT} {q q′ : Cone c₀ f V} → ConeIso q q′ → ConeIso (edge q) (edge q′)
  action {q = q} {q′} Φ = coneIso-compose (normalized q′)
    (coneIso-compose (compositeConeIso r b (changeLeft-iso (κ ⁻¹) Φ))
      (coneIso-inverse (normalized q)))

  restrict : {U V : CAT} (u : MAP U V) (q : Cone c₀ f V) →
    ConeIso (conePre u (edge q)) (edge (conePre u q))
  restrict u q = coneIso-compose (normalized (conePre u q))
    (coneIso-compose (compositeConeIso r b (changeLeft-pre (κ ⁻¹) u q))
      (coneIso-compose (compositeCone-pre r b u (changeLeft (κ ⁻¹) q))
        (coneIso-pre u (coneIso-inverse (normalized q)))))


  action-with-legs : {V : CAT} {q q′ : Cone c₀ f V} → ConeIso q q′ → ConeIso (edge q) (edge q′)
  action-with-legs {q = q} Φ = coneIso-adjust (action Φ) (r ◁ ConeIso.leftIso Φ) (ConeIso.rightIso Φ)
    (isoComp-unitˡ-at (r ◁ ConeIso.leftIso Φ) ∙
      isoComp-cong (idIso _) (isoComp-unitʳ-at (r ◁ ConeIso.leftIso Φ) ∙
        isoComp-cong (idIso _) (inverse-identity (r ∘ Cone.left q))))
    (isoComp-unitˡ-at (ConeIso.rightIso Φ) ∙
      isoComp-cong (idIso _) (isoComp-unitʳ-at (ConeIso.rightIso Φ) ∙
        isoComp-cong (idIso _) (inverse-identity (Cone.right q))))

  restrict-with-legs : {U V : CAT} (u : MAP U V) (q : Cone c₀ f V) →
    ConeIso (conePre u (edge q)) (edge (conePre u q))
  restrict-with-legs u q = coneIso-adjust (restrict u q)
    (comp-assoc u (Cone.left q) r) (idIso (Cone.right q ∘ u)) left-normal right-normal
    where
    associator = comp-assoc u (Cone.left q) r
    left-unit = preWhisker-idIso (r ∘ Cone.left q) u ∙
      (preWhisker u ◁ inverse-identity (r ∘ Cone.left q))
    right-unit = preWhisker-idIso (Cone.right q) u ∙
      (preWhisker u ◁ inverse-identity (Cone.right q))
    left-normal = isoComp-unitˡ-at associator ∙
      isoComp-cong (idIso _) (isoComp-unitˡ-at associator ∙
        isoComp-cong (postWhisker-idIso r (Cone.left q ∘ u))
          (isoComp-unitʳ-at associator ∙ isoComp-cong (idIso associator) left-unit))
    right-normal = isoComp-unitˡ-at _ ∙
      isoComp-cong (idIso _) (isoComp-unitˡ-at _ ∙
        isoComp-cong (idIso _) (isoComp-unitˡ-at _ ∙
          isoComp-cong (idIso _) right-unit))
```
