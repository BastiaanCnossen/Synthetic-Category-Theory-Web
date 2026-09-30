# The action of a cospan map on whole cones

The expanded matching in `CospanMap.mapCone` is the transported image
of the original matching. Identifying these formulas gives the action
on cone comparisons and its compatibility with parameter restriction.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.Cospans.ConeAction
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectedCones 𝒯

module Action {C D E C′ D′ E′ : CAT}
  {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
  (F : CospanMap f g f′ g′) where
  open CospanMap F renaming
    (left to u; right to v; base to w; leftSquare to α; rightSquare to β)
  module Normal = Coordinate f g f′ g′ u v w (α ⁻¹) (β ⁻¹)
    using (left-normal; right-normal; left-natural; right-natural; read; read-iso; read-pre)

  left-inverse : {T : CAT} (p : MAP T C) →
    (Normal.left-normal p) ⁻¹ =₂
      (comp-assoc p f w ∙ ((α ▷ p) ∙ (comp-assoc p u f′) ⁻¹))
  left-inverse p = isoComp-assoc-at A (α ▷ p) (B ⁻¹) ∙
    (isoComp-cong
      (isoComp-cong (inverse-inverse A)
        (inverse-inverse (α ▷ p) ∙ (＝-inv ◁ pre-inverse α p)) ∙
        inverse-composite (α ⁻¹ ▷ p) (A ⁻¹))
      (idIso (B ⁻¹)) ∙ inverse-composite B ((α ⁻¹ ▷ p) ∙ A ⁻¹))
    where
    A = comp-assoc p f w
    B = comp-assoc p u f′

  normalization : {T : CAT} (s : Cone f g T) →
    Cone.match (mapCone s) =₂ Cone.match (Normal.read s)
  normalization s =
    isoComp-cong (idIso (Normal.right-normal q))
      (isoComp-cong (idIso (w ◁ τ)) ((left-inverse p) ⁻¹)) ∙
    ((isoComp-assoc-at A (B ∙ dPath) tail) ⁻¹ ∙
      isoComp-cong (idIso A) ((isoComp-assoc-at B dPath tail) ⁻¹))
    where
    p = Cone.left s
    q = Cone.right s
    τ = Cone.match s
    A = comp-assoc q v g′
    B = β ⁻¹ ▷ q
    dPath = (comp-assoc q g w) ⁻¹
    tail = (w ◁ τ) ∙ (comp-assoc p f w ∙ ((α ▷ p) ∙ (comp-assoc p u f′) ⁻¹))

  comparison : {T : CAT} (s : Cone f g T) → ConeIso (mapCone s) (Normal.read s)
  comparison s = cone-match-change _ _ _ _ (normalization s)

  map-iso : {T : CAT} {s t : Cone f g T} → ConeIso s t → ConeIso (mapCone s) (mapCone t)
  map-iso {s = s} {t} Φ = coneIso-compose (coneIso-inverse (comparison t))
    (coneIso-compose (Normal.read-iso Φ) (comparison s))

  map-pre : {S T : CAT} (r : MAP S T) (s : Cone f g T) →
    ConeIso (mapCone (conePre r s)) (conePre r (mapCone s))
  map-pre r s = coneIso-compose (coneIso-pre r (coneIso-inverse (comparison s)))
    (coneIso-compose (Normal.read-pre r s) (comparison (conePre r s)))


  map-iso-with-legs : {T : CAT} {s t : Cone f g T} → ConeIso s t → ConeIso (mapCone s) (mapCone t)
  map-iso-with-legs {s = s} {t} Φ = coneIso-adjust (map-iso Φ)
    (u ◁ ConeIso.leftIso Φ) (v ◁ ConeIso.rightIso Φ)
    (isoComp-unitˡ-at _ ∙ isoComp-cong (inverse-identity (u ∘ Cone.left t)) (isoComp-unitʳ-at _))
    (isoComp-unitˡ-at _ ∙ isoComp-cong (inverse-identity (v ∘ Cone.right t)) (isoComp-unitʳ-at _))

  map-pre-with-legs : {S T : CAT} (r : MAP S T) (s : Cone f g T) →
    ConeIso (mapCone (conePre r s)) (conePre r (mapCone s))
  map-pre-with-legs r s = coneIso-adjust (map-pre r s)
    ((comp-assoc r (Cone.left s) u) ⁻¹) ((comp-assoc r (Cone.right s) v) ⁻¹)
    (isoComp-unitˡ-at _ ∙ isoComp-cong
      (preWhisker-idIso (u ∘ Cone.left s) r ∙ (preWhisker r ◁ inverse-identity (u ∘ Cone.left s)))
      (isoComp-unitʳ-at _))
    (isoComp-unitˡ-at _ ∙ isoComp-cong
      (preWhisker-idIso (v ∘ Cone.right s) r ∙ (preWhisker r ◁ inverse-identity (v ∘ Cone.right s)))
      (isoComp-unitʳ-at _))
```
