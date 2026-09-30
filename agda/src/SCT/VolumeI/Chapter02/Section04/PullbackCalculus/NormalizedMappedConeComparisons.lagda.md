# Evaluated comparisons with explicit endpoint frames

The coordinate form of an evaluated mapped-cone comparison has the
prescribed evaluated leg isomorphisms followed by inverse evaluation
frames. Retaining this computation lets subsequent pasting arguments
use those same witnesses without expanding the cospan action.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter02.Section04.PullbackCalculus.NormalizedMappedConeComparisons
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
  using (inverse-inverse; inverse-composite; pre-inverse)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.MappedCones 𝒯 M ℱ P
  using (mappedCone)
import SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectedCones as Coordinates
import SCT.VolumeI.Chapter02.Section04.PullbackCalculus.MappedEvaluationCones as Mapped

module At {T C D E X Γ : CAT} {f : MAP C E} {g : MAP D E}
  (v : Obj-abs T) (s : Cone f g X) (F : MAP Γ (Fun T X))
  (q : Cone (funPost {C = T} f) (funPost g) Γ)
  (Φ : ConeIso (conePre F (mappedCone T s)) q) where
  module Read = Coordinates.Coordinate 𝒯 (funPost f) (funPost g) f g
    (evaluate v) (evaluate v) (evaluate v) (evaluate-post v f) (evaluate-post v g)
    using (read; read-iso; read-pre)
  module Known = Mapped.MappedAt 𝒯 M ℱ P v s using (comparison)

  raw : ConeIso (conePre (evaluate v ∘ F) s) (Read.read q)
  raw = coneIso-compose (Read.read-iso Φ)
    (coneIso-compose (coneIso-inverse (Read.read-pre F (mappedCone T s)))
      (coneIso-compose (coneIso-pre F (coneIso-inverse Known.comparison))
        (coneIso-inverse (conePre-assoc F (evaluate v) s))))

  abstract
    frame-inverse : {Y : CAT} (u : MAP X Y) →
      (((comp-assoc F (funPost u) (evaluate v)) ⁻¹) ⁻¹ ∙
        (((evaluate-post v u) ⁻¹ ▷ F) ∙ (comp-assoc F (evaluate v) u) ⁻¹)) =₂
      (evaluate-post-at v u F) ⁻¹
    frame-inverse u = (inverse-composite a₁ (b₁ ∙ d₁ ⁻¹)) ⁻¹ ∙
      isoComp-cong (inverse-composite b₁ (d₁ ⁻¹) ⁻¹)
        (idIso (a₁ ⁻¹)) ∙
      (isoComp-assoc-at ((d₁ ⁻¹) ⁻¹) (b₁ ⁻¹) (a₁ ⁻¹)) ⁻¹ ∙
      isoComp-cong (idIso ((d₁ ⁻¹) ⁻¹))
        (isoComp-cong (pre-inverse (evaluate-post v u) F) (idIso (a₁ ⁻¹)))
      where
      a₁ : ((u ∘ evaluate v) ∘ F) =₁ (u ∘ (evaluate v ∘ F))
      a₁ = comp-assoc F (evaluate v) u
      b₁ : ((evaluate v ∘ funPost u) ∘ F) =₁ ((u ∘ evaluate v) ∘ F)
      b₁ = evaluate-post v u ▷ F
      d₁ : ((evaluate v ∘ funPost u) ∘ F) =₁ (evaluate v ∘ (funPost u ∘ F))
      d₁ = comp-assoc F (funPost u) (evaluate v)

    left-frame : ConeIso.leftIso raw =₂
      ((evaluate v ◁ ConeIso.leftIso Φ) ∙ (evaluate-post-at v (Cone.left s) F) ⁻¹)
    left-frame = isoComp-cong (idIso (evaluate v ◁ ConeIso.leftIso Φ)) (frame-inverse (Cone.left s))

    right-frame : ConeIso.rightIso raw =₂
      ((evaluate v ◁ ConeIso.rightIso Φ) ∙ (evaluate-post-at v (Cone.right s) F) ⁻¹)
    right-frame = isoComp-cong (idIso (evaluate v ◁ ConeIso.rightIso Φ)) (frame-inverse (Cone.right s))

  comparison : ConeIso (conePre (evaluate v ∘ F) s) (Read.read q)
  comparison = coneIso-adjust raw
    ((evaluate v ◁ ConeIso.leftIso Φ) ∙ (evaluate-post-at v (Cone.left s) F) ⁻¹)
    ((evaluate v ◁ ConeIso.rightIso Φ) ∙ (evaluate-post-at v (Cone.right s) F) ⁻¹)
    left-frame right-frame
```
