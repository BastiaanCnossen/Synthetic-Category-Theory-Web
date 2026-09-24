# Projection calculations for the transferred cone comparison

`UniversalConeComparison` contains the construction and its equivalence proof.
This supporting module proves the projection identity used there. Whiskering
an endpoint comparison gives a square of identification families; conjugation
by its two endpoint identifications recovers the required projection.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section03.Parameterized as Parameterized
import SCT.VolumeI.Chapter01.Section03.FamilyNaturality as Naturality

module SCT.VolumeI.Chapter01.Section06.UniversalConeProjectionCalculus
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open Setup 𝒯
open Parameterized vocabulary terminal products productLaws composition vertical
open Naturality vocabulary terminal products productLaws composition vertical whiskering
  using (family-substitution-square-projection)
open import SCT.VolumeI.Chapter01.Section06.ConeIdentificationTransport 𝒯 P

-- A projection of a composite, with all three associators retained.
composite-projection : {A B C D E F : CAT}
  (u : MAP A B) (v : MAP B C) (w : MAP C D)
  (p : MAP C E) (q : MAP D F) (r : MAP B E) (z : MAP E F)
  → (p ∘ v) =₁ r → (q ∘ w) =₁ (z ∘ p)
  → (q ∘ (w ∘ (v ∘ u))) =₁ (z ∘ (r ∘ u))
composite-projection u v w p q r z first second =
  (z ◁ ((first ▷ u) ∙ (comp-assoc u v p) ⁻¹)) ∙
  (comp-assoc (v ∘ u) p z ∙
    ((second ▷ (v ∘ u)) ∙ (comp-assoc (v ∘ u) w q) ⁻¹))

module Projection {U T S : CAT} (l : MAP T U) (h k : MAP S T)
  {B : CAT} (π : MAP U B) (r : MAP T B)
  (b : (π ∘ l) =₁ r) where

  before = (b ▷ h) ∙ (comp-assoc h l π) ⁻¹
  after = (b ▷ k) ∙ (comp-assoc k l π) ⁻¹
  module Conjugate = Conjugation before after
  u = π ◁ postWhisker {f = h} {g = k} l
  v = postWhisker {f = h} {g = k} r

  opaque
    square : (const after ∙ u) =₁ (v ∙ const before)
    square = isoComp-cong (comp-unitʳ v) (idIso (const before)) ∙
      (family-substitution-square-projection π l r b (id (h ＝ k)) ∙
        (isoComp-cong (idIso (const after))
          (postWhisker π ◁ comp-unitʳ (postWhisker l))) ⁻¹)

    normalize : (Conjugate.forward ∘ u) =₁ v
    normalize = right-cancel before v ∙
      (isoComp-cong square (idIso (const (before ⁻¹))) ∙
        ((assoc (const after) u (const (before ⁻¹))) ⁻¹ ∙ Conjugate.evaluate u))

```
