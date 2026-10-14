# Changing an evaluated separation square

Changing the two object coordinates and identifying the evaluator carries
an evaluated separation square to the changed route. The proof retains
the two chosen coordinate comparisons and the square between them.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.EvaluatedSeparationChange
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 public
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 using (post-square)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Naturality
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open Naturality vocabulary terminal products productLaws composition vertical whiskering using (move-square)
open Structural vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at; postWhisker-comp-at)

module At {A B D E : CAT} (σ : MAP A B) (j z : MAP A A) (k v : MAP B B)
  (δ : j =₁ z) (ε : k =₁ v) (S : (k ∘ σ) =₁ (σ ∘ j)) (ν : (v ∘ σ) =₁ (σ ∘ z))
  (square : (ν ∙ (ε ▷ σ)) =₂ ((σ ◁ δ) ∙ S)) (d : MAP B E)
  (W : MAP A D) (e : MAP D E) (β : (d ∘ σ) =₁ (e ∘ W))
  {P : MAP A D} (χ : (W ∘ z) =₁ P) where
  prefix = (comp-assoc j σ d) ⁻¹ ∙ ((d ◁ S) ∙ comp-assoc σ k d)
  changed = (comp-assoc z σ d) ⁻¹ ∙ ((d ◁ ν) ∙ comp-assoc σ v d)
  n′ = (e ◁ χ) ∙ (comp-assoc z W e ∙ (β ▷ z))
  n = (e ◁ (χ ∙ (W ◁ δ))) ∙ (comp-assoc j W e ∙ (β ▷ j))
  Ξ = n′ ∙ changed

  abstract
    inner : (((d ◁ ν) ∙ comp-assoc σ v d) ∙ ((d ◁ ε) ▷ σ)) =₂
      ((d ◁ (σ ◁ δ)) ∙ ((d ◁ S) ∙ comp-assoc σ k d))
    inner = paste-squares (comp-assoc σ k d) (comp-assoc σ v d) (d ◁ S) (d ◁ ν)
      ((d ◁ ε) ▷ σ) (d ◁ (ε ▷ σ)) (d ◁ (σ ◁ δ))
      (whisker-mixed-at ε σ d) (post-square d S ν (ε ▷ σ) (σ ◁ δ) square)

    coordinate-change : (changed ∙ ((d ◁ ε) ▷ σ)) =₂ (((d ∘ σ) ◁ δ) ∙ prefix)
    coordinate-change = paste-squares ((d ◁ S) ∙ comp-assoc σ k d) ((d ◁ ν) ∙ comp-assoc σ v d)
      ((comp-assoc j σ d) ⁻¹) ((comp-assoc z σ d) ⁻¹)
      ((d ◁ ε) ▷ σ) (d ◁ (σ ◁ δ)) ((d ∘ σ) ◁ δ) inner
      (move-square (comp-assoc z σ d) ((d ∘ σ) ◁ δ) (d ◁ (σ ◁ δ)) (comp-assoc j σ d)
        (postWhisker-comp-at δ σ d))

    evaluation-change : (n′ ∙ ((d ∘ σ) ◁ δ)) =₂ n
    evaluation-change = isoComp-cong ((postWhisker-isoComp-at e χ (W ◁ δ)) ⁻¹)
        (idIso (comp-assoc j W e ∙ (β ▷ j))) ∙
      (isoComp-assoc-at (e ◁ χ) (e ◁ (W ◁ δ)) (comp-assoc j W e ∙ (β ▷ j))) ⁻¹ ∙
      isoComp-cong (idIso (e ◁ χ)) (isoComp-assoc-at (e ◁ (W ◁ δ)) (comp-assoc j W e) (β ▷ j)) ∙
      isoComp-cong (idIso (e ◁ χ)) (isoComp-cong (postWhisker-comp-at δ W e) (idIso (β ▷ j))) ∙
      isoComp-cong (idIso (e ◁ χ)) ((isoComp-assoc-at (comp-assoc z W e) ((e ∘ W) ◁ δ) (β ▷ j)) ⁻¹) ∙
      isoComp-cong (idIso (e ◁ χ)) (isoComp-cong (idIso (comp-assoc z W e)) (interchange-at β δ)) ∙
      isoComp-cong (idIso (e ◁ χ)) (isoComp-assoc-at (comp-assoc z W e) (β ▷ z) ((d ∘ σ) ◁ δ)) ∙
      isoComp-assoc-at (e ◁ χ) (comp-assoc z W e ∙ (β ▷ z)) ((d ∘ σ) ◁ δ)

    combined : (Ξ ∙ ((d ◁ ε) ▷ σ)) =₂ (n ∙ prefix)
    combined = isoComp-cong evaluation-change (idIso prefix) ∙
      (isoComp-assoc-at n′ ((d ∘ σ) ◁ δ) prefix) ⁻¹ ∙
      isoComp-cong (idIso n′) coordinate-change ∙
      isoComp-assoc-at n′ changed ((d ◁ ε) ▷ σ)

    append : {T : MAP B E} (leading : T =₁ (d ∘ k)) →
      (n ∙ (prefix ∙ (leading ▷ σ))) =₂ (Ξ ∙ (((d ◁ ε) ∙ leading) ▷ σ))
    append leading = isoComp-cong (idIso Ξ) ((preWhisker-isoComp-at (d ◁ ε) leading σ) ⁻¹) ∙
      isoComp-assoc-at Ξ ((d ◁ ε) ▷ σ) (leading ▷ σ) ∙
      isoComp-cong (combined ⁻¹) (idIso (leading ▷ σ)) ∙
      (isoComp-assoc-at n prefix (leading ▷ σ)) ⁻¹
```
