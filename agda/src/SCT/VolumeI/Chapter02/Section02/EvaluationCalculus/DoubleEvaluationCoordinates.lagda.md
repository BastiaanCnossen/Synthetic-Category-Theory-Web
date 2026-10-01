# The coordinate square after double evaluation

Changing both axis comparisons and evaluating the coordinate permutation
preserves its specified corner. The two external associators are part of
the comparison, so this statement can be pasted with curry beta equations.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.DoubleEvaluationCoordinates
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ public
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SquareEvaluation 𝒯 M using (evaluate-square)
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SquareEvaluationPostcomposition as Post
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareParameterCorner as Corner
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 using (post-square)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square; cancel-left-reflect)
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open Structural vocabulary terminal products productLaws composition whiskering using (whisker-mixed-at)

change-axes : {X Y K L C : CAT} (e : MAP L C) (f : MAP X Y) (i : MAP X K)
  {F F′ : MAP K L} {j j′ : MAP Y L} (p : j =₁ j′) (q : F =₁ F′)
  (α : (j ∘ f) =₁ (F ∘ i)) (β : (j′ ∘ f) =₁ (F′ ∘ i)) →
  (β ∙ (p ▷ f)) =₂ ((q ▷ i) ∙ α) →
  (evaluate-square e f F′ i j′ β ∙ ((e ◁ p) ▷ f)) =₂
    (((e ◁ q) ▷ i) ∙ evaluate-square e f F i j α)
change-axes e f i {F} {F′} {j} {j′} p q α β square = paste-squares
  ((e ◁ α) ∙ comp-assoc f j e) ((e ◁ β) ∙ comp-assoc f j′ e)
  ((comp-assoc i F e) ⁻¹) ((comp-assoc i F′ e) ⁻¹)
  ((e ◁ p) ▷ f) (e ◁ (q ▷ i)) ((e ◁ q) ▷ i)
  (paste-squares (comp-assoc f j e) (comp-assoc f j′ e) (e ◁ α) (e ◁ β)
    ((e ◁ p) ▷ f) (e ◁ (p ▷ f)) (e ◁ (q ▷ i))
    (whisker-mixed-at p f e) (post-square e α β (p ▷ f) (q ▷ i) square))
  (move-square (comp-assoc i F′ e) ((e ◁ q) ▷ i) (e ◁ (q ▷ i))
    (comp-assoc i F e) (whisker-mixed-at q i e))

module At {Γ A B C : CAT} (h : MAP (Γ × (A × B)) C)
  (u : Obj-abs A) (v : Obj-abs B) where
  module K = Corner.At 𝒯 M ℱ Γ A B u v
  module H = K.H
  module V = K.V
  J = K.J
  ia = K.ia
  ib = K.ib
  χ = K.χ
  E₀ = evaluate-square J ib V.step ia H.step χ
  E₁ = evaluate-square h ib (J ∘ V.step) ia (J ∘ H.step) E₀
  E₂ = evaluate-square (h ∘ J) ib V.step ia H.step χ
  result = evaluate-square h ib V.restriction ia H.restriction K.matching
  module P = Post.At 𝒯 M J h ib V.step ia H.step χ
    using (J₀; V; comparison)
  left-associator = comp-assoc H.step J h ▷ ib
  right-associator = comp-assoc V.step J h ▷ ia
  p = H.comparison ▷ ib
  q = V.comparison ▷ ia

  abstract
    matching-normal : K.matching =₂ (q ∙ (E₀ ∙ p ⁻¹))
    matching-normal = isoComp-cong (idIso q)
      ((isoComp-assoc-at K.fourth (K.third ∙ K.second) (p ⁻¹)) ⁻¹ ∙
        isoComp-cong (idIso K.fourth) ((isoComp-assoc-at K.third K.second (p ⁻¹)) ⁻¹))

    matching-square : (K.matching ∙ p) =₂ (q ∙ E₀)
    matching-square = isoComp-cong (idIso q) (cancel-inverse-tail E₀ p) ∙
      isoComp-assoc-at q (E₀ ∙ p ⁻¹) p ∙ isoComp-cong matching-normal (idIso p)

    axes : (result ∙ ((h ◁ H.comparison) ▷ ib)) =₂ (((h ◁ V.comparison) ▷ ia) ∙ E₁)
    axes = change-axes h ib ia H.comparison V.comparison E₀ K.matching matching-square

    permutation : (E₁ ∙ left-associator) =₂ (right-associator ∙ E₂)
    permutation = cancel-left-reflect P.V
      (isoComp-assoc-at P.V right-associator E₂ ∙ P.comparison ∙
        isoComp-assoc-at (h ◁ E₀) P.J₀ left-associator ∙
        isoComp-cong (cancel-inverse P.V ((h ◁ E₀) ∙ P.J₀)) (idIso left-associator) ∙
        (isoComp-assoc-at P.V E₁ left-associator) ⁻¹)

    comparison :
      (((h ◁ V.comparison) ▷ ia) ∙ (right-associator ∙ E₂)) =₂
      (result ∙ (((h ◁ H.comparison) ▷ ib) ∙ left-associator))
    comparison = isoComp-assoc-at result ((h ◁ H.comparison) ▷ ib) left-associator ∙
      isoComp-cong (axes ⁻¹) (idIso left-associator) ∙
      (isoComp-assoc-at ((h ◁ V.comparison) ▷ ia) E₁ left-associator) ⁻¹ ∙
      isoComp-cong (idIso ((h ◁ V.comparison) ▷ ia)) (permutation ⁻¹)
```
