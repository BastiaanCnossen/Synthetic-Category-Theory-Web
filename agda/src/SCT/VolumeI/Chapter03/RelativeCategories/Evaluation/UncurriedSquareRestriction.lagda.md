# Restricting an evaluated postcomposition square

The matching of a cartesian forgetful square evaluates to the family
beta comparison. This calculation retains that formula under an arbitrary
parameter functor, including both reassociation maps.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.UncurriedSquareRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (Cone; conePre)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-composite)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.MappingSubstitution 𝒯 M ℱ using (funPost-uncurry-restrict)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Iso
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left; cancel-right)
open Iso vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module Restrict {K C D A B X : CAT} (u : MAP C D)
  (a : MAP A (Fun K C)) (b : MAP B (Fun K D)) (H : MAP A B)
  (σ : (funPost u ∘ a) =₁ (b ∘ H))
  (β : funUncurry (b ∘ H) =₁ (u ∘ funUncurry a))
  (image : funUncurryIso σ =₂ (β ⁻¹ ∙ funPost-uncurry u a))
  (F : MAP X A) where
  R = productMap F (id K)
  ℓ = funUncurry-restrict a F
  l = funUncurry-restrict (funPost u ∘ a) F
  r = funUncurry-restrict (b ∘ H) F
  L = funUncurryIso (comp-assoc F a (funPost u))
  Q = funUncurryIso (comp-assoc F H b)
  τ = funUncurryIso (σ ▷ F)
  δ = funUncurryIso σ ▷ R
  d = funPost-uncurry u a ▷ R
  βr = β ▷ R
  A′ = comp-assoc R (funUncurry a) u
  D′ = u ◁ ℓ
  c′ = funPost-uncurry u (a ∘ F)
  square : Cone (funPost u) b A
  square = record { left = a ; right = H ; match = σ }
  restricted = conePre F square
  comparison = (u ◁ ℓ ⁻¹) ∙
    (A′ ∙ (βr ∙ (r ∙ funUncurryIso ((comp-assoc F H b) ⁻¹))))

  abstract
    middle : (βr ∙ δ) =₂ d
    middle = (preWhisker R ◁
      (cancel-inverse β (funPost-uncurry u a) ∙ isoComp-cong (idIso β) image)) ∙
      (preWhisker-isoComp-at β (funUncurryIso σ) R) ⁻¹
    natural : (βr ∙ (r ∙ τ)) =₂ (d ∙ l)
    natural = isoComp-cong middle (idIso l) ∙
      ((isoComp-assoc-at βr δ l) ⁻¹ ∙
        isoComp-cong (idIso βr) (funUncurry-restrict-inputs σ F))
    raw-image : funUncurryIso (Cone.match restricted) =₂ (Q ∙ (τ ∙ L ⁻¹))
    raw-image = isoComp-cong (idIso Q)
      (isoComp-cong (idIso τ) (funUncurryIso-inverse (comp-assoc F a (funPost u))) ∙
        funUncurryIso-comp (σ ▷ F) ((comp-assoc F a (funPost u)) ⁻¹)) ∙
      funUncurryIso-comp (comp-assoc F H b)
        ((σ ▷ F) ∙ (comp-assoc F a (funPost u)) ⁻¹)

    inner : ((r ∙ Q ⁻¹) ∙ (Q ∙ (τ ∙ L ⁻¹))) =₂ (r ∙ (τ ∙ L ⁻¹))
    inner = isoComp-cong (idIso r) (cancel-left Q (τ ∙ L ⁻¹)) ∙
      isoComp-assoc-at r (Q ⁻¹) (Q ∙ (τ ∙ L ⁻¹))
    middle-restricted : (βr ∙ ((r ∙ Q ⁻¹) ∙ (Q ∙ (τ ∙ L ⁻¹)))) =₂ ((d ∙ l) ∙ L ⁻¹)
    middle-restricted = isoComp-cong natural (idIso (L ⁻¹)) ∙
      ((isoComp-assoc-at βr (r ∙ τ) (L ⁻¹)) ⁻¹ ∙
        isoComp-cong (idIso βr)
          ((isoComp-assoc-at r τ (L ⁻¹)) ⁻¹ ∙ inner))
    outer : ((D′ ⁻¹) ∙ (A′ ∙ ((d ∙ l) ∙ L ⁻¹))) =₂ c′
    outer = cancel-right L c′ ∙
      (isoComp-cong (cancel-left D′ (c′ ∙ L)) (idIso (L ⁻¹)) ∙
        ((isoComp-assoc-at (D′ ⁻¹) (D′ ∙ (c′ ∙ L)) (L ⁻¹)) ⁻¹ ∙
          isoComp-cong (idIso (D′ ⁻¹))
            (isoComp-cong ((funPost-uncurry-restrict u a F) ⁻¹) (idIso (L ⁻¹)) ∙
              (isoComp-assoc-at A′ (d ∙ l) (L ⁻¹)) ⁻¹)))
    normalized : (comparison ∙ funUncurryIso (Cone.match restricted)) =₂ c′
    normalized = outer ∙
      (isoComp-cong (idIso (D′ ⁻¹))
        (isoComp-cong (idIso A′)
          (middle-restricted ∙ isoComp-assoc-at βr (r ∙ Q ⁻¹) (Q ∙ (τ ∙ L ⁻¹))) ∙
          isoComp-assoc-at A′ (βr ∙ (r ∙ Q ⁻¹)) (Q ∙ (τ ∙ L ⁻¹))) ∙
        (isoComp-assoc-at (D′ ⁻¹) (A′ ∙ (βr ∙ (r ∙ Q ⁻¹))) (Q ∙ (τ ∙ L ⁻¹)) ∙
          isoComp-cong
            (isoComp-cong (post-inverse u ℓ)
              (isoComp-cong (idIso A′) (isoComp-cong (idIso βr)
                (isoComp-cong (idIso r) (funUncurryIso-inverse (comp-assoc F H b))))))
            raw-image))
```
