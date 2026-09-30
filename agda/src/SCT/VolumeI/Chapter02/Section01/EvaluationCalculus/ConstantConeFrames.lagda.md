# The matching frames of constant cones

The constant-diagram comparison commutes with postcomposition, with its
specified associators. This is the leg calculation used when comparing
the entire constant cone after uncurrying.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.ConstantConeFrames
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ public
import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.ConstantDiagramNaturality as Constants
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.MappingSubstitution 𝒯 M ℱ
  using (funPost-uncurry-restrict)
open import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Parameterized
  using (module WhiskeringLaws)
open WhiskeringLaws vocabulary terminal products productLaws composition vertical whiskering
  using (whisker-mixed-at)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits
  vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module At {Γ C D : CAT} (A : CAT) (f : MAP C D) (h : MAP Γ C) where
  module Constant = Constants.At 𝒯 M ℱ A using (comparison; module Post; module CompositeParameter)
  module Square = Constant.Post f using (value; evaluated; computation)
  module Composite = Constant.CompositeParameter f h using (value; module Coordinates)
  cC = constantDiagram A C
  cD = constantDiagram A D
  R = productMap h (id A)
  β = funCurry-β (pr₁ {C = C} {D = A})
  π = pair-β₁ (h ∘ pr₁) (id A ∘ pr₂)
  Θ = funUncurry-restrict cC h
  Θleft = funUncurry-restrict (cD ∘ f) h
  Θright = funUncurry-restrict (funPost f ∘ cC) h
  E₀ = funPost-uncurry f cC
  E₁ = funPost-uncurry f (cC ∘ h)
  η = comp-assoc h cC (funPost f)
  θ = comp-assoc h f cD
  normal = η ∙ ((Square.value ▷ h) ∙ θ ⁻¹)
  α = funUncurryIso (Square.value ▷ h)
  Uη = funUncurryIso η
  Uθ = funUncurryIso θ
  aΘ = f ◁ Θ
  aβ = f ◁ (β ▷ R)
  aπ = f ◁ π
  assocU = comp-assoc R (funUncurry cC) f
  assocπ = comp-assoc R pr₁ f
  outside = comp-assoc (pr₁ {C = Γ} {D = A}) h f
  v = aπ ∙ assocπ

  abstract
    post-restriction : ((f ◁ Constant.comparison h) ∙ (E₁ ∙ Uη)) =₂
      (v ∙ ((Square.evaluated ▷ R) ∙ Θright))
    post-restriction = isoComp-cong (idIso v)
        (isoComp-cong ((preWhisker-isoComp-at (f ◁ β) E₀ R) ⁻¹) (idIso Θright) ∙
          (isoComp-assoc-at ((f ◁ β) ▷ R) (E₀ ▷ R) Θright) ⁻¹) ∙
      (isoComp-assoc-at aπ assocπ (((f ◁ β) ▷ R) ∙ ((E₀ ▷ R) ∙ Θright)) ⁻¹ ∙
      (isoComp-cong (idIso aπ)
        (isoComp-assoc-at assocπ ((f ◁ β) ▷ R) ((E₀ ▷ R) ∙ Θright) ∙
          isoComp-cong (whisker-mixed-at β R f ⁻¹) (idIso ((E₀ ▷ R) ∙ Θright))) ∙
      (isoComp-cong (idIso aπ)
        (isoComp-assoc-at aβ assocU ((E₀ ▷ R) ∙ Θright) ⁻¹ ∙
          isoComp-cong (idIso aβ) (funPost-uncurry-restrict f cC h)) ∙
      (isoComp-cong (idIso aπ) (isoComp-assoc-at aβ aΘ (E₁ ∙ Uη)) ∙
      (isoComp-assoc-at aπ (aβ ∙ aΘ) (E₁ ∙ Uη) ∙
        isoComp-cong
          (isoComp-cong (idIso aπ) (postWhisker-isoComp-at f (β ▷ R) Θ) ∙
            postWhisker-isoComp-at f π ((β ▷ R) ∙ Θ))
          (idIso (E₁ ∙ Uη)))))))

    evaluated-square : (Square.evaluated ∙ funUncurryIso Square.value) =₂ Constant.comparison f
    evaluated-square = cancel-inverse Square.evaluated (Constant.comparison f) ∙
      isoComp-cong (idIso Square.evaluated) Square.computation

    restricted-square : ((Square.evaluated ▷ R) ∙ (Θright ∙ α)) =₂
      ((Constant.comparison f ▷ R) ∙ Θleft)
    restricted-square = isoComp-cong
        ((preWhisker R ◁ evaluated-square) ∙
          (preWhisker-isoComp-at Square.evaluated (funUncurryIso Square.value) R) ⁻¹)
        (idIso Θleft) ∙
      (isoComp-assoc-at (Square.evaluated ▷ R) (funUncurryIso Square.value ▷ R) Θleft ⁻¹ ∙
        isoComp-cong (idIso (Square.evaluated ▷ R)) (funUncurry-restrict-inputs Square.value h))

    left-expanded : (((f ◁ Constant.comparison h) ∙ (E₁ ∙ Uη)) ∙ α) =₂
      (v ∙ ((Constant.comparison f ▷ R) ∙ Θleft))
    left-expanded = isoComp-cong (idIso v)
        (restricted-square ∙ isoComp-assoc-at (Square.evaluated ▷ R) Θright α) ∙
      (isoComp-assoc-at v ((Square.evaluated ▷ R) ∙ Θright) α ∙
        isoComp-cong post-restriction (idIso α))

    outer-frame : (outside ∙ Composite.Coordinates.first) =₂ v
    outer-frame = cancel-inverse outside v

    right-expanded : ((outside ∙ Constant.comparison (f ∘ h)) ∙ Uθ) =₂
      (v ∙ ((Constant.comparison f ▷ R) ∙ Θleft))
    right-expanded = isoComp-cong outer-frame (idIso ((Constant.comparison f ▷ R) ∙ Θleft)) ∙
      (isoComp-assoc-at outside Composite.Coordinates.first ((Constant.comparison f ▷ R) ∙ Θleft) ⁻¹ ∙
      (isoComp-cong (idIso outside) Composite.value ∙
        isoComp-assoc-at outside (Constant.comparison (f ∘ h)) Uθ))

    normalized-input : (funUncurryIso normal ∙ Uθ) =₂ (Uη ∙ α)
    normalized-input = isoComp-cong (idIso Uη)
        (isoComp-unitʳ-at α ∙
          (isoComp-cong (idIso α) (isoComp-inverseˡ-at Uθ) ∙
            isoComp-assoc-at α (Uθ ⁻¹) Uθ)) ∙
      (isoComp-assoc-at Uη (α ∙ Uθ ⁻¹) Uθ ∙
        isoComp-cong
          (isoComp-cong (idIso Uη)
            (isoComp-cong (idIso α) (funUncurryIso-inverse θ) ∙
              funUncurryIso-comp (Square.value ▷ h) (θ ⁻¹)) ∙
            funUncurryIso-comp η ((Square.value ▷ h) ∙ θ ⁻¹))
          (idIso Uθ))

    expanded-input : (((f ◁ Constant.comparison h) ∙ (E₁ ∙ funUncurryIso normal)) ∙ Uθ) =₂
      (((f ◁ Constant.comparison h) ∙ (E₁ ∙ Uη)) ∙ α)
    expanded-input = isoComp-assoc-at (f ◁ Constant.comparison h) (E₁ ∙ Uη) α ⁻¹ ∙
      (isoComp-cong (idIso (f ◁ Constant.comparison h))
        (isoComp-assoc-at E₁ Uη α ⁻¹) ∙
      (isoComp-cong (idIso (f ◁ Constant.comparison h))
        (isoComp-cong (idIso E₁) normalized-input) ∙
      (isoComp-cong (idIso (f ◁ Constant.comparison h))
        (isoComp-assoc-at E₁ (funUncurryIso normal) Uθ) ∙
        isoComp-assoc-at (f ◁ Constant.comparison h) (E₁ ∙ funUncurryIso normal) Uθ)))

    value : ((f ◁ Constant.comparison h) ∙ (E₁ ∙ funUncurryIso normal)) =₂
      (outside ∙ Constant.comparison (f ∘ h))
    value = cancel-right-reflect Uθ (right-expanded ⁻¹ ∙ (left-expanded ∙ expanded-input))
```
