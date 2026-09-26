# Uncurrying triangles and their families

Uncurrying a functor over a functor category also uncurries its specified
base triangle. For a family, reassociate the parameter product and
remove its projection from the base. The comparison operation retains
the compatibility of triangles, so this construction applies to whole
families, including their identifications.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Uncurrying
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.MappingCompatibility 𝒯 M ℱ using (funPost-uncurry-natural)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurrying 𝒯 M ℱ using (paste-iso-squares)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.RestrictionEquivalences 𝒯 M ℱ P using (module Restriction)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square; cancel-left; cancel-right)

module Triangle {K S C B : CAT} (r : MAP C B) (f : MAP K (Fun S B)) where
  value : FunctorOver f (funPost r) → FunctorOver (funUncurry f) r
  value v = record { lift = funUncurry (FunctorLift.lift v)
    ; comparison = funUncurryIso (FunctorLift.comparison v) ∙
        (funPost-uncurry r (FunctorLift.lift v)) ⁻¹ }

  module Identification {v w : FunctorOver f (funPost r)} (Φ : FunctorOverIso v w) where
    h = FunctorLift.lift v
    k = FunctorLift.lift w
    α = FunctorOverIso.underlying Φ
    θ = FunctorLift.comparison v
    ψ = FunctorLift.comparison w
    b₀ = funPost-uncurry r h
    b₁ = funPost-uncurry r k
    first = r ◁ funUncurryIso α
    second = funUncurryIso (funPost r ◁ α)
    final = idIso (funUncurry f)

    abstract
      matching : (funUncurryIso ψ ∙ second) =₂ (final ∙ funUncurryIso θ)
      matching = (isoComp-unitˡ-at (funUncurryIso θ)) ⁻¹ ∙
        ((funUncurry-isoMap _ _ ◁ FunctorOverIso.compatible Φ) ∙
          (funUncurryIso-comp ψ (funPost r ◁ α)) ⁻¹)

      comparison : FunctorOverIso (value v) (value w)
      comparison = record { underlying = funUncurryIso α
        ; compatible = isoComp-unitˡ-at (FunctorLift.comparison (value v)) ∙
            paste-iso-squares (b₀ ⁻¹) (b₁ ⁻¹) (funUncurryIso θ) (funUncurryIso ψ)
              first second final (move-square b₁ second first b₀ (funPost-uncurry-natural r α)) matching }

  module Recovery (w : FunctorOver (funUncurry f) r) where
    h = funCurry (FunctorLift.lift w)
    β = funCurry-β (FunctorLift.lift w)
    θ = FunctorLift.comparison w
    b = funPost-uncurry r h
    raw = (θ ∙ (r ◁ β)) ∙ b
    triangle = funIsoReflect (funPost r ∘ h) f raw
    backward : FunctorOver f (funPost r)
    backward = record { lift = h ; comparison = triangle }

    abstract
      comparison : FunctorOverIso (value backward) w
      comparison = record { underlying = β
        ; compatible = (cancel-right b (θ ∙ (r ◁ β)) ∙
            isoComp-cong (funIsoReflect-β (funPost r ∘ h) f raw) (idIso (b ⁻¹))) ⁻¹ }

    abstract
      comparison-underlying : FunctorOverIso.underlying comparison =₂ β
      comparison-underlying = idIso β

  module Reflection {v w : FunctorOver f (funPost r)} (Φ : FunctorOverIso (value v) (value w)) where
    h = FunctorLift.lift v
    k = FunctorLift.lift w
    α = funIsoReflect h k (FunctorOverIso.underlying Φ)
    b₀ = funPost-uncurry r h
    b₁ = funPost-uncurry r k
    θ = funUncurryIso (FunctorLift.comparison v)
    ψ = funUncurryIso (FunctorLift.comparison w)
    χ = funUncurryIso (funPost r ◁ α)
    γ = r ◁ FunctorOverIso.underlying Φ

    abstract
      natural : (b₁ ∙ χ) =₂ (γ ∙ b₀)
      natural = isoComp-cong (postWhisker r ◁ funIsoReflect-β h k (FunctorOverIso.underlying Φ)) (idIso b₀) ∙
        funPost-uncurry-natural r α

      recover : (ψ ∙ χ) =₂ θ
      recover = isoComp-unitʳ-at θ ∙
        (isoComp-cong (idIso θ) (isoComp-inverseˡ-at b₀) ∙
          (isoComp-assoc-at θ (b₀ ⁻¹) b₀ ∙
            (isoComp-cong (FunctorOverIso.compatible Φ) (idIso b₀) ∙
              ((isoComp-assoc-at (ψ ∙ b₁ ⁻¹) γ b₀) ⁻¹ ∙
                (isoComp-cong (idIso (ψ ∙ b₁ ⁻¹)) natural ∙
                  ((isoComp-assoc-at ψ (b₁ ⁻¹) (b₁ ∙ χ)) ⁻¹ ∙
                    isoComp-cong (idIso ψ) ((cancel-left b₁ χ) ⁻¹)))))))

      comparison : FunctorOverIso v w
      comparison = record { underlying = α
        ; compatible = funReflect-Iso₂ _ _
            (recover ∙ funUncurryIso-comp (FunctorLift.comparison w) (funPost r ◁ α)) }

  abstract
    left-inverse : (v : FunctorOver f (funPost r)) →
      FunctorOverIso (Recovery.backward (value v)) v
    left-inverse v = Reflection.comparison (Recovery.comparison (value v))

module Family {K S C B : CAT} (r : MAP C B) (f : MAP K (Fun S B)) (X : CAT) where
  u = funUncurry f
  regroup = Associativity.backward X K S
  projection = productMap (pr₂ {C = X} {D = K}) (id S)

  abstract
    remove-parameter : (projection ∘ regroup) =₁ pr₂ {C = X} {D = K × S}
    remove-parameter = pair-η pr₂ ∙
      (pair-cong (Associativity.backward-second X K S)
        (Associativity.backward-third X K S ∙ ((comp-unitˡ pr₂) ▷ regroup)) ∙
        pair-pre (pr₂ ∘ pr₁) (id S ∘ pr₂) regroup)

  insertion : FunctorOver (u ∘ pr₂ {C = X}) (funUncurry (f ∘ pr₂ {C = X}))
  insertion = record { lift = regroup
    ; comparison = (u ◁ remove-parameter) ∙
        (comp-assoc regroup projection u ∙ ((funUncurry-restrict f pr₂) ▷ regroup)) }

  value : FunctorOver (f ∘ pr₂ {C = X}) (funPost r) → FunctorOver (u ∘ pr₂ {C = X}) r
  value v = compose-over (Triangle.value r (f ∘ pr₂) v) insertion

  abstract
    identification : {v w : FunctorOver (f ∘ pr₂ {C = X}) (funPost r)} → FunctorOverIso v w →
      FunctorOverIso (value v) (value w)
    identification Φ = prewhisker-over insertion (Triangle.Identification.comparison r (f ∘ pr₂) Φ)

  abstract
    insertion-isEquiv : IsEquiv (FunctorLift.lift insertion)
    insertion-isEquiv = equiv-inverse (Associativity.forward-isEquiv X K S)

  module Recovery (w : FunctorOver (u ∘ pr₂ {C = X}) r) where
    module Lifted = Restriction.Factor (funUncurry (f ∘ pr₂ {C = X})) r insertion insertion-isEquiv w
      using (value; comparison)
    module Curried = Triangle.Recovery r (f ∘ pr₂ {C = X}) Lifted.value using (backward; comparison)
    backward : FunctorOver (f ∘ pr₂ {C = X}) (funPost r)
    backward = Curried.backward

    abstract
      comparison : FunctorOverIso (value backward) w
      comparison = compose-iso-over Lifted.comparison (prewhisker-over insertion Curried.comparison)

  abstract
    reflect : {v w : FunctorOver (f ∘ pr₂ {C = X}) (funPost r)} →
      FunctorOverIso (value v) (value w) → FunctorOverIso v w
    reflect {v} {w} Φ = Triangle.Reflection.comparison r (f ∘ pr₂ {C = X})
      (Restriction.Reflect.comparison (funUncurry (f ∘ pr₂ {C = X})) r insertion insertion-isEquiv
        (Triangle.value r (f ∘ pr₂) v) (Triangle.value r (f ∘ pr₂) w) Φ)

    left-inverse : (v : FunctorOver (f ∘ pr₂ {C = X}) (funPost r)) →
      FunctorOverIso (Recovery.backward (value v)) v
    left-inverse v = reflect (Recovery.comparison (value v))
```
