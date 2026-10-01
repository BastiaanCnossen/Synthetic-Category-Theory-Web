# Evaluating the relative pullback cone

Forget the base triangles, then uncurry. The relative matching becomes
the original pullback matching conjugated by the two family comparisons.
Cancelling those endpoint comparisons identifies the whole cone with the
original pullback cone restricted along universal evaluation.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackConeEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯
  using (changeEndpoints; changeEndpoints-cong; changeEndpoints-to-square)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurrying 𝒯 M ℱ using (uncurryCone)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurryingNormalization 𝒯 M ℱ using (endpoints-iterated)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Pullbacks 𝒯 M ℱ P using () renaming (module Pullback to RelativePullback)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.Postcomposition 𝒯 M ℱ P using (module Postcompose)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.PullbackMatching 𝒯 M ℱ P using (module Matching)
open import SCT.VolumeI.Chapter03.RelativeCategories.Composition.PostcompositionCartesian 𝒯 M ℱ P using (module Postcomposition)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Iso
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
open Iso vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

abstract
  change-endpoints-inputs : {X Y : CAT} {f f′ g g′ : MAP X Y}
    {p p′ : f =₁ f′} {q q′ : g =₁ g′} (τ : f =₁ g) →
    p =₂ p′ → q =₂ q′ → changeEndpoints p q τ =₂ changeEndpoints p′ q′ τ
  change-endpoints-inputs τ α β = isoComp-cong β (isoComp-cong (idIso τ) (＝-inv ◁ α))

module Transport {X Y : CAT} {x y a₀ b₀ a₁ b₁ a₂ b₂ : MAP X Y}
  (κ : x =₁ a₀) (κ′ : y =₁ b₀) (u : a₀ =₁ a₁) (v : b₀ =₁ b₁)
  (A : a₂ =₁ a₁) (B : b₂ =₁ b₁) (τ : a₂ =₁ b₂) (μ : x =₁ y) where
  L = A ⁻¹ ∙ (u ∙ κ)
  R = B ⁻¹ ∙ (v ∙ κ′)
  raw = changeEndpoints κ κ′ μ
  target = changeEndpoints A B τ
  module WithImage (image : μ =₂ (R ⁻¹ ∙ (τ ∙ L))) where
    abstract
      recovered : changeEndpoints L R μ =₂ τ
      recovered = cancel-right L τ ∙
        (isoComp-cong (cancel-inverse R (τ ∙ L)) (idIso (L ⁻¹)) ∙
          ((isoComp-assoc-at R (R ⁻¹ ∙ (τ ∙ L)) (L ⁻¹)) ⁻¹ ∙
            changeEndpoints-cong L R image))
      transported : changeEndpoints (u ∙ κ) (v ∙ κ′) μ =₂ target
      transported = changeEndpoints-cong A B recovered ∙
        ((endpoints-iterated L R A B μ) ⁻¹ ∙
          (change-endpoints-inputs μ (cancel-inverse A (u ∙ κ)) (cancel-inverse B (v ∙ κ′))) ⁻¹)
      square : (target ∙ u) =₂ (v ∙ raw)
      square = (changeEndpoints-to-square u v raw target
        (transported ∙ endpoints-iterated κ κ′ u v μ)) ⁻¹

module Evaluation {K C D E S : CAT} (k : MAP K S)
  {f : MAP C S} {g : MAP D S} {h : MAP E S} (u : FunctorOver f h) (v : FunctorOver g h) where
  private
    module R = RelativePullback u v using (projection; category; first; second; first-map; second-map; left-map; right-map; matching)
  private
    module First = Postcompose k R.first using (functor; family-comparison)
  private
    module Second = Postcompose k R.second using (functor; family-comparison)
  private
    module Match = Matching k u v using (matching; evaluated-image; native-comparison-underlying; left-family-underlying; right-family-underlying)
  private
    module CU = Postcomposition k u using (square; module Restricted)
  private
    module CV = Postcomposition k v using (square; module Restricted)
  private
    module U = CU.Restricted First.functor using (family-comparison-image)
  private
    module V = CV.Restricted Second.functor using (family-comparison-image)
  Source = FunOver k R.projection
  forget = Over.forget k R.projection
  e = funUncurry forget
  first = Over.forget k f ∘ First.functor
  second = Over.forget k g ∘ Second.functor
  qu = Cone.match (conePre First.functor CU.square)
  qv = Cone.match (conePre Second.functor CV.square)
  μ = Over.forget k h ◁ Match.matching
  ordinary : Cone (funPost R.left-map) (funPost R.right-map) Source
  ordinary = record { left = first ; right = second ; match = qv ⁻¹ ∙ (μ ∙ qu) }
  source = uncurryCone ordinary
  target = conePre e (pullbackCone R.left-map R.right-map)
  β₁ = FunctorOverIso.underlying First.family-comparison
  β₂ = FunctorOverIso.underlying Second.family-comparison
  κ = FunctorOverIso.underlying (postcompose-family k u First.functor)
  κ′ = FunctorOverIso.underlying (postcompose-family k v Second.functor)
  ω = funUncurryIso μ
  uq = funUncurryIso qu
  vq = funUncurryIso qv
  fl = funPost-uncurry R.left-map first
  gr = funPost-uncurry R.right-map second
  raw = changeEndpoints κ κ′ ω
  A = comp-assoc e R.first-map R.left-map
  B′ = comp-assoc e R.second-map R.right-map
  τ = R.matching ▷ e
  private
    module Changed = Transport κ κ′ (R.left-map ◁ β₁) (R.right-map ◁ β₂) A B′ τ ω
      using (module WithImage)
  abstract
    uncurried-matching : funUncurryIso (Cone.match ordinary) =₂ changeEndpoints (uq ⁻¹) (vq ⁻¹) ω
    uncurried-matching =
      isoComp-cong (funUncurryIso-inverse qv)
        (isoComp-cong (idIso ω) ((inverse-inverse uq) ⁻¹) ∙ funUncurryIso-comp μ qu) ∙
        funUncurryIso-comp (qv ⁻¹) (μ ∙ qu)
    source-normal : Cone.match source =₂ raw
    source-normal = change-endpoints-inputs ω (U.family-comparison-image ⁻¹) (V.family-comparison-image ⁻¹) ∙
      (endpoints-iterated (uq ⁻¹) (vq ⁻¹) fl gr ω ∙
        changeEndpoints-cong fl gr uncurried-matching)
    image : ω =₂ ((B′ ⁻¹ ∙ ((R.right-map ◁ β₂) ∙ κ′)) ⁻¹ ∙
      (τ ∙ (A ⁻¹ ∙ ((R.left-map ◁ β₁) ∙ κ))))
    image = isoComp-cong (＝-inv ◁ Match.right-family-underlying)
      (isoComp-cong (idIso τ) Match.left-family-underlying) ∙
      (Match.native-comparison-underlying ∙ Match.evaluated-image)
    comparison : ConeIso source target
    comparison = record { leftIso = β₁ ; rightIso = β₂
      ; compatible = isoComp-cong (idIso (R.right-map ◁ β₂)) (source-normal ⁻¹) ∙
          Changed.WithImage.square image }
    comparison-left : ConeIso.leftIso comparison =₂ β₁
    comparison-left = idIso β₁
    comparison-right : ConeIso.rightIso comparison =₂ β₂
    comparison-right = idIso β₂
```
