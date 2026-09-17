# Naturality of precomposition under uncurrying

The product comparison separating the two coordinates is natural in the
varying first input. This supplies the additional uncurrying comparison
needed for the coproduct restriction theorem.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section02.FamilyProductFunctor as FP
import SCT.VolumeI.Chapter01.Section02.FamilyPairing as FamilyPairing
import SCT.VolumeI.Chapter01.Section02.Parameterized as Parameterized
import SCT.VolumeI.Chapter01.Section02.FamilyNaturality as FamilyNaturality

module SCT.VolumeI.Chapter01.Section03.PrecompositionNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open import SCT.VolumeI.Chapter01.Section03.Currying 𝒯 M
open import SCT.VolumeI.Chapter01.Section03.Functoriality 𝒯 M
open import SCT.VolumeI.Chapter01.Section03.Compatibility 𝒯 M
open FP vocabulary terminal products productLaws composition vertical whiskering
open FamilyPairing vocabulary terminal products productLaws composition vertical whiskering using (post-constant; pre-constant)
open Parameterized vocabulary terminal products productLaws composition vertical using (const-cong; unitˡ; unitʳ)
open Parameterized.WhiskeringLaws vocabulary terminal products productLaws composition vertical whiskering
  using (postWhisker-id-general; preWhisker-id-general; postWhisker-comp-general; whisker-mixed-general)
open FamilyNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (family-move-square; family-interchange-fixedOuter)

constant-unit-square : {A C D : CAT} {f g : MAP C D} (β : NatIso f g)
  (u : MAP A (f ≅ f)) → NatIso u (const (idIso f)) →
  NatIso (const β ∙ u) (const (idIso g) ∙ const β)
constant-unit-square β u p = invIso (unitˡ (const β)) ∙
  (unitʳ (const β) ∙ isoComp-cong (idIso (const β)) p)

productMap-separate-inputs : {A X Y B C : CAT} {u v : MAP X Y}
  (γ : MAP A (u ≅ v)) (i : MAP B C) →
  NatIso (const (productMap-separate v i) ∙ (productMap (id Y) i ◁ productFamily γ (const (idIso (id B)))))
    ((productFamily γ (const (idIso (id C))) ▷ productMap (id X) i) ∙ const (productMap-separate u i))
productMap-separate-inputs {X = X} {Y} {B} {C} {u} {v} γ i =
  paste-family-squares (invIso r₃u ∙ (r₂u ∙ r₁u)) (invIso r₃v ∙ (r₂v ∙ r₁v))
    (invIso r₄u) (invIso r₄v) action₀ action₃ action₄
    (paste-family-squares (r₂u ∙ r₁u) (r₂v ∙ r₁v) (invIso r₃u) (invIso r₃v)
      action₀ action₂ action₃
      (paste-family-squares r₁u r₁v r₂u r₂v action₀ action₁ action₂ step₁ step₂) step₃)
    step₄
  where
  identityB = const (idIso (id B))
  identityC = const (idIso (id C))
  r₁u = productMap-comp u (id Y) (id B) i
  r₁v = productMap-comp v (id Y) (id B) i
  r₂u = productMap-cong (comp-unitˡ u) (comp-unitʳ i)
  r₂v = productMap-cong (comp-unitˡ v) (comp-unitʳ i)
  r₃u = productMap-cong (comp-unitʳ u) (comp-unitˡ i)
  r₃v = productMap-cong (comp-unitʳ v) (comp-unitˡ i)
  r₄u = productMap-comp (id X) u i (id C)
  r₄v = productMap-comp (id X) v i (id C)
  action₀ = productMap (id Y) i ◁ productFamily γ identityB
  action₁ = productFamily (id Y ◁ γ) (i ◁ identityB)
  action₂ = productFamily γ (const (idIso i))
  action₃ = productFamily (γ ▷ id X) (identityC ▷ i)
  action₄ = productFamily γ identityC ▷ productMap (id X) i
  step₁ = productMap-comp-family-inner γ identityB (id Y) i
  step₂ = product-family-square (comp-unitˡ u) (comp-unitˡ v) (comp-unitʳ i) (comp-unitʳ i)
    (id Y ◁ γ) γ (i ◁ identityB) (const (idIso i))
    (postWhisker-id-general γ)
    (constant-unit-square (comp-unitʳ i) _
      (const-cong (postWhisker-idIso i (id B)) ∙ post-constant i (idIso (id B))))
  step₃ = family-move-square r₃v action₃ action₂ r₃u
    (product-family-square (comp-unitʳ u) (comp-unitʳ v) (comp-unitˡ i) (comp-unitˡ i)
      (γ ▷ id X) γ (identityC ▷ i) (const (idIso i))
      (preWhisker-id-general γ)
      (constant-unit-square (comp-unitˡ i) _
        (const-cong (preWhisker-idIso (id C) i) ∙ pre-constant (idIso (id C)) i)))
  step₄ = family-move-square r₄v action₄ action₃ r₄u
    (productMap-comp-family-outer (id X) i γ identityC)

mapPre-uncurry-inputs : {A X B C E : CAT} (i : MAP B C)
  {u v : MAP X (Map C E)} (γ : MAP A (u ≅ v)) →
  NatIso (const (mapPre-uncurry i v) ∙ uncurryFamily (mapPre i ◁ γ))
    ((uncurryFamily γ ▷ productMap (id X) i) ∙ const (mapPre-uncurry i u))
mapPre-uncurry-inputs {X = X} {B} {C} {E} i {u} {v} γ =
  paste-family-squares (r₄u ∙ (r₃u ∙ (r₂u ∙ r₁u))) (r₄v ∙ (r₃v ∙ (r₂v ∙ r₁v)))
    r₅u r₅v action₀ action₄ action₅
    (paste-family-squares (r₃u ∙ (r₂u ∙ r₁u)) (r₃v ∙ (r₂v ∙ r₁v)) r₄u r₄v
      action₀ action₃ action₄
      (paste-family-squares (r₂u ∙ r₁u) (r₂v ∙ r₁v) r₃u r₃v action₀ action₂ action₃
        (paste-family-squares r₁u r₁v r₂u r₂v action₀ action₁ action₂
          (uncurry-pre-substitution (mapPre i) γ)
          (family-interchange-fixedOuter (mapPre-β i) pγ))
        (postWhisker-comp-general pγ K mapEval))
      (post-family-square mapEval (productMap-separate u i) (productMap-separate v i)
        (K ◁ pγ) (qγ ▷ R) (productMap-separate-inputs γ i)))
    (family-move-square (comp-assoc R qv mapEval) action₅ action₄ (comp-assoc R qu mapEval)
      (whisker-mixed-general qγ R mapEval))
  where
  K = productMap (id (Map C E)) i
  R = productMap (id X) i
  pu = productMap u (id B)
  pv = productMap v (id B)
  qu = productMap u (id C)
  qv = productMap v (id C)
  pγ = productFamily γ (const (idIso (id B)))
  qγ = productFamily γ (const (idIso (id C)))
  r₁u = mapUncurry-pre (mapPre i) u
  r₁v = mapUncurry-pre (mapPre i) v
  r₂u = mapPre-β i ▷ pu
  r₂v = mapPre-β i ▷ pv
  r₃u = comp-assoc pu K mapEval
  r₃v = comp-assoc pv K mapEval
  r₄u = mapEval ◁ productMap-separate u i
  r₄v = mapEval ◁ productMap-separate v i
  r₅u = invIso (comp-assoc R qu mapEval)
  r₅v = invIso (comp-assoc R qv mapEval)
  action₀ = uncurryFamily (mapPre i ◁ γ)
  action₁ = mapUncurry (mapPre i) ◁ pγ
  action₂ = (mapEval ∘ K) ◁ pγ
  action₃ = mapEval ◁ (K ◁ pγ)
  action₄ = mapEval ◁ (qγ ▷ R)
  action₅ = uncurryFamily γ ▷ R
```
