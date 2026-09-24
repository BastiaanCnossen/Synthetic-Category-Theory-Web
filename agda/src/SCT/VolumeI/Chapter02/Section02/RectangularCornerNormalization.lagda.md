# Normalizing the rectangle frames at a corner

Extending the specified vertex frames over the parameter agrees with
successively restricting the two product coordinates. We retain the
projection and associator comparisons in both calculations.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section02.RectangularCornerNormalization
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EndpointEvaluation 𝒯 M ℱ public
import SCT.VolumeI.Chapter02.Section02.PairedProjectionComposition as Paired
import SCT.VolumeI.Chapter02.Section02.InsertedShapeCorners as Shape
import SCT.VolumeI.Chapter01.Section04.ProjectionSquares as Projection
open import SCT.VolumeI.Chapter01.Section04.ProductAssociativity 𝒯 M
  using (module PairingAssembly; cancel-inverse-tail)
import SCT.VolumeI.Chapter01.Section03.PairingCoherence as Pairing
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-id; pair-cong-Iso₂)
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as Naturality
open Naturality vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)
import SCT.VolumeI.Chapter01.Section03.ProductFunctorUnits as ProductUnits
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (left-unitor-comp)
module PS = Projection 𝒯

module PairFrame {Q R X A B : CAT} (f : MAP X A) (g : MAP X B)
  (r : MAP R X) (t : MAP Q R) {u : MAP R A} {v : MAP R B}
  (α : (f ∘ r) =₁ u) (β : (g ∘ r) =₁ v) where
  left = (α ▷ t) ∙ (comp-assoc t r f) ⁻¹
  right = (β ▷ t) ∙ (comp-assoc t r g) ⁻¹
  first = pair-cong α β ∙ pair-pre f g r
  frame = pair-pre u v t ∙ (first ▷ t)
  direct = pair-cong left right ∙ pair-pre f g (r ∘ t)
  module P = Paired.At 𝒯 M ℱ f g r t α β (idIso (u ∘ t)) (idIso (v ∘ t))

  abstract
    direct-normal : P.direct =₂ direct
    direct-normal = isoComp-cong
      (pair-cong-Iso₂ (isoComp-unitˡ-at left) (isoComp-unitˡ-at right))
      (idIso (pair-pre f g (r ∘ t)))

    composite-normal : P.composite =₂ (frame ∙ (comp-assoc t r (pair f g)) ⁻¹)
    composite-normal = (isoComp-assoc-at (pair-pre u v t) (first ▷ t)
        ((comp-assoc t r (pair f g)) ⁻¹)) ⁻¹ ∙
      isoComp-cong
        (isoComp-unitˡ-at (pair-pre u v t) ∙
          isoComp-cong (pair-cong-id (u ∘ t) (v ∘ t)) (idIso (pair-pre u v t)))
        (idIso ((first ▷ t) ∙ (comp-assoc t r (pair f g)) ⁻¹))

    comparison : (frame ∙ (comp-assoc t r (pair f g)) ⁻¹) =₂ direct
    comparison = direct-normal ∙ P.comparison ⁻¹ ∙ composite-normal ⁻¹
```


```agda
clear-base : {Q R X D : CAT} (f : MAP X D) (r : MAP R X) (t : MAP Q R)
  {v : MAP R D} {w : MAP Q D} (b : (f ∘ r) =₁ v) (d : (v ∘ t) =₁ w) →
  (PS.compose-base f r b t d ∙ comp-assoc t r f) =₂ (d ∙ (b ▷ t))
clear-base f r t b d = cancel-inverse-tail (d ∙ (b ▷ t)) (comp-assoc t r f) ∙
  isoComp-cong ((isoComp-assoc-at d (b ▷ t) ((comp-assoc t r f) ⁻¹)) ⁻¹)
    (idIso (comp-assoc t r f))

module VertexRestriction {Γ R X A B : CAT} (f : MAP X A) (g : MAP X B)
  (r : MAP R X) (t : MAP Γ R) (x : Obj-abs X)
  (δ : (r ∘ t) =₁ const x) {u : Obj-abs A} {v : Obj-abs B}
  (α : (f ∘ x) =₁ u) (β : (g ∘ x) =₁ v)
  {f₁ : MAP R A} {g₁ : MAP R B}
  (b : (f ∘ r) =₁ f₁) (c : (g ∘ r) =₁ g₁)
  (d : (f₁ ∘ t) =₁ const u) (e : (g₁ ∘ t) =₁ const v) where
  module V = PairFrame f g x (terminate Γ) α β
  module Assemble = PairingAssembly f g r t (const x) δ
    b c d e V.left V.right (idIso (const u)) (idIso (const v))
  first = pair-cong b c ∙ pair-pre f g r
  second = pair-cong d e ∙ pair-pre f₁ g₁ t
  inner = V.frame ∙ ((comp-assoc (terminate Γ) x (pair f g)) ⁻¹ ∙
    PS.lift-base (pair f g) r t δ)

  abstract
    comparison :
      Assemble.shortFirst =₂ (d ∙ (b ▷ t)) →
      Assemble.shortSecond =₂ (e ∙ (c ▷ t)) →
      inner =₂ (second ∙ (first ▷ t))
    comparison left right =
      (isoComp-unitˡ-at (second ∙ (first ▷ t)) ∙
        isoComp-cong (pair-cong-id (const u) (const v)) (idIso (second ∙ (first ▷ t)))) ∙
      Assemble.assemble ((isoComp-unitˡ-at (d ∙ (b ▷ t))) ⁻¹ ∙ left)
        ((isoComp-unitˡ-at (e ∙ (c ▷ t))) ⁻¹ ∙ right) ∙
      isoComp-cong V.comparison (idIso (PS.lift-base (pair f g) r t δ)) ∙
      (isoComp-assoc-at V.frame ((comp-assoc (terminate Γ) x (pair f g)) ⁻¹)
        (PS.lift-base (pair f g) r t δ)) ⁻¹
```


```agda
module Axis {Γ X A B : CAT} (f : MAP X A) (g : MAP X B) (x : Obj-abs X)
  {u : Obj-abs A} {v : Obj-abs B}
  (α : (f ∘ x) =₁ u) (β : (g ∘ x) =₁ v)
  {f₁ : MAP (Γ × X) A} {g₁ : MAP (Γ × X) B}
  (b : (f ∘ pr₂) =₁ f₁) (c : (g ∘ pr₂) =₁ g₁)
  (d : (f₁ ∘ insert x) =₁ const u) (e : (g₁ ∘ insert x) =₁ const v) where
  i = insert {X = Γ} x
  L = productMap (id Γ) (pair f g)
  module V = VertexRestriction f g pr₂ i x (pair-β₂ (id Γ) (const x)) α β b c d e
  projection = pair-β₂ (id Γ ∘ pr₁) (pair f g ∘ pr₂)
  tail = (projection ▷ i) ∙ (comp-assoc i L pr₂) ⁻¹
  vertex = (comp-assoc (terminate Γ) x (pair f g)) ⁻¹ ∙
    PS.lift-base (pair f g) pr₂ i (pair-β₂ (id Γ) (const x))
  raw = V.V.frame ∙ (vertex ∙ tail)
  normalized = PS.compose-base pr₂ L (V.first ∙ projection) i V.second

  abstract
    comparison :
      V.Assemble.shortFirst =₂ (d ∙ (b ▷ i)) →
      V.Assemble.shortSecond =₂ (e ∙ (c ▷ i)) →
      raw =₂ normalized
    comparison left right =
      isoComp-cong (idIso V.second)
        (isoComp-cong ((preWhisker-isoComp-at V.first projection i) ⁻¹)
          (idIso ((comp-assoc i L pr₂) ⁻¹)) ∙
        (isoComp-assoc-at (V.first ▷ i) (projection ▷ i) ((comp-assoc i L pr₂) ⁻¹)) ⁻¹) ∙
      isoComp-assoc-at V.second (V.first ▷ i) tail ∙
      isoComp-cong (V.comparison left right) (idIso tail) ∙
      (isoComp-assoc-at V.V.frame vertex tail) ⁻¹
```


```agda
module ConstantLeg {Γ R X A : CAT} (u : Obj-abs A) (x : Obj-abs X)
  (p : MAP R X) (r : MAP Γ R) (δ : (p ∘ r) =₁ const x) where
  object-frame = (Shape.constant-at-object 𝒯 M ℱ u x ▷ terminate Γ) ∙
    (comp-assoc (terminate Γ) x (const u)) ⁻¹
  source = object-frame ∙ ((const u ◁ δ) ∙ comp-assoc r p (const u))
  target = const-pre u r ∙ (const-pre u p ▷ r)

  abstract
    comparison : source =₂ target
    comparison = clear-base (const u) p r (const-pre u p) (const-pre u r) ∙
      isoComp-cong (Shape.constant-coordinate 𝒯 M ℱ u p r δ) (idIso (comp-assoc r p (const u))) ∙
      (isoComp-assoc-at (const-pre u (const x)) (const u ◁ δ) (comp-assoc r p (const u))) ⁻¹ ∙
      isoComp-cong (Shape.constant-at-object-pre 𝒯 M ℱ u x)
        (idIso ((const u ◁ δ) ∙ comp-assoc r p (const u)))

module IdentityLeg {Γ R X : CAT} (x : Obj-abs X)
  (p : MAP R X) (r : MAP Γ R) (δ : (p ∘ r) =₁ const x) where
  object-frame = (comp-unitˡ x ▷ terminate Γ) ∙ (comp-assoc (terminate Γ) x (id X)) ⁻¹
  source = object-frame ∙ ((id X ◁ δ) ∙ comp-assoc r p (id X))
  target = δ ∙ (comp-unitˡ p ▷ r)

  abstract
    object-normal : object-frame =₂ comp-unitˡ (const x)
    object-normal = cancel-right (comp-assoc (terminate Γ) x (id X)) (comp-unitˡ (const x)) ∙
      isoComp-cong ((left-unitor-comp (terminate Γ) x) ⁻¹)
        (idIso ((comp-assoc (terminate Γ) x (id X)) ⁻¹))

    comparison : source =₂ target
    comparison = clear-base (id X) p r (comp-unitˡ p) δ ∙
      isoComp-cong (Shape.identity-coordinate 𝒯 M ℱ p r δ) (idIso (comp-assoc r p (id X))) ∙
      (isoComp-assoc-at (comp-unitˡ (const x)) (id X ◁ δ) (comp-assoc r p (id X))) ⁻¹ ∙
      isoComp-cong object-normal (idIso ((id X ◁ δ) ∙ comp-assoc r p (id X)))

module At (Γ A B : CAT) (u : Obj-abs A) (v : Obj-abs B) where
  module Goal = Shape.CompareCurrying 𝒯 M ℱ Γ A B u v
  ia = insert {X = Γ} u
  ib = insert {X = Γ} v
  ba = pair-β₂ (id Γ) (const u)
  bb = pair-β₂ (id Γ) (const v)
  module H = Axis (const u) (id B) v (Shape.constant-at-object 𝒯 M ℱ u v) (comp-unitˡ v)
    (const-pre u pr₂) (comp-unitˡ pr₂) (const-pre u ib) bb
  module V = Axis (id A) (const v) u (comp-unitˡ u) (Shape.constant-at-object 𝒯 M ℱ v u)
    (comp-unitˡ pr₂) (const-pre v pr₂) ba (const-pre v ia)

  abstract
    source-normalization : Goal.SourceNormalization
    source-normalization = H.comparison
      (ConstantLeg.comparison u v pr₂ ib bb) (IdentityLeg.comparison v pr₂ ib bb)

    target-normalization : Goal.TargetNormalization
    target-normalization = V.comparison
      (IdentityLeg.comparison u pr₂ ia ba) (ConstantLeg.comparison v u pr₂ ia ba)

    comparison : Goal.R.matching =₂ Goal.K.Shape.comparison
    comparison = Goal.comparison source-normalization target-normalization
```
