# The projections of source compatibility

The source-compositor equation can be checked after each projection of
the target pullback. The first projection uses prewhiskering, interchange,
and the computation of the chosen compositor. The second follows from
the two native triangle witnesses.

These projected equations do not by themselves give the equation in the
pullback. A higher cone comparison would also need their compatibility
with the matching. We keep this distinction explicit.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter03.Section05.BaseChange.BaseChangeComparisonComputation as Images

module SCT.VolumeI.Chapter03.Section05.BaseChange.BaseChangeSourceProjections
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurrying 𝒯 M ℱ using (paste-iso-squares)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.Identifications 𝒯 M ℱ P using (module Change)
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (move-square; pre-square-projection; cancel-left-reflect)
open Structural vocabulary terminal products productLaws composition whiskering
  using (preWhisker-comp-at)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-inverse)

module RestrictionSquare {A B C X Y : CAT}
  (r : MAP B C) (s : MAP A B) (w : MAP X C) (t : MAP A X)
  (σ : (r ∘ s) =₁ (w ∘ t)) {u v : MAP C Y} (α : u =₁ v) where
  boundary : (z : MAP C Y) → ((z ∘ r) ∘ s) =₁ ((z ∘ w) ∘ t)
  boundary z = (comp-assoc t w z) ⁻¹ ∙ ((z ◁ σ) ∙ comp-assoc s r z)

  opaque
    naturality : (boundary v ∙ ((α ▷ r) ▷ s)) =₂ (((α ▷ w) ▷ t) ∙ boundary u)
    naturality = paste-iso-squares
      ((u ◁ σ) ∙ comp-assoc s r u) ((v ◁ σ) ∙ comp-assoc s r v)
      ((comp-assoc t w u) ⁻¹) ((comp-assoc t w v) ⁻¹)
      ((α ▷ r) ▷ s) (α ▷ (w ∘ t)) ((α ▷ w) ▷ t)
      (paste-iso-squares (comp-assoc s r u) (comp-assoc s r v) (u ◁ σ) (v ◁ σ)
        ((α ▷ r) ▷ s) (α ▷ (r ∘ s)) (α ▷ (w ∘ t))
        (preWhisker-comp-at α r s) ((interchange-at α σ) ⁻¹))
      (move-square (comp-assoc t w v) ((α ▷ w) ▷ t) (α ▷ (w ∘ t))
        (comp-assoc t w u) (preWhisker-comp-at α w t))

module IdentificationImage {C D S T : CAT} (p : MAP S T)
  {f : MAP C T} {g : MAP D T} (u v : FunctorOver f g) (Φ : FunctorOverIso u v) where
  module B = Change p using (cone; module Identification)
  module Computation = Images.Computation 𝒯 M ℱ P p u v using (left-image)
  βu = pullbackLift-β₁ (B.cone u)
  βv = pullbackLift-β₁ (B.cone v)
  α = FunctorOverIso.underlying Φ
  image = FunctorOverIso.underlying (B.Identification.comparison Φ)

  opaque
    square : (βv ∙ (pullback₁ {f = g} {p} ◁ image)) =₂
      ((α ▷ pullback₁ {f = f} {p}) ∙ βu)
    square = cancel-inverse βv ((α ▷ pullback₁ {f = f} {p}) ∙ βu) ∙
      isoComp-cong (idIso βv)
        (Computation.left-image Φ ∙
          (postWhisker (pullback₁ {f = g} {p}) ◁ B.Identification.comparison-underlying Φ))

module CompositeImage {A C D S T : CAT} (p : MAP S T)
  {e : MAP A T} {f : MAP C T} {g : MAP D T}
  (w : FunctorOver e f) (z : FunctorOver f g) where
  module B = Change p using (cone; functor; module Composite)
  module Composite = B.Composite w z using (comparison; cone-computation)
  rA : MAP (Pullback e p) A
  rA = pullback₁
  rC : MAP (Pullback f p) C
  rC = pullback₁
  rD : MAP (Pullback g p) D
  rD = pullback₁
  bw = FunctorLift.lift (B.functor w)
  bz = FunctorLift.lift (B.functor z)
  βw = pullbackLift-β₁ (B.cone w)
  βz = pullbackLift-β₁ (B.cone z)
  βzw = pullbackLift-β₁ (B.cone (compose-over z w))
  tail = (βz ▷ bw) ∙ (comp-assoc bw bz rD) ⁻¹
  boundary = (comp-assoc rA (FunctorLift.lift w) (FunctorLift.lift z)) ⁻¹ ∙
    ((FunctorLift.lift z ◁ βw) ∙ comp-assoc bw rC (FunctorLift.lift z))
  normal = (comp-assoc rA (FunctorLift.lift w) (FunctorLift.lift z)) ⁻¹ ∙
    ((FunctorLift.lift z ◁ βw) ∙ (comp-assoc bw rC (FunctorLift.lift z) ∙ tail))

  opaque
    normalization : (boundary ∙ tail) =₂ normal
    normalization = isoComp-cong (idIso ((comp-assoc rA (FunctorLift.lift w) (FunctorLift.lift z)) ⁻¹))
      (isoComp-assoc-at (FunctorLift.lift z ◁ βw) (comp-assoc bw rC (FunctorLift.lift z)) tail) ∙
      isoComp-assoc-at ((comp-assoc rA (FunctorLift.lift w) (FunctorLift.lift z)) ⁻¹)
        ((FunctorLift.lift z ◁ βw) ∙ comp-assoc bw rC (FunctorLift.lift z)) tail

    square : (βzw ∙ (rD ◁ FunctorOverIso.underlying Composite.comparison)) =₂ (boundary ∙ tail)
    square = normalization ⁻¹ ∙
      (cancel-inverse βzw normal ∙ isoComp-cong (idIso βzw) (ConeIso₂.leftId Composite.cone-computation))

module SourceCompatibility {A C D S T : CAT} (p : MAP S T)
  {e : MAP A T} {f : MAP C T} {g : MAP D T}
  (w : FunctorOver e f) (u v : FunctorOver f g) (Φ : FunctorOverIso u v) where
  module B = Change p using (cone; functor; module Identification; module Composite)
  module U = CompositeImage p w u
  module V = CompositeImage p w v
  α = FunctorOverIso.underlying Φ
  δ = FunctorOverIso.underlying (B.Identification.comparison Φ)
  δw = FunctorOverIso.underlying (B.Identification.comparison (prewhisker-over w Φ))
  cu = FunctorOverIso.underlying (B.Composite.comparison w u)
  cv = FunctorOverIso.underlying (B.Composite.comparison w v)
  left-native = compose-iso-over (B.Identification.comparison (prewhisker-over w Φ)) (B.Composite.comparison w u)
  right-native = compose-iso-over (B.Composite.comparison w v)
    (prewhisker-over (B.functor w) (B.Identification.comparison Φ))
  left = FunctorOverIso.underlying left-native
  right = FunctorOverIso.underlying right-native
  γ = (α ▷ FunctorLift.lift w) ▷ U.rA
  module Restricted = RestrictionSquare U.rC U.bw (FunctorLift.lift w) U.rA U.βw α
    using (naturality)

  opaque
    tail-square : (V.tail ∙ (U.rD ◁ (δ ▷ U.bw))) =₂ (((α ▷ U.rC) ▷ U.bw) ∙ U.tail)
    tail-square = pre-square-projection U.rD δ (α ▷ U.rC) U.βz V.βz U.bw
      (IdentificationImage.square p u v Φ)

    boundary-square : ((V.boundary ∙ V.tail) ∙ (U.rD ◁ (δ ▷ U.bw))) =₂
      (γ ∙ (U.boundary ∙ U.tail))
    boundary-square = paste-iso-squares U.tail V.tail U.boundary V.boundary
      (U.rD ◁ (δ ▷ U.bw)) ((α ▷ U.rC) ▷ U.bw) γ tail-square Restricted.naturality

    left-normal : (V.βzw ∙ (U.rD ◁ left)) =₂ (γ ∙ (U.boundary ∙ U.tail))
    left-normal = isoComp-cong (idIso γ) U.square ∙
      (isoComp-assoc-at γ U.βzw (U.rD ◁ cu) ∙
      (isoComp-cong (IdentificationImage.square p (compose-over u w) (compose-over v w) (prewhisker-over w Φ))
        (idIso (U.rD ◁ cu)) ∙
      ((isoComp-assoc-at V.βzw (U.rD ◁ δw) (U.rD ◁ cu)) ⁻¹ ∙
        isoComp-cong (idIso V.βzw) (postWhisker-isoComp-at U.rD δw cu))))

    right-normal : (V.βzw ∙ (U.rD ◁ right)) =₂ (γ ∙ (U.boundary ∙ U.tail))
    right-normal = boundary-square ∙
      (isoComp-cong V.square (idIso (U.rD ◁ (δ ▷ U.bw))) ∙
      ((isoComp-assoc-at V.βzw (U.rD ◁ cv) (U.rD ◁ (δ ▷ U.bw))) ⁻¹ ∙
        isoComp-cong (idIso V.βzw) (postWhisker-isoComp-at U.rD cv (δ ▷ U.bw))))

    first-projection : (U.rD ◁ left) =₂ (U.rD ◁ right)
    first-projection = cancel-left-reflect V.βzw (right-normal ⁻¹ ∙ left-normal)

    second-projection : (pullback₂ {f = g} {p} ◁ left) =₂ (pullback₂ {f = g} {p} ◁ right)
    second-projection = cancel-left-reflect (FunctorLift.comparison (B.functor (compose-over v w)))
      ((FunctorOverIso.compatible right-native) ⁻¹ ∙ FunctorOverIso.compatible left-native)
```
