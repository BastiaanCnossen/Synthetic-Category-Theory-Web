# Coslice equivalences induced by an adjunction

Transposition for arbitrary parameter categories gives an equivalence of
relative coslices over the parameter category. The endpoint presentations
retain their complete pullback comparisons. Both inverse identifications
are then taken over the base, not merely between the total functors.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter04.Section04.CosliceAdjunctions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter04.Section03.RelativeSlices 𝒯 M ℱ P I using (module RelativeCoslice)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
  using (FunctorOver; compose-over; identity-over)
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P using (FunctorOverIso)
import SCT.VolumeI.Chapter03.RelativeCategories.Equivalences as Relative
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.RelativeCoslicePresentation as Presentation
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberEquivalences as Frames
import SCT.VolumeI.Chapter04.Section04.HomAdjunctions as Transposition
import SCT.VolumeI.Chapter01.Section06.Cospans.ConeAction as ConeActions
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; ConeIso; conePre; coneIso-compose; coneIso-inverse; coneIso-pre; conePre-assoc)
open Laws.PullbackStructure P using (pullbackCone)

module At {B C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) (b : Obj-abs C) (y : MAP B D) where
  module Left = RelativeCoslice y (l ∘ b)
  module Right = RelativeCoslice (r ∘ y) b
  private
    module LP = Presentation.At 𝒯 M ℱ P I y (l ∘ b)
      using (functor; isEquiv; over-base)
    module RP = Presentation.At 𝒯 M ℱ P I (r ∘ y) b
      using (functor; isEquiv; over-base)
    module LI = Relative.Inverse 𝒯 M ℱ P LP.over-base LP.isEquiv
      using (inverse)
    module Change = Frames.ChangeEndpoints 𝒯 M ℱ P I
      {u = const {P = B} (l ∘ b)} {v = y}
      {u′ = l ∘ const b} {v′ = y}
      (comp-assoc (terminate B) b l) (idIso y)
      using (map; map-isEquiv; projection)
    module H = Transposition.HomEquivalence 𝒯 M ℱ P I E S Q adj (const {P = B} b) y
      using (functor; isEquiv; over-base)
    change-over : FunctorOver (EndpointFiber.base (const (l ∘ b)) y)
      (EndpointFiber.base (l ∘ const b) y)
    change-over = record { lift = Change.map ; comparison = Change.projection }

  over-base : FunctorOver Left.projection Right.projection
  over-base = compose-over RP.over-base
    (compose-over H.over-base (compose-over change-over LI.inverse))

  functor : MAP Left.category Right.category
  functor = FunctorLift.lift over-base

  private
    -- The chosen relative inverse need not be the bare IsEquiv inverse.
    module LInverse = Relative.Inverse 𝒯 M ℱ P LP.over-base LP.isEquiv
      using (left-inverse; right-inverse)
  abstract
    inverse-presentation-isEquiv : IsEquiv (FunctorLift.lift LI.inverse)
    inverse-presentation-isEquiv = record
      { inverse = LP.functor
      ; sectionIso = (FunctorOverIso.underlying LInverse.right-inverse) ⁻¹
      ; retractionIso = (FunctorOverIso.underlying LInverse.left-inverse) ⁻¹ }

    isEquiv : IsEquiv functor
    isEquiv = equiv-compose
      (H.functor ∘ (Change.map ∘ FunctorLift.lift LI.inverse)) RP.functor
      (equiv-compose (Change.map ∘ FunctorLift.lift LI.inverse) H.functor
        (equiv-compose (FunctorLift.lift LI.inverse) Change.map
          inverse-presentation-isEquiv Change.map-isEquiv) H.isEquiv) RP.isEquiv

  private
    module Inverse = Relative.Inverse 𝒯 M ℱ P over-base isEquiv
      using (inverse; left-inverse; right-inverse)
  open Inverse public renaming
    (inverse to inverse-over-base; left-inverse to left-inverse-over-base;
     right-inverse to right-inverse-over-base)
```


The absolute coslice form uses the identity target family directly. Its
source is the ordinary coslice, avoiding an extra pullback along the
identity functor.

```agda
module Absolute {C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) (b : Obj-abs C) where
  module Right = RelativeCoslice r b
  private
    module LP = Frames.ChangeEndpoints 𝒯 M ℱ P I
      {u = const {P = D} (l ∘ b)} {v = id D}
      {u′ = l ∘ const b} {v′ = id D}
      (comp-assoc (terminate D) b l) (idIso (id D))
      using (map; map-isEquiv; projection)
    module H = Transposition.HomEquivalence 𝒯 M ℱ P I E S Q adj (const {P = D} b) (id D)
      using (functor; isEquiv; over-base; forward-cone; forward-computation)
    module RP = Frames.ChangeEndpoints 𝒯 M ℱ P I
      {u = const {P = D} b} {v = r ∘ id D}
      {u′ = const b} {v′ = r}
      (idIso (const b)) (comp-unitʳ r)
      using (map; map-isEquiv; projection; change; map-β)
    module Target = Presentation.At 𝒯 M ℱ P I r b
      using (functor; isEquiv; over-base; comparison; square)
    left-over : FunctorOver (coslice-projection (l ∘ b))
      (EndpointFiber.base (l ∘ const b) (id D))
    left-over = record { lift = LP.map ; comparison = LP.projection }
    right-over : FunctorOver (EndpointFiber.base (const b) (r ∘ id D))
      (EndpointFiber.base (const b) r)
    right-over = record { lift = RP.map ; comparison = RP.projection }

  over-base : FunctorOver (coslice-projection (l ∘ b)) Right.projection
  over-base = compose-over Target.over-base
    (compose-over right-over (compose-over H.over-base left-over))

  functor : MAP (Coslice D (l ∘ b)) Right.category
  functor = FunctorLift.lift over-base

  abstract
    isEquiv : IsEquiv functor
    isEquiv = equiv-compose (RP.map ∘ (H.functor ∘ LP.map)) Target.functor
      (equiv-compose (H.functor ∘ LP.map) RP.map
        (equiv-compose LP.map H.functor LP.map-isEquiv H.isEquiv) RP.map-isEquiv)
      Target.isEquiv

  equivalence : Equiv (Coslice D (l ∘ b)) Right.category
  equivalence = record { functor = functor ; isEquiv = isEquiv }

  private
    module Inverse = Relative.Inverse 𝒯 M ℱ P over-base isEquiv
      using (inverse; left-inverse; right-inverse)
  open Inverse public renaming
    (inverse to inverse-over-base; left-inverse to left-inverse-over-base;
     right-inverse to right-inverse-over-base)

  transposed : MAP (Coslice D (l ∘ b)) (EndpointFiber.category (const b) r)
  transposed = RP.map ∘ (H.functor ∘ LP.map)

  transposed-cone : Cone endpoints (pair (const b) r) (Coslice D (l ∘ b))
  transposed-cone = CospanMap.mapCone RP.change (conePre LP.map H.forward-cone)
  private
    module Action = ConeActions.Action 𝒯 P RP.change using (map-iso; map-pre)
    middle-computation : ConeIso
      (conePre (H.functor ∘ LP.map) (pullbackCone endpoints (pair (const b) (r ∘ id D))))
      (conePre LP.map H.forward-cone)
    middle-computation = coneIso-compose (coneIso-pre LP.map H.forward-computation)
      (coneIso-inverse (conePre-assoc LP.map H.functor
        (pullbackCone endpoints (pair (const b) (r ∘ id D)))))

  private
    middle = H.functor ∘ LP.map
    source-cone = pullbackCone endpoints (pair (const b) (r ∘ id D))
    target-cone = pullbackCone endpoints (pair (const b) r)
    abstract
      associate-transposed : ConeIso (conePre transposed target-cone)
        (conePre middle (conePre RP.map target-cone))
      associate-transposed = coneIso-inverse (conePre-assoc middle RP.map target-cone)
      compute-frame-change : ConeIso (conePre middle (conePre RP.map target-cone))
        (conePre middle (CospanMap.mapCone RP.change source-cone))
      compute-frame-change = coneIso-pre middle RP.map-β
      restrict-frame-change : ConeIso
        (conePre middle (CospanMap.mapCone RP.change source-cone))
        (CospanMap.mapCone RP.change (conePre middle source-cone))
      restrict-frame-change = coneIso-inverse (Action.map-pre middle source-cone)
      compute-transposition : ConeIso
        (CospanMap.mapCone RP.change (conePre middle source-cone)) transposed-cone
      compute-transposition = Action.map-iso middle-computation

  abstract
    transposed-computation : ConeIso
      (conePre transposed (pullbackCone endpoints (pair (const b) r))) transposed-cone
    transposed-computation = coneIso-compose compute-transposition
      (coneIso-compose restrict-frame-change
        (coneIso-compose compute-frame-change associate-transposed))

    coslice-projection-computation : (Right.diagram ∘ functor) =₁ (Cone.left Target.square ∘ transposed)
    coslice-projection-computation = (ConeIso.leftIso Target.comparison ▷ transposed) ∙
      (comp-assoc transposed Target.functor Right.diagram) ⁻¹
```

