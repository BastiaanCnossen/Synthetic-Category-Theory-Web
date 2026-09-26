# Functors over a category

For `def:Relative_Functor_Category_Global_Sections`, take the fiber of
postcomposition over the specified structure functor. The pullback
retains the identification making the triangle commute.

`FunOver` is the category of functors over the base; `MapOver` is its
core. These are categories of global functors, as distinct from the
relative internal functor category constructed later in this section.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.Whiskering as WhiskeringEquivalences

module SCT.VolumeI.Chapter03.RelativeCategories.Functors
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Categories.FunctorCategories ℱ using (Fun)
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section04.Core 𝒯 M using (Core; core-isAn; coreInclusion; core-universal)
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M ℱ using (funPost)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting 𝒯 P using (pullback-reflect)
open import SCT.VolumeI.Chapter03.Section04.CoconeCalculus.DiagramInterchange 𝒯 M ℱ
  using (post-nameFun; decodeFun-cong)
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.NamingIdentifications 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯
  using (coneRetarget; coneRetarget-β; coneIso-compose; coneIso-inverse; cone-match-change)
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.CoreInclusions 𝒯 M using (coreInclusion-name)
open import SCT.VolumeI.Chapter01.Section04.EquivalenceDetection 𝒯 M using (mapPost-reflect)
open WhiskeringEquivalences vocabulary terminal products productLaws composition vertical whiskering
  using (leftMultiply; rightMultiply; leftMultiply-isEquiv; rightMultiply-isEquiv)

FunctorOver : {C D S : CAT} → MAP C S → MAP D S → Set m
FunctorOver f g = FunctorLift g f

identity-over : {C S : CAT} (f : MAP C S) → FunctorOver f f
identity-over f = record { lift = id _ ; comparison = comp-unitʳ f }

compose-over : {B C D S : CAT} {f : MAP B S} {g : MAP C S} {h : MAP D S} →
  FunctorOver g h → FunctorOver f g → FunctorOver f h
compose-over {h = h} v u = record
  { lift = FunctorLift.lift v ∘ FunctorLift.lift u
  ; comparison = FunctorLift.comparison u ∙
      ((FunctorLift.comparison v ▷ FunctorLift.lift u) ∙
        (comp-assoc (FunctorLift.lift u) (FunctorLift.lift v) h) ⁻¹) }

FunOver : {C D S : CAT} → MAP C S → MAP D S → CAT
FunOver f g = Pullback (funPost g) (nameFun f)

MapOver : {C D S : CAT} → MAP C S → MAP D S → CAT
MapOver f g = Core (FunOver f g)

mapOver-isAn : {C D S : CAT} (f : MAP C S) (g : MAP D S) → isAn (MapOver f g)
mapOver-isAn f g = core-isAn (FunOver f g)

module Over {C D S : CAT} (f : MAP C S) (g : MAP D S) where
  forget : MAP (FunOver f g) (Fun C D)
  forget = pullback₁

  matching : (funPost g ∘ forget) =₁ (nameFun f ∘ pullback₂)
  matching = pullbackMatch

  intro : {X : CAT} → Cone (funPost g) (nameFun f) X → MAP X (FunOver f g)
  intro = pullbackLift

  intro-β : {X : CAT} (s : Cone (funPost g) (nameFun f) X) →
    ConeIso (conePre (intro s) (pullbackCone (funPost g) (nameFun f))) s
  intro-β = pullbackLift-β

  reflect : {X : CAT} (u v : MAP X (FunOver f g)) →
    ConeIso (conePre u (pullbackCone (funPost g) (nameFun f)))
      (conePre v (pullbackCone (funPost g) (nameFun f))) → u =₁ v
  reflect = pullback-reflect

  triangleNameMap : (h : MAP C D) →
    MAP ((g ∘ h) ＝ f) ((funPost g ∘ nameFun h) ＝ (nameFun f ∘ id One))
  triangleNameMap h = leftMultiply ((comp-unitʳ (nameFun f)) ⁻¹) ∘
    (rightMultiply (post-nameFun g h) ∘ nameFun-isoMap (g ∘ h) f)

  triangleNameMap-isEquiv : (h : MAP C D) → IsEquiv (triangleNameMap h)
  triangleNameMap-isEquiv h = equiv-compose
    (rightMultiply (post-nameFun g h) ∘ nameFun-isoMap (g ∘ h) f)
    (leftMultiply ((comp-unitʳ (nameFun f)) ⁻¹))
    (equiv-compose (nameFun-isoMap (g ∘ h) f) (rightMultiply (post-nameFun g h))
      (nameFun-isoMap-isEquiv (g ∘ h) f) (rightMultiply-isEquiv (post-nameFun g h)))
    (leftMultiply-isEquiv ((comp-unitʳ (nameFun f)) ⁻¹))

  module Name (u : FunctorOver f g) where
    cone : Cone (funPost g) (nameFun f) One
    cone = record
      { left = nameFun (FunctorLift.lift u)
      ; right = id One
      ; match = triangleNameMap (FunctorLift.lift u) ∘ FunctorLift.comparison u }

    object : Obj-abs (FunOver f g)
    object = intro cone

    comparison : ConeIso (conePre object (pullbackCone (funPost g) (nameFun f))) cone
    comparison = intro-β cone

  module Decode (x : Obj-abs (FunOver f g)) where
    cone = conePre x (pullbackCone (funPost g) (nameFun f))
    functor : MAP C D
    functor = decodeFun (forget ∘ x)

    normalized : Cone (funPost g) (nameFun f) One
    normalized = coneRetarget cone (nameFun functor) (id One)
      ((name-decodeFun (forget ∘ x)) ⁻¹) (terminal-iso _ _)

    chosen : FunctorLift (triangleNameMap functor) (Cone.match normalized)
    chosen = equiv-lift (triangleNameMap-isEquiv functor) (Cone.match normalized)

    over : (g ∘ functor) =₁ f
    over = FunctorLift.lift chosen

    triangle : FunctorOver f g
    triangle = record { lift = functor ; comparison = over }

    matching-comparison : Cone.match (Name.cone triangle) =₂ Cone.match normalized
    matching-comparison = FunctorLift.comparison chosen

    cone-comparison : ConeIso (Name.cone triangle) cone
    cone-comparison = coneIso-compose
      (coneIso-inverse (coneRetarget-β cone (nameFun functor) (id One)
        ((name-decodeFun (forget ∘ x)) ⁻¹) (terminal-iso _ _)))
      (cone-match-change _ _ _ _ matching-comparison)

    object-roundtrip : Name.object triangle =₁ x
    object-roundtrip = reflect _ _ (coneIso-compose cone-comparison (Name.comparison triangle))

  opaque
    name-over : FunctorOver f g → Obj-abs (MapOver f g)
    name-over u = nameMap (Name.object u)

  opaque
    unfolding name-over
    decode-over : Obj-abs (MapOver f g) → FunctorOver f g
    decode-over x = Decode.triangle (coreInclusion (FunOver f g) ∘ x)
  
    decoded-cone : (x : Obj-abs (MapOver f g)) →
      ConeIso (Name.cone (decode-over x))
        (conePre (coreInclusion (FunOver f g) ∘ x) (pullbackCone (funPost g) (nameFun f)))
    decoded-cone x = Decode.cone-comparison (coreInclusion (FunOver f g) ∘ x)

    named-cone : (u : FunctorOver f g) →
      ConeIso (conePre (coreInclusion (FunOver f g) ∘ name-over u)
        (pullbackCone (funPost g) (nameFun f))) (Name.cone u)
    named-cone u = coneIso-compose (Name.comparison u)
      (cone-action (pullbackCone (funPost g) (nameFun f)) (coreInclusion-name (Name.object u)))

    decode-identification-cone : {x y : Obj-abs (MapOver f g)} → x =₁ y →
      ConeIso (Name.cone (decode-over x)) (Name.cone (decode-over y))
    decode-identification-cone {x} {y} α = coneIso-compose (coneIso-inverse (decoded-cone y))
      (coneIso-compose
        (cone-action (pullbackCone (funPost g) (nameFun f)) (coreInclusion (FunOver f g) ◁ α))
        (decoded-cone x))

    identify-cones : (u v : FunctorOver f g) → name-over u =₁ name-over v →
      ConeIso (Name.cone u) (Name.cone v)
    identify-cones u v α = coneIso-compose (named-cone v)
      (coneIso-compose
        (cone-action (pullbackCone (funPost g) (nameFun f)) (coreInclusion (FunOver f g) ◁ α))
        (coneIso-inverse (named-cone u)))

    decode-name-cone : (u : FunctorOver f g) →
      ConeIso (Name.cone (decode-over (name-over u))) (Name.cone u)
    decode-name-cone u = coneIso-compose (named-cone u) (decoded-cone (name-over u))

    name-decode-over : (x : Obj-abs (MapOver f g)) → name-over (decode-over x) =₁ x
    name-decode-over x = mapPost-reflect (coreInclusion (FunOver f g))
      (core-universal One (FunOver f g) one-isAn) _ _
      (Decode.object-roundtrip (coreInclusion (FunOver f g) ∘ x) ∙
        coreInclusion-name (Name.object (decode-over x)))

    decode-underlying : (x : Obj-abs (MapOver f g)) →
      FunctorLift.lift (decode-over x) =₁ decodeFun (forget ∘ (coreInclusion (FunOver f g) ∘ x))
    decode-underlying x = idIso _

    named-cones-identify : (u v : FunctorOver f g) →
      ConeIso (Name.cone u) (Name.cone v) → name-over u =₁ name-over v
    named-cones-identify u v Φ = nameMapIso
      (reflect (Name.object u) (Name.object v)
        (coneIso-compose (coneIso-inverse (Name.comparison v))
          (coneIso-compose Φ (Name.comparison u))))

    decode-identification : {x y : Obj-abs (MapOver f g)} → x =₁ y →
      FunctorLift.lift (decode-over x) =₁ FunctorLift.lift (decode-over y)
    decode-identification α = decodeFun-cong (forget ◁ (coreInclusion (FunOver f g) ◁ α))

    named-forget : (u : FunctorOver f g) →
      (forget ∘ (coreInclusion (FunOver f g) ∘ name-over u)) =₁ nameFun (FunctorLift.lift u)
    named-forget u = ConeIso.leftIso (Name.comparison u) ∙
      (forget ◁ coreInclusion-name (Name.object u))

    decode-name-over : (u : FunctorOver f g) →
      FunctorLift.lift (decode-over (name-over u)) =₁ FunctorLift.lift u
    decode-name-over u = decode-nameFun (FunctorLift.lift u) ∙
      decodeFun-cong (named-forget u)

    identify-underlying : (u v : FunctorOver f g) → name-over u =₁ name-over v →
      FunctorLift.lift u =₁ FunctorLift.lift v
    identify-underlying u v α = decode-name-over v ∙
      (decode-identification α ∙ (decode-name-over u) ⁻¹)

```

The introduction comparison is a comparison of the entire cone, including
its matching. Thus the commutativity identification is part of the
constructed object, rather than an equation discarded after choosing
the underlying functor.

`Over.decode-name-cone` is the roundtrip statement for the entire named
triangle. Its compatibility field compares the matching identifications.
`Over.identify-cones` similarly retains the triangles when reflecting an
identification of relative mapping points. `Over.decode-name-over` separately gives a convenient comparison of the
underlying functors. No equality between those two chosen comparisons is
asserted.
