# Relative mapping animae

The relative mapping anima is the core of the relative functor category.
Apply `Map One` to its defining fiber square, then compare the three
cospan vertices with `Map C D`, `Map C S` and `One`. The comparison uses
actual postcomposition and the named structural functor, including both
commutativity identifications.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section09.RelativeMappingAnimae where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (comp-unitˡ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section03.Equivalences
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
import SCT.VolumeI.Chapter01.Section04.Currying as Mapping
import SCT.VolumeI.Chapter01.Section04.Functoriality as Maps
open import SCT.VolumeI.Chapter01.Section04.Points using (name; name-representation)
open import SCT.VolumeI.Chapter01.Section04.Core
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section06.ConeTransport
open import SCT.VolumeI.Chapter01.Section06.ConeUniversality
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares
open import SCT.VolumeI.Chapter01.Section06.PullbackConstructions
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctoriality
open import SCT.VolumeI.Chapter01.Section06.MappingPullbacks
open import SCT.VolumeI.Chapter01.Section07.Evaluation
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories
open import SCT.VolumeI.Chapter01.Section07.Functoriality
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun
open import SCT.VolumeI.Chapter01.Section09.NamedEvaluation
open import SCT.VolumeI.Chapter01.Section09.RelativeFunctorCategories

module _ {Γ : Context} where
  core-inclusion-natural : {C D : CAT Γ} (f : MAP C D)
    → (coreInclusion D ∘ Maps.mapPost {C = One} f) =₁
        (f ∘ coreInclusion C)
  core-inclusion-natural {C} {D} f =
    comp-assoc (product-unitʳ-inverse (Core C)) mapEval f ∙
      ((Maps.mapPost-β {C = One} f ▷ product-unitʳ-inverse (Core C)) ∙
        (core-evaluation (Maps.mapPost {C = One} f)) ⁻¹)

  private
    core-evaluation-restrict : {K C D : CAT Γ}
      (h : MAP K (Core (Fun C D)))
      → uncurry (coreFunUncurrying C D ∘ h) =₁
          evaluate (funEval {C = C} {D = D}) (coreInclusion (Fun C D) ∘ h)
    core-evaluation-restrict {C = C} {D} h =
      (evaluate-restrict (funEval {C = C} {D = D}) (coreInclusion (Fun C D)) h) ⁻¹ ∙
        ((coreFunUncurrying-evaluation C D ▷ productMap h (id C)) ∙
          Mapping.uncurry-restrict (coreFunUncurrying C D) h)

  core-fun-post : {C D E : CAT Γ} (q : MAP D E)
    → (Maps.mapPost {C = C} q ∘ coreFunUncurrying C D) =₁
        (coreFunUncurrying C E ∘ Maps.mapPost {C = One} (funPost {C = C} q))
  core-fun-post {C} {D} {E} q = Mapping.uncurry-reflect (core-isAn (Fun C D)) _ _
    (right-route ⁻¹ ∙ left-route)
    where
    e : MAP (Fun C E × C) E
    e = funEval {C = C} {D = E}
    left-route : uncurry (Maps.mapPost q ∘ coreFunUncurrying C D) =₁
      (q ∘ evaluate (funEval {C = C} {D = D}) (coreInclusion (Fun C D)))
    left-route = (q ◁ coreFunUncurrying-evaluation C D) ∙
      Maps.mapPost-uncurry q (coreFunUncurrying C D)
    right-route : uncurry (coreFunUncurrying C E ∘ Maps.mapPost {C = One} (funPost q)) =₁
      (q ∘ evaluate (funEval {C = C} {D = D}) (coreInclusion (Fun C D)))
    right-route = funPost-uncurry q (coreInclusion (Fun C D)) ∙
      (evaluate-cong e (core-inclusion-natural (funPost q)) ∙
        core-evaluation-restrict (Maps.mapPost {C = One} (funPost q)))

  core-fun-name : {C S : CAT Γ} (p : MAP C S)
    → (name p ∘ coreInclusion One) =₁
        (coreFunUncurrying C S ∘ Maps.mapPost {C = One} (funName p))
  core-fun-name {C} {S} p = Mapping.uncurry-reflect (core-isAn One) _ _
    (right-route ⁻¹ ∙ left-route)
    where
    z : MAP (Core One) One
    z = coreInclusion One
    left-route : uncurry (name p ∘ z) =₁ (p ∘ pr₂ {C = Core One} {D = C})
    left-route =
      (p ◁ (comp-unitˡ pr₂ ∙ pair-β₂ (z ∘ pr₁) (id C ∘ pr₂))) ∙
        (comp-assoc (productMap z (id C)) (pr₂ {C = One} {D = C}) p ∙
          ((Mapping.CurriedRepresentation.evaluation (name-representation p) ▷ productMap z (id C)) ∙
            Mapping.uncurry-restrict (name p) z))
    right-route : uncurry (coreFunUncurrying C S ∘ Maps.mapPost {C = One} (funName p)) =₁
      (p ∘ pr₂ {C = Core One} {D = C})
    right-route = NamedEvaluation.named-evaluation p z ∙
      (evaluate-cong (funEval {C = C} {D = S}) (core-inclusion-natural (funName p)) ∙
        core-evaluation-restrict (Maps.mapPost {C = One} (funName p)))

module RelativeMappingAnima {Γ : Context} {S : CAT Γ}
  (A B : CategoryOverBase S) where
  private
    C = CategoryOverBase.category A
    D = CategoryOverBase.category B
    p = CategoryOverBase.map A
    q = CategoryOverBase.map B
    module Relative = RelativeFunctorCategory A B

  anima : CAT Γ
  anima = Core Relative.category

  anima-isAn : isAn anima
  anima-isAn = core-isAn Relative.category

  core-fiber : Cone (Maps.mapPost {C = One} Relative.postcomposition)
    (Maps.mapPost {C = One} Relative.point) anima
  core-fiber = mapped-cone One Relative.fiber

  core-fiber-isPullback : IsPullback core-fiber
  core-fiber-isPullback = map-preserves-pullback One Relative.fiber
    (pullback-cone-isPullback Relative.postcomposition Relative.point)

  cospan-comparison : CospanMap
    (Maps.mapPost {C = One} Relative.postcomposition)
    (Maps.mapPost {C = One} Relative.point) (Maps.mapPost {C = C} q) (name p)
  cospan-comparison = record
    { left = coreFunUncurrying C D
    ; right = coreInclusion One
    ; base = coreFunUncurrying C S
    ; left-square = core-fun-post q
    ; right-square = core-fun-name p }
```

The chosen comparison of the core fiber with its pullback transports the
whole cone. The two leg computations restore the displayed projections.
Thus the matching below is specified by this transport and its full beta,
not inferred merely from equivalence of the corner animae.

```agda
  private
    source-cone = pullback-cone
      (Maps.mapPost {C = One} Relative.postcomposition)
      (Maps.mapPost {C = One} Relative.point)

    factor : MAP anima (Pullback
      (Maps.mapPost {C = One} Relative.postcomposition)
      (Maps.mapPost {C = One} Relative.point))
    factor = pullback-factor core-fiber

    mapped : Cone (Maps.mapPost {C = C} q) (name p)
      (Pullback (Maps.mapPost {C = One} Relative.postcomposition)
        (Maps.mapPost {C = One} Relative.point))
    mapped = CospanMap.map-cone cospan-comparison source-cone

    restricted : Cone (Maps.mapPost {C = C} q) (name p) anima
    restricted = cone-restrict factor mapped

  projection : MAP anima (Map C D)
  projection = coreFunUncurrying C D ∘ Cone.left core-fiber

  terminal-projection : MAP anima One
  terminal-projection = coreInclusion One ∘ Cone.right core-fiber

  private
    left-computation : Cone.left restricted =₁ projection
    left-computation =
      (coreFunUncurrying C D ◁ ConeIdentification₁.left (pullback-factor-β core-fiber)) ∙
        comp-assoc factor (Cone.left source-cone) (coreFunUncurrying C D)

    right-computation : Cone.right restricted =₁ terminal-projection
    right-computation =
      (coreInclusion One ◁ ConeIdentification₁.right (pullback-factor-β core-fiber)) ∙
        comp-assoc factor (Cone.right source-cone) (coreInclusion One)

  square : Cone (Maps.mapPost {C = C} q) (name p) anima
  square = cone-change-legs restricted projection terminal-projection
    left-computation right-computation

  comparison : MAP anima (Pullback (Maps.mapPost {C = C} q) (name p))
  comparison = pullback-map cospan-comparison ∘ factor

  comparison-whole-image : ConeIdentification₁
    (cone-restrict comparison (pullback-cone (Maps.mapPost {C = C} q) (name p))) square
  comparison-whole-image = cone-compose
    (cone-change-legs-β restricted projection terminal-projection left-computation right-computation)
    (cone-compose
      (cone-identification-restrict-One factor (pullback-map-β cospan-comparison))
      (cone-inverse (cone-restrict-assoc factor (pullback-map cospan-comparison)
        (pullback-cone (Maps.mapPost {C = C} q) (name p)))))

  comparison-isEquiv : IsEquiv comparison
  comparison-isEquiv = equiv-compose factor (pullback-map cospan-comparison)
    core-fiber-isPullback
    (CospanEquivalence.pullback-map-isEquiv cospan-comparison
      (coreFunUncurrying-isEquiv C D) (core-of-anima One one-isAn)
      (coreFunUncurrying-isEquiv C S))

  square-isPullback : IsPullback square
  square-isPullback = isPullback-cone-identification comparison-whole-image
    (equiv-transport
      ((pullback-factor-restrict comparison
        (pullback-cone (Maps.mapPost {C = C} q) (name p))) ⁻¹)
      (equiv-compose comparison
        (pullback-factor (pullback-cone (Maps.mapPost {C = C} q) (name p)))
        comparison-isEquiv (pullback-cone-isPullback (Maps.mapPost {C = C} q) (name p))))
```
