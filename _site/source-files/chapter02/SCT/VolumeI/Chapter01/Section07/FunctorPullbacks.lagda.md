# Functor categories preserve pullbacks

The mapped cone curries the original cone restricted along evaluation.
Its legs are the actual postcomposition functors; its matching is the
chosen native reflected matching with the complete curried evaluation beta.
Universal factorization, that full beta and whole-cone reflection prove
`lem:Functor_Category_Preserves_Pullbacks`.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section07.FunctorPullbacks where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares
open import SCT.VolumeI.Chapter01.Section06.PullbackConstructions using (pullback-cone-isPullback)
open import SCT.VolumeI.Chapter01.Section07.Evaluation
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories
open import SCT.VolumeI.Chapter01.Section07.Currying
open import SCT.VolumeI.Chapter01.Section07.Functoriality
open import SCT.VolumeI.Chapter01.Section07.FunctorCones
open import SCT.VolumeI.Chapter01.Section07.FunctorConeRestriction

module _ {Γ : Context} {C D E S : CAT Γ} {f : MAP C E} {g : MAP D E} (K : CAT Γ) where
  mappedCone : Cone f g S → Cone (funPost {C = K} f) (funPost {C = K} g) (Fun K S)
  mappedCone s = FunctorCones.CurriedCone.value K f g
    (cone-restrict (funEval {C = K} {D = S}) s)

  mappedCone-evaluation : (s : Cone f g S)
    → ConeIdentification₁ (FunctorCones.uncurryCone K f g (mappedCone s))
        (cone-restrict (funEval {C = K} {D = S}) s)
  mappedCone-evaluation s = FunctorCones.CurriedCone.comparison K f g
    (cone-restrict (funEval {C = K} {D = S}) s)

  mappedCone-restrict-evaluation : {T : CAT Γ} (s : Cone f g S) (h : MAP T (Fun K S))
    → ConeIdentification₁ (FunctorCones.uncurryCone K f g (cone-restrict h (mappedCone s)))
        (cone-restrict (funUncurry {C = K} {D = S} h) s)
  mappedCone-restrict-evaluation s h = cone-compose
    (cone-restrict-assoc (productMap h (id K)) (funEval {C = K} {D = S}) s)
    (cone-compose (cone-identification-restrict-One (productMap h (id K)) (mappedCone-evaluation s))
      (uncurryCone-restrict K f g h (mappedCone s)))

  module Preservation (s : Cone f g S) (universal : IsPullback s) where
    private
      module U = UniversalCone s universal
      eS = funEval {C = K} {D = S}

    factor : {T : CAT Γ} → Cone (funPost {C = K} f) (funPost {C = K} g) T → MAP T (Fun K S)
    factor t = funCurry {C = K} {D = S} (U.factor (FunctorCones.uncurryCone K f g t))

    β : {T : CAT Γ} (t : Cone (funPost {C = K} f) (funPost {C = K} g) T)
      → ConeIdentification₁ (cone-restrict (factor t) (mappedCone s)) t
    β t = cone-identification-One
      (FunctorCones.ReflectedCone.value K f g (cone-restrict (factor t) (mappedCone s)) t
        (cone-identification (cone-compose (U.β (FunctorCones.uncurryCone K f g t))
          (cone-compose (cone-action-One s
              (funCurry-β {C = K} {D = S} (U.factor (FunctorCones.uncurryCone K f g t))))
            (mappedCone-restrict-evaluation s (factor t))))))

    reflect-cones : (h k : MAP (Fun K S) (Fun K S))
      → ConeIdentification₁ (cone-restrict h (mappedCone s)) (cone-restrict k (mappedCone s)) → h =₁ k
    reflect-cones h k Φ = SCT.VolumeI.Chapter01.Section07.Currying.reflect eS (funUniversal K S) h k
      (U.reflect (funUncurry {C = K} {D = S} h) (funUncurry {C = K} {D = S} k)
        (cone-compose (mappedCone-restrict-evaluation s k)
          (cone-compose (cone-identification-One
              (FunctorCones.uncurryCone-identification K f g (cone-identification Φ)))
            (cone-inverse (mappedCone-restrict-evaluation s h)))))

    isPullback : IsPullback (mappedCone s)
    isPullback = pullback-recognize (mappedCone s) factor β reflect-cones

  fun-preserves-pullback : (s : Cone f g S) → IsPullback s → IsPullback (mappedCone s)
  fun-preserves-pullback = Preservation.isPullback

module FunctorPullback {Γ : Context} (K : CAT Γ) {C D E : CAT Γ} (f : MAP C E) (g : MAP D E) where
  Source = Fun K (Pullback f g)
  Target = Pullback (funPost {C = K} f) (funPost {C = K} g)
  square : Cone (funPost {C = K} f) (funPost {C = K} g) Source
  square = mappedCone K (pullback-cone f g)

  comparison : MAP Source Target
  comparison = pullback-factor square

  comparison-computation : ConeIdentification₁
    (cone-restrict comparison (pullback-cone (funPost {C = K} f) (funPost {C = K} g))) square
  comparison-computation = pullback-factor-β square

  comparison-isEquiv : IsEquiv comparison
  comparison-isEquiv = fun-preserves-pullback K (pullback-cone f g) (pullback-cone-isPullback f g)
```
