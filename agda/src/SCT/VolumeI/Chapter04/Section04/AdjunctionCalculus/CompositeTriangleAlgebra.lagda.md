# The component calculation for a composite adjunction

The expanded unit and counit of two adjunctions satisfy both component
triangles. Each calculation uses one naturality square and the two given
triangle equations. Comparisons with the globally framed composite unit
and counit are a separate step.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.CompositeTriangleAlgebra
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.SealedComponents as Sealed

module At (Γ : CAT) where
  module X = Sealed.At 𝒯 M ℱ P I E S Q Γ
  module K = X.K

  abstract
    middle : {C : CAT} {x₀ x₁ x₂ x₃ x₄ : MAP Γ C}
      (a₀ : MorphismExpression x₀ x₁) (b₀ : MorphismExpression x₁ x₂)
      (c₀ : MorphismExpression x₂ x₃) (d₀ : MorphismExpression x₃ x₄) →
      ExpressionIso (K.composite (K.composite a₀ b₀) (K.composite c₀ d₀))
        (K.composite a₀ (K.composite (K.composite b₀ c₀) d₀))
    middle a₀ b₀ c₀ d₀ = expressionIso-compose
      (K.composite-cong (expressionIso-id a₀) (K.associative b₀ c₀ d₀))
      (expressionIso-inverse (K.associative a₀ b₀ (K.composite c₀ d₀)))

    exchange : {C : CAT} {x₀ x₁ x₂ x₃ x₄ x₂′ : MAP Γ C}
      (a₀ : MorphismExpression x₀ x₁) (b₀ : MorphismExpression x₁ x₂)
      (c₀ : MorphismExpression x₂ x₃) (d₀ : MorphismExpression x₃ x₄)
      (c₁ : MorphismExpression x₁ x₂′) (b₁ : MorphismExpression x₂′ x₃) →
      ExpressionIso (K.composite b₀ c₀) (K.composite c₁ b₁) →
      ExpressionIso (K.composite (K.composite a₀ b₀) (K.composite c₀ d₀))
        (K.composite (K.composite a₀ c₁) (K.composite b₁ d₀))
    exchange a₀ b₀ c₀ d₀ c₁ b₁ same = expressionIso-compose
      (expressionIso-inverse (middle a₀ c₁ b₁ d₀))
      (expressionIso-compose
        (K.composite-cong (expressionIso-id a₀) (K.composite-cong same (expressionIso-id d₀)))
        (middle a₀ b₀ c₀ d₀))

    double-post-composite : {B C D : CAT} (F : MAP B C) (G : MAP C D)
      {x y z : MAP Γ B} (u : MorphismExpression x y) (v : MorphismExpression y z) →
      ExpressionIso (K.post G (K.post F (K.composite u v)))
        (K.composite (K.post G (K.post F u)) (K.post G (K.post F v)))
    double-post-composite F G u v = expressionIso-compose
      (expressionIso-inverse (K.post-composite G (K.post F u) (K.post F v)))
      (X.post-cong G (expressionIso-inverse (K.post-composite F u v)))

  module Composite {C D T : CAT} {l : MAP C D} {r : MAP D C}
    {k : MAP D T} {s : MAP T D} (a₀ : Adjunction l r) (b₀ : Adjunction k s) where
    module A = Adjunction a₀ using (unit-at; counit-at)
    module B = Adjunction b₀ using (unit-at; counit-at)
    module AC = X.Components a₀
    module BC = X.Components b₀

    expanded-unit : (x : MAP Γ C) → MorphismExpression x (r ∘ (s ∘ (k ∘ (l ∘ x))))
    expanded-unit x = K.composite (A.unit-at x) (K.post r (B.unit-at (l ∘ x)))

    expanded-counit : (y : MAP Γ T) → MorphismExpression (k ∘ (l ∘ (r ∘ (s ∘ y)))) y
    expanded-counit y = K.composite (K.post k (A.counit-at (s ∘ y))) (B.counit-at y)

    abstract
      left-triangle : (x : MAP Γ C) →
        ExpressionIso
          (K.composite (K.post k (K.post l (expanded-unit x))) (expanded-counit (k ∘ (l ∘ x))))
          (K.identity (k ∘ (l ∘ x)))
      left-triangle x = expressionIso-compose (BC.left-triangle (l ∘ x))
        (expressionIso-compose (K.unit-left (K.composite bb₁ dd))
          (expressionIso-compose
            (K.composite-cong
              (expressionIso-compose (K.post-unit k (l ∘ x))
                (expressionIso-compose (X.post-cong k (AC.left-triangle x))
                  (K.post-composite k (K.post l (A.unit-at x)) (A.counit-at (l ∘ x)))))
              (expressionIso-id (K.composite bb₁ dd)))
            (expressionIso-compose
              (exchange aa bb cc dd cc₁ bb₁
                (expressionIso-compose (expressionIso-inverse (K.post-composite k (A.counit-at (l ∘ x)) (B.unit-at (l ∘ x))))
                  (expressionIso-compose (X.post-cong k (AC.counit-natural (B.unit-at (l ∘ x))))
                    (K.post-composite k (K.post l (K.post r (B.unit-at (l ∘ x)))) (A.counit-at (s ∘ (k ∘ (l ∘ x))))))))
              (K.composite-cong
                (double-post-composite l k (A.unit-at x) (K.post r (B.unit-at (l ∘ x))))
                (expressionIso-id (expanded-counit (k ∘ (l ∘ x))))))))
        where
        aa : MorphismExpression (k ∘ (l ∘ x)) (k ∘ (l ∘ (r ∘ (l ∘ x))))
        aa = K.post k (K.post l (A.unit-at x))
        bb : MorphismExpression (k ∘ (l ∘ (r ∘ (l ∘ x)))) (k ∘ (l ∘ (r ∘ (s ∘ (k ∘ (l ∘ x))))))
        bb = K.post k (K.post l (K.post r (B.unit-at (l ∘ x))))
        cc : MorphismExpression (k ∘ (l ∘ (r ∘ (s ∘ (k ∘ (l ∘ x)))))) (k ∘ (s ∘ (k ∘ (l ∘ x))))
        cc = K.post k (A.counit-at (s ∘ (k ∘ (l ∘ x))))
        dd : MorphismExpression (k ∘ (s ∘ (k ∘ (l ∘ x)))) (k ∘ (l ∘ x))
        dd = B.counit-at (k ∘ (l ∘ x))
        cc₁ : MorphismExpression (k ∘ (l ∘ (r ∘ (l ∘ x)))) (k ∘ (l ∘ x))
        cc₁ = K.post k (A.counit-at (l ∘ x))
        bb₁ : MorphismExpression (k ∘ (l ∘ x)) (k ∘ (s ∘ (k ∘ (l ∘ x))))
        bb₁ = K.post k (B.unit-at (l ∘ x))

      right-triangle : (y : MAP Γ T) →
        ExpressionIso
          (K.composite (expanded-unit (r ∘ (s ∘ y))) (K.post r (K.post s (expanded-counit y))))
          (K.identity (r ∘ (s ∘ y)))
      right-triangle y = expressionIso-compose (K.post-unit r (s ∘ y))
        (expressionIso-compose (X.post-cong r (BC.right-triangle y))
          (expressionIso-compose (K.post-composite r (B.unit-at (s ∘ y)) (K.post s (B.counit-at y)))
            (expressionIso-compose (K.unit-left (K.composite bb₁ dd))
              (expressionIso-compose (K.composite-cong (AC.right-triangle (s ∘ y)) (expressionIso-id (K.composite bb₁ dd)))
                (expressionIso-compose
                  (exchange aa bb cc dd cc₁ bb₁
                    (expressionIso-compose (expressionIso-inverse (K.post-composite r (A.counit-at (s ∘ y)) (B.unit-at (s ∘ y))))
                      (expressionIso-compose (X.post-cong r (BC.unit-natural (A.counit-at (s ∘ y))))
                        (K.post-composite r (B.unit-at (l ∘ (r ∘ (s ∘ y)))) (K.post s (K.post k (A.counit-at (s ∘ y))))))))
                  (K.composite-cong (expressionIso-id (expanded-unit (r ∘ (s ∘ y))))
                    (double-post-composite s r (K.post k (A.counit-at (s ∘ y))) (B.counit-at y))))))))
        where
        aa : MorphismExpression (r ∘ (s ∘ y)) (r ∘ (l ∘ (r ∘ (s ∘ y))))
        aa = A.unit-at (r ∘ (s ∘ y))
        bb : MorphismExpression (r ∘ (l ∘ (r ∘ (s ∘ y)))) (r ∘ (s ∘ (k ∘ (l ∘ (r ∘ (s ∘ y))))))
        bb = K.post r (B.unit-at (l ∘ (r ∘ (s ∘ y))))
        cc : MorphismExpression (r ∘ (s ∘ (k ∘ (l ∘ (r ∘ (s ∘ y)))))) (r ∘ (s ∘ (k ∘ (s ∘ y))))
        cc = K.post r (K.post s (K.post k (A.counit-at (s ∘ y))))
        dd : MorphismExpression (r ∘ (s ∘ (k ∘ (s ∘ y)))) (r ∘ (s ∘ y))
        dd = K.post r (K.post s (B.counit-at y))
        cc₁ : MorphismExpression (r ∘ (l ∘ (r ∘ (s ∘ y)))) (r ∘ (s ∘ y))
        cc₁ = K.post r (A.counit-at (s ∘ y))
        bb₁ : MorphismExpression (r ∘ (s ∘ y)) (r ∘ (s ∘ (k ∘ (s ∘ y))))
        bb₁ = K.post r (B.unit-at (s ∘ y))
```
