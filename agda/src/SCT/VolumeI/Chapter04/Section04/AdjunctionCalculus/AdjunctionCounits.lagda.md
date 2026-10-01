# An adjunction supplies universal counits

The counit factorization is transposition. One inverse equation proves
its factorization law; the other, together with congruence, proves that
it reflects comparisons. The resulting package is abstract so its users
can compare universal counits without expanding the transposition formulas.

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

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.AdjunctionCounits
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.UniversalCounits as Universal
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionCalculus 𝒯 M ℱ P I E S Q
  using (ExpressionCalculus; expression-calculus)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeIdentifications as Inverses
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeComparisons as Comparisons

UniversalCounit : {Γ C D : CAT} (l : MAP C D) (y : MAP Γ D) (r : MAP Γ C) → Set m
UniversalCounit {Γ} = Universal.At.UniversalCounit 𝒯 M ℱ P I E S Q Γ

private
  abstract
    reflect-with-inverse : {Γ C D : CAT} {x x′ : MAP Γ C} {y y′ : MAP Γ D}
      (encode : MorphismExpression x x′ → MorphismExpression y y′)
      (decode : MorphismExpression y y′ → MorphismExpression x x′) →
      ({α β : MorphismExpression y y′} → ExpressionIso α β → ExpressionIso (decode α) (decode β)) →
      ((f : MorphismExpression x x′) → ExpressionIso (decode (encode f)) f) →
      (f g : MorphismExpression x x′) → ExpressionIso (encode f) (encode g) → ExpressionIso f g
    reflect-with-inverse encode decode congruence inverse f g same =
      expressionIso-compose (inverse g)
        (expressionIso-compose (congruence same) (expressionIso-inverse (inverse f)))

abstract
  adjunction-counit : {Γ C D : CAT} {l : MAP C D} {r : MAP D C}
    (adj : Adjunction l r) (y : MAP Γ D) → UniversalCounit l y (r ∘ y)
  adjunction-counit {Γ} {l = l} adj y = record
    { counit = A.counit-at y
    ; factor = λ x → A.transpose x y
    ; factor-law = λ x f → expressionIso-compose (V.untranspose-transpose x y f)
        (K.action-comparison l (A.transpose x y f) (A.counit-at y))
    ; reflect = λ {x} f g same →
        reflect-with-inverse (A.untranspose x y) (A.transpose x y)
          (N.transpose-cong x y) (V.transpose-untranspose x y) f g
          (expressionIso-compose (K.action-comparison l g (A.counit-at y))
            (expressionIso-compose same
              (expressionIso-inverse (K.action-comparison l f (A.counit-at y)))))
    }
    where
    module K = ExpressionCalculus (expression-calculus Γ) using (action-comparison)
    module A = Adjunction adj using (counit-at; transpose; untranspose)
    module V = Inverses.InverseLaws 𝒯 M ℱ P I E S Q adj
      using (untranspose-transpose; transpose-untranspose)
    module N = Comparisons.Comparisons 𝒯 M ℱ P I E S adj using (transpose-cong)
```
