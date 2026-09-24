# Triangles as squares with a constant side

For `cor:Commutative_Triangles`, cancel the square-axiom pullback and
then the Segal pullback, and paste the resulting two squares. Each outer
rectangle has both horizontal maps equivalences. We retain its pasted
matching throughout; no uniqueness of commutativity identifications is used.

With `j₀ = (s₀,s₁)` and `j₁ = (s₁,s₀)`, `p₀` has constant side
`[1] × {0}`, and `p₂` has constant side `[1] × {1}`. These are the
coordinate restrictions used below. `vertex-square` writes the vertical leg
as evaluation at the corresponding triangle vertex and transports the
specified matching along that vertex comparison.

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

module SCT.VolumeI.Chapter02.Section02.TrianglePullbacks
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.Composition 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section01.SquareRetractions 𝒯 M ℱ P I E Q
  using (p₀; p₂; p₀-j₀; p₀-j₁; p₂-j₀; p₂-j₁; j₀; j₁; gluing-square; bottom-boundary; top-boundary)
open import SCT.VolumeI.Chapter02.Section01.SquareFamilies 𝒯 M ℱ P I E Q using (square-functor-pullback)
open import SCT.VolumeI.Chapter01.Section08.FunctorSquares 𝒯 M ℱ P using (functorOut; preComp; preCong)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; IsPullback; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (degenerate-pullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeSymmetry 𝒯 using (coneSwap; coneSwap-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus 𝒯 using (coneRetarget; coneRetarget-β)
open import SCT.VolumeI.Chapter01.Section06.ConeArrowChange 𝒯 using (changeLeft)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)
import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange as ArrowChange
open import SCT.VolumeI.Chapter01.Section07.IsomorphismLifting 𝒯 M ℱ using (funIsoReflect)
import SCT.VolumeI.Chapter02.Section02.DirectUnitTriangles as UnitTriangles

abstract
  horizontal-equivalences : {A B Z T : CAT} {f : MAP A Z} {g : MAP B Z}
    (s : Cone f g T) → IsEquiv f → IsEquiv (Cone.right s) → IsPullback s
  horizontal-equivalences s ef eq = pullback-cone-invariant (coneSwap-swap s)
    (pullback-swap (coneSwap s) (degenerate-pullback ef (coneSwap s) eq))

module At (C : CAT) where
  module U = UnitTriangles.Universal 𝒯 M ℱ P I E C
  square-cone : Cone (edge₁ {C}) edge₁ (Fun ([1] × [1]) C)
  square-cone = functorOut gluing-square C
  segal-cone : Cone (ev₁ {C}) ev₀ (Triangles C)
  segal-cone = triangle-cone C

  abstract
    constant-comparison : (v : MAP (Ar C) C) →
      (identityArrow ∘ v) =₁ MorphismExpression.arrow (identity-expression v)
    constant-comparison v = funIsoReflect _ _
      ((funCurry-β (v ∘ pr₁)) ⁻¹ ∙
        (pair-β₁ (v ∘ pr₁) (id [1] ∘ pr₂) ∙
          ((funCurry-β pr₁ ▷ productMap v (id [1])) ∙ funUncurry-restrict identityArrow v)))

  module Left where
    right-square : Cone (edge₁ {C}) edge₁ (Fun ([1] × [1]) C)
    right-square = coneSwap square-cone
    right-isPullback : IsPullback right-square
    right-isPullback = pullback-swap square-cone (square-functor-pullback C)
    module Upper = Pasting (funPre s₀) edge₁ edge₁ right-square right-isPullback

    upper-cone : Cone (funPre s₀) (funPre j₁) (Triangles C)
    upper-cone = record { left = edge₁ ; right = funPre p₀
      ; match = (preComp j₁ p₀) ⁻¹ ∙ ((preCong p₀-j₁) ⁻¹ ∙ preComp s₀ d₁) }
    abstract
      upper-isPullback : IsPullback upper-cone
      upper-isPullback = Upper.cancel-isPullback upper-cone
        (horizontal-equivalences (Upper.Paste.flatten upper-cone)
          (equiv-transport ((funPre-id [1] C ∙ (preCong s₀-d₁ ∙ preComp d₁ s₀)) ⁻¹) (id-isEquiv (Ar C)))
          (equiv-transport ((funPre-id [2] C ∙ (preCong p₀-j₀ ∙ preComp j₀ p₀)) ⁻¹) (id-isEquiv (Triangles C))))

    module Lower = Pasting identityArrow ev₁ ev₀ segal-cone (SegalAxiom.segal-isPullback S C)
    lower-cone : Cone (identityArrow {C}) edge₂ (Ar C)
    lower-cone = record { left = ev₀ ; right = funPre s₀
      ; match = (U.Left.First.comparison) ⁻¹ ∙ constant-comparison ev₀ }
    abstract
      lower-isPullback : IsPullback lower-cone
      lower-isPullback = Lower.cancel-isPullback lower-cone
        (horizontal-equivalences (Lower.Paste.flatten lower-cone)
          (equiv-transport (identity-target ⁻¹) (id-isEquiv C))
          (equiv-transport ((funPre-id [1] C ∙ (preCong s₀-d₀ ∙ preComp d₀ s₀)) ⁻¹) (id-isEquiv (Ar C))))

    module Whole = Pasting (funPre j₁) edge₂ identityArrow
      (coneSwap lower-cone) (pullback-swap lower-cone lower-isPullback)
    pasted = Whole.Paste.flatten (coneSwap upper-cone)
    abstract
      pasted-isPullback : IsPullback pasted
      pasted-isPullback = Whole.paste-isPullback (coneSwap upper-cone)
        (pullback-swap upper-cone upper-isPullback)

    side-comparison : (edge₂ ∘ funPre {D = C} j₁) =₁ (funPre (insert zero))
    side-comparison = preCong bottom-boundary ∙ preComp d₂ j₁
    module Side = ArrowChange.ChangeLeft 𝒯 P side-comparison identityArrow
    square : Cone (funPre (insert zero)) (identityArrow {C}) (Triangles C)
    square = changeLeft side-comparison pasted
    abstract
      square-isPullback : IsPullback square
      square-isPullback = Side.preserve pasted pasted-isPullback

    vertex-comparison : (Cone.right square) =₁ evaluate vertex₀
    vertex-comparison = evaluate-cong d₁-zero ∙ evaluate-pre d₁ zero
    vertex-square : Cone (funPre (insert zero)) (identityArrow {C}) (Triangles C)
    vertex-square = coneRetarget square (funPre p₀) (evaluate vertex₀)
      (idIso (funPre p₀)) vertex-comparison
    abstract
      vertex-square-isPullback : IsPullback vertex-square
      vertex-square-isPullback = pullback-cone-invariant
        (coneRetarget-β square (funPre p₀) (evaluate vertex₀)
          (idIso (funPre p₀)) vertex-comparison) square-isPullback

  module Right where
    module Upper = Pasting (funPre s₁) edge₁ edge₁ square-cone (square-functor-pullback C)
    upper-cone : Cone (funPre s₁) (funPre j₀) (Triangles C)
    upper-cone = record { left = edge₁ ; right = funPre p₂
      ; match = (preComp j₀ p₂) ⁻¹ ∙ ((preCong p₂-j₀) ⁻¹ ∙ preComp s₁ d₁) }
    abstract
      upper-isPullback : IsPullback upper-cone
      upper-isPullback = Upper.cancel-isPullback upper-cone
        (horizontal-equivalences (Upper.Paste.flatten upper-cone)
          (equiv-transport ((funPre-id [1] C ∙ (preCong s₁-d₁ ∙ preComp d₁ s₁)) ⁻¹) (id-isEquiv (Ar C)))
          (equiv-transport ((funPre-id [2] C ∙ (preCong p₂-j₁ ∙ preComp j₁ p₂)) ⁻¹) (id-isEquiv (Triangles C))))

    module Lower = Pasting identityArrow ev₀ ev₁ (coneSwap segal-cone)
      (pullback-swap segal-cone (SegalAxiom.segal-isPullback S C))
    lower-cone : Cone (identityArrow {C}) edge₀ (Ar C)
    lower-cone = record { left = ev₁ ; right = funPre s₁
      ; match = (U.Right.Second.comparison) ⁻¹ ∙ constant-comparison ev₁ }
    abstract
      lower-isPullback : IsPullback lower-cone
      lower-isPullback = Lower.cancel-isPullback lower-cone
        (horizontal-equivalences (Lower.Paste.flatten lower-cone)
          (equiv-transport (identity-source ⁻¹) (id-isEquiv C))
          (equiv-transport ((funPre-id [1] C ∙ (preCong s₁-d₂ ∙ preComp d₂ s₁)) ⁻¹) (id-isEquiv (Ar C))))

    module Whole = Pasting (funPre j₀) edge₀ identityArrow
      (coneSwap lower-cone) (pullback-swap lower-cone lower-isPullback)
    pasted = Whole.Paste.flatten (coneSwap upper-cone)
    abstract
      pasted-isPullback : IsPullback pasted
      pasted-isPullback = Whole.paste-isPullback (coneSwap upper-cone)
        (pullback-swap upper-cone upper-isPullback)

    side-comparison : (edge₀ ∘ funPre {D = C} j₀) =₁ (funPre (insert one))
    side-comparison = preCong top-boundary ∙ preComp d₀ j₀
    module Side = ArrowChange.ChangeLeft 𝒯 P side-comparison identityArrow
    square : Cone (funPre (insert one)) (identityArrow {C}) (Triangles C)
    square = changeLeft side-comparison pasted
    abstract
      square-isPullback : IsPullback square
      square-isPullback = Side.preserve pasted pasted-isPullback

    vertex-comparison : (Cone.right square) =₁ evaluate vertex₂
    vertex-comparison = evaluate-cong d₁-one ∙ evaluate-pre d₁ one
    vertex-square : Cone (funPre (insert one)) (identityArrow {C}) (Triangles C)
    vertex-square = coneRetarget square (funPre p₂) (evaluate vertex₂)
      (idIso (funPre p₂)) vertex-comparison
    abstract
      vertex-square-isPullback : IsPullback vertex-square
      vertex-square-isPullback = pullback-cone-invariant
        (coneRetarget-β square (funPre p₂) (evaluate vertex₂)
          (idIso (funPre p₂)) vertex-comparison) square-isPullback
```
