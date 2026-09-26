# Calculus of endpoint-preserving identifications

Identity, inversion, composition, and a change of endpoint frames retain
the two equations in `ExpressionIso`. These operations let the proofs
below compare full morphism expressions, including their endpoints.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right)

expressionIso-id : {Γ C : CAT} {x y : MAP Γ C} (f : MorphismExpression x y) → ExpressionIso f f
expressionIso-id f = record
  { comparison = idIso F.arrow
  ; source-compatible = isoComp-unitʳ-at F.source-frame ∙
      isoComp-cong (idIso F.source-frame) (postWhisker-idIso ev₀ F.arrow)
  ; target-compatible = isoComp-unitʳ-at F.target-frame ∙
      isoComp-cong (idIso F.target-frame) (postWhisker-idIso ev₁ F.arrow) }
  where module F = MorphismExpression f

expressionIso-compose : {Γ C : CAT} {x y : MAP Γ C} {f g h : MorphismExpression x y} →
  ExpressionIso g h → ExpressionIso f g → ExpressionIso f h
expressionIso-compose {f = f} {g} {h} β α = record
  { comparison = B.comparison ∙ A.comparison
  ; source-compatible = endpoint ev₀ F.source-frame G.source-frame H.source-frame A.source-compatible B.source-compatible
  ; target-compatible = endpoint ev₁ F.target-frame G.target-frame H.target-frame A.target-compatible B.target-compatible }
  where
  module F = MorphismExpression f
  module G = MorphismExpression g
  module H = MorphismExpression h
  module A = ExpressionIso α
  module B = ExpressionIso β
  endpoint : (v : MAP (Ar _) _) {z : MAP _ _}
    (p : (v ∘ F.arrow) =₁ z) (q : (v ∘ G.arrow) =₁ z) (r : (v ∘ H.arrow) =₁ z) →
    (q ∙ (v ◁ A.comparison)) =₂ p → (r ∙ (v ◁ B.comparison)) =₂ q →
    (r ∙ (v ◁ (B.comparison ∙ A.comparison))) =₂ p
  endpoint v p q r first second = first ∙
    (isoComp-cong second (idIso (v ◁ A.comparison)) ∙
      ((isoComp-assoc-at r (v ◁ B.comparison) (v ◁ A.comparison)) ⁻¹ ∙
        isoComp-cong (idIso r) (postWhisker-isoComp-at v B.comparison A.comparison)))

expressionIso-inverse : {Γ C : CAT} {x y : MAP Γ C} {f g : MorphismExpression x y} →
  ExpressionIso f g → ExpressionIso g f
expressionIso-inverse {f = f} {g} α = record
  { comparison = A.comparison ⁻¹
  ; source-compatible = endpoint ev₀ F.source-frame G.source-frame A.source-compatible
  ; target-compatible = endpoint ev₁ F.target-frame G.target-frame A.target-compatible }
  where
  module F = MorphismExpression f
  module G = MorphismExpression g
  module A = ExpressionIso α
  endpoint : (v : MAP (Ar _) _) {z : MAP _ _}
    (p : (v ∘ F.arrow) =₁ z) (q : (v ∘ G.arrow) =₁ z) →
    (q ∙ (v ◁ A.comparison)) =₂ p → (p ∙ (v ◁ A.comparison ⁻¹)) =₂ q
  endpoint v p q same = cancel-right (v ◁ A.comparison) q ∙
    (isoComp-cong (same ⁻¹) (idIso ((v ◁ A.comparison) ⁻¹)) ∙
      isoComp-cong (idIso p) (post-inverse v A.comparison))

retarget-expressionIso : {Γ C : CAT} {x y x′ y′ : MAP Γ C}
  {f g : MorphismExpression x y} → ExpressionIso f g →
  (p : x =₁ x′) (q : y =₁ y′) →
  ExpressionIso (retarget-expression f p q) (retarget-expression g p q)
retarget-expressionIso {g = g} α p q = record
  { comparison = A.comparison
  ; source-compatible = isoComp-cong (idIso p) A.source-compatible ∙
      isoComp-assoc-at p (MorphismExpression.source-frame g) (ev₀ ◁ A.comparison)
  ; target-compatible = isoComp-cong (idIso q) A.target-compatible ∙
      isoComp-assoc-at q (MorphismExpression.target-frame g) (ev₁ ◁ A.comparison) }
  where module A = ExpressionIso α
```
