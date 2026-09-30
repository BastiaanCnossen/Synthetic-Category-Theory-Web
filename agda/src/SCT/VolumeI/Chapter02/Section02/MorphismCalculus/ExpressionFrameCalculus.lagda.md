# Changes of endpoint frames

Successive endpoint changes associate, identified changes agree, and
postcomposition carries an endpoint change to its image. These small
comparisons keep the same arrow diagram throughout.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I using (post-boundary-normal)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
  using (expressionIso-compose; expressionIso-inverse; retarget-expressionIso)

same-arrow : {Γ C : CAT} {x y : MAP Γ C} (h : MAP Γ (Ar C))
  (p p′ : (ev₀ ∘ h) =₁ x) (q q′ : (ev₁ ∘ h) =₁ y) → p′ =₂ p → q′ =₂ q →
  ExpressionIso (record { arrow = h ; source-frame = p ; target-frame = q })
    (record { arrow = h ; source-frame = p′ ; target-frame = q′ })
same-arrow h p p′ q q′ source target = record { comparison = idIso h
  ; source-compatible = source ∙ isoComp-unitʳ-at p′ ∙ isoComp-cong (idIso p′) (postWhisker-idIso ev₀ h)
  ; target-compatible = target ∙ isoComp-unitʳ-at q′ ∙ isoComp-cong (idIso q′) (postWhisker-idIso ev₁ h) }

retarget-assoc : {Γ C : CAT} {x y x′ y′ x″ y″ : MAP Γ C}
  (f : MorphismExpression x y) (α : x =₁ x′) (β : y =₁ y′) (p : x′ =₁ x″) (q : y′ =₁ y″) →
  ExpressionIso (retarget-expression (retarget-expression f α β) p q)
    (retarget-expression f (p ∙ α) (q ∙ β))
retarget-assoc f α β p q = same-arrow F.arrow _ _ _ _
  (isoComp-assoc-at p α F.source-frame) (isoComp-assoc-at q β F.target-frame)
  where module F = MorphismExpression f

retarget-cong : {Γ C : CAT} {x y x′ y′ : MAP Γ C} (f : MorphismExpression x y)
  {α α′ : x =₁ x′} {β β′ : y =₁ y′} → α =₂ α′ → β =₂ β′ →
  ExpressionIso (retarget-expression f α β) (retarget-expression f α′ β′)
retarget-cong f p q = same-arrow F.arrow _ _ _ _
  (isoComp-cong (p ⁻¹) (idIso F.source-frame)) (isoComp-cong (q ⁻¹) (idIso F.target-frame))
  where module F = MorphismExpression f

retarget-id : {Γ C : CAT} {x y : MAP Γ C} (f : MorphismExpression x y) →
  ExpressionIso (retarget-expression f (idIso x) (idIso y)) f
retarget-id f = same-arrow F.arrow _ _ _ _
  ((isoComp-unitˡ-at F.source-frame) ⁻¹) ((isoComp-unitˡ-at F.target-frame) ⁻¹)
  where module F = MorphismExpression f

post-retarget : {Γ C D : CAT} (F : MAP C D) {x y x′ y′ : MAP Γ C}
  (f : MorphismExpression x y) (α : x =₁ x′) (β : y =₁ y′) →
  ExpressionIso (post-expression F (retarget-expression f α β))
    (retarget-expression (post-expression F f) (F ◁ α) (F ◁ β))
post-retarget F f α β = same-arrow (funPost F ∘ A.arrow) _ _ _ _
  (endpoint zero A.source-frame α) (endpoint one A.target-frame β)
  where
  module A = MorphismExpression f
  endpoint : (v : Obj-abs [1]) {x x′ : MAP _ _}
    (p : (evaluate v ∘ A.arrow) =₁ x) (q : x =₁ x′) →
    ((F ◁ q) ∙ post-boundary v F A.arrow p) =₂ post-boundary v F A.arrow (q ∙ p)
  endpoint v p q = (post-boundary-normal v F A.arrow (q ∙ p)) ⁻¹ ∙
    isoComp-cong ((postWhisker-isoComp-at F q p) ⁻¹) (idIso (evaluate-post-at v F A.arrow)) ∙
    (isoComp-assoc-at (F ◁ q) (F ◁ p) (evaluate-post-at v F A.arrow)) ⁻¹ ∙
    isoComp-cong (idIso (F ◁ q)) (post-boundary-normal v F A.arrow p)
```

Retargeting is reversible as an operation on framed expressions. In
particular, a comparison whose source was retargeted backwards can be
moved across the endpoint changes without forgetting either frame.

```agda
restrict-retarget : {Γ Δ C : CAT} {x y x′ y′ : MAP Γ C}
  (f : MorphismExpression x y) (p : x =₁ x′) (q : y =₁ y′) (r : MAP Δ Γ) →
  ExpressionIso (restrict-expression (retarget-expression f p q) r)
    (retarget-expression (restrict-expression f r) (p ▷ r) (q ▷ r))
restrict-retarget f p q r = same-arrow (F.arrow ∘ r) _ _ _ _
  (endpoint ev₀ F.source-frame p) (endpoint ev₁ F.target-frame q)
  where
  module F = MorphismExpression f
  endpoint : (v : MAP (Ar _) _) {z z′ : MAP _ _}
    (b : (v ∘ F.arrow) =₁ z) (a : z =₁ z′) →
    ((a ▷ r) ∙ ((b ▷ r) ∙ (comp-assoc r F.arrow v) ⁻¹)) =₂
    (((a ∙ b) ▷ r) ∙ (comp-assoc r F.arrow v) ⁻¹)
  endpoint v b a =
    isoComp-cong ((preWhisker-isoComp-at a b r) ⁻¹)
      (idIso ((comp-assoc r F.arrow v) ⁻¹)) ∙
    (isoComp-assoc-at (a ▷ r) (b ▷ r) ((comp-assoc r F.arrow v) ⁻¹)) ⁻¹

restrict-retarget-outer : {Γ Δ C : CAT} {x y x′ y′ : MAP Γ C}
  {u v : MAP Δ C} (f : MorphismExpression x y)
  (p : x =₁ x′) (q : y =₁ y′) (r : MAP Δ Γ)
  (a : (x′ ∘ r) =₁ u) (b : (y′ ∘ r) =₁ v) →
  ExpressionIso (retarget-expression (restrict-expression (retarget-expression f p q) r) a b)
    (retarget-expression (restrict-expression f r) (a ∙ (p ▷ r)) (b ∙ (q ▷ r)))
restrict-retarget-outer f p q r a b = expressionIso-compose
  (retarget-assoc (restrict-expression f r) (p ▷ r) (q ▷ r) a b)
  (retarget-expressionIso (restrict-retarget f p q r) a b)

retarget-cancel : {Γ C : CAT} {x y x′ y′ : MAP Γ C}
  (f : MorphismExpression x y) (p : x =₁ x′) (q : y =₁ y′) →
  ExpressionIso
    (retarget-expression (retarget-expression f p q) (p ⁻¹) (q ⁻¹)) f
retarget-cancel f p q = expressionIso-compose (retarget-id f)
  (expressionIso-compose
    (retarget-cong f (isoComp-inverseˡ-at p) (isoComp-inverseˡ-at q))
    (retarget-assoc f p q (p ⁻¹) (q ⁻¹)))

retarget-cancel-inverse : {Γ C : CAT} {x y x′ y′ : MAP Γ C}
  (f : MorphismExpression x′ y′) (p : x =₁ x′) (q : y =₁ y′) →
  ExpressionIso
    (retarget-expression (retarget-expression f (p ⁻¹) (q ⁻¹)) p q) f
retarget-cancel-inverse f p q = expressionIso-compose (retarget-id f)
  (expressionIso-compose
    (retarget-cong f (isoComp-inverseʳ-at p) (isoComp-inverseʳ-at q))
    (retarget-assoc f (p ⁻¹) (q ⁻¹) p q))

retarget-move : {Γ C : CAT} {x y x′ y′ : MAP Γ C}
  {f : MorphismExpression x′ y′} {g : MorphismExpression x y}
  (p : x =₁ x′) (q : y =₁ y′) →
  ExpressionIso (retarget-expression f (p ⁻¹) (q ⁻¹)) g →
  ExpressionIso (retarget-expression g p q) f
retarget-move {f = f} p q α = expressionIso-compose
  (retarget-cancel-inverse f p q)
  (retarget-expressionIso (expressionIso-inverse α) p q)
```
