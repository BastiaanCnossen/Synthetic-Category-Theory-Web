# The outer vertices with endpoint compatibility

Initiality at `0` and terminality at `1` choose the lower and upper
face identifications together with their images under both degeneracies.
These equations control the endpoints of the long edge of a unit triangle.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section01.OuterVertices
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Lattice 𝒯 M ℱ P I E public
open import SCT.VolumeI.Chapter02.Section01.UniversalComparisons 𝒯 M ℱ P I using (initial-comparison; terminal-comparison)
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left-reflect)

module Bottom where
  source-before = (comp-unitˡ zero ∙ (identity-source ▷ zero)) ∙ (comp-assoc zero identityArrow ev₀) ⁻¹
  source-after = ((constant-boundary zero zero) ∙ (MorphismExpression.source-frame min-expression ▷ zero)) ∙
    (comp-assoc zero min̄ ev₀) ⁻¹
  target-before = (comp-unitˡ zero ∙ (identity-target ▷ zero)) ∙ (comp-assoc zero identityArrow ev₁) ⁻¹
  target-after = (comp-unitˡ zero ∙ (MorphismExpression.target-frame min-expression ▷ zero)) ∙
    (comp-assoc zero min̄ ev₁) ⁻¹

  before after : MorphismExpression (const zero) zero
  before = record { arrow = identityArrow ∘ zero ; source-frame = (const-One zero) ⁻¹ ∙ source-before ; target-frame = target-before }
  after = record { arrow = min̄ ∘ zero ; source-frame = (const-One zero) ⁻¹ ∙ source-after ; target-frame = target-after }

  comparison : ExpressionIso before after
  comparison = initial-comparison zero zero-isInitial zero before after
  value : (identityArrow ∘ zero) =₁ (min̄ ∘ zero)
  value = ExpressionIso.comparison comparison

  source-compatible : (source-after ∙ (ev₀ ◁ value)) =₂ source-before
  source-compatible = cancel-left-reflect ((const-One zero) ⁻¹)
    (ExpressionIso.source-compatible comparison ∙ (isoComp-assoc-at ((const-One zero) ⁻¹) source-after (ev₀ ◁ value)) ⁻¹)
  target-compatible : (target-after ∙ (ev₁ ◁ value)) =₂ target-before
  target-compatible = ExpressionIso.target-compatible comparison

module Top where
  source-before = (comp-unitˡ one ∙ (MorphismExpression.source-frame max-expression ▷ one)) ∙
    (comp-assoc one max̄ ev₀) ⁻¹
  source-after = (comp-unitˡ one ∙ (identity-source ▷ one)) ∙ (comp-assoc one identityArrow ev₀) ⁻¹
  target-before = ((constant-boundary one one) ∙ (MorphismExpression.target-frame max-expression ▷ one)) ∙
    (comp-assoc one max̄ ev₁) ⁻¹
  target-after = (comp-unitˡ one ∙ (identity-target ▷ one)) ∙ (comp-assoc one identityArrow ev₁) ⁻¹

  before after : MorphismExpression one (const one)
  before = record { arrow = max̄ ∘ one ; source-frame = source-before ; target-frame = (const-One one) ⁻¹ ∙ target-before }
  after = record { arrow = identityArrow ∘ one ; source-frame = source-after ; target-frame = (const-One one) ⁻¹ ∙ target-after }

  comparison : ExpressionIso before after
  comparison = terminal-comparison one one-isTerminal one before after
  value : (max̄ ∘ one) =₁ (identityArrow ∘ one)
  value = ExpressionIso.comparison comparison

  source-compatible : (source-after ∙ (ev₀ ◁ value)) =₂ source-before
  source-compatible = ExpressionIso.source-compatible comparison
  target-compatible : (target-after ∙ (ev₁ ◁ value)) =₂ target-before
  target-compatible = cancel-left-reflect ((const-One one) ⁻¹)
    (ExpressionIso.target-compatible comparison ∙ (isoComp-assoc-at ((const-One one) ⁻¹) target-after (ev₁ ◁ value)) ⁻¹)
```

