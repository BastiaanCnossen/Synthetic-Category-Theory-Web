# The outer vertices with endpoint compatibility

Initiality at `0` and terminality at `1` choose the lower and upper
face identifications together with their images under both degeneracies.
These equations control the endpoints of the long edge of a unit triangle.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section09.WalkingMorphism as Walking
import SCT.VolumeI.Chapter01.Section09.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter01.Section09.OuterVertices
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter01.Section09.Lattice 𝒯 M ℱ P I E public
open import SCT.VolumeI.Chapter01.Section09.UniversalComparisons 𝒯 M ℱ P I using (initial-comparison; terminal-comparison)
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left-reflect)

module Bottom where
  source-before = (comp-unitˡ zero ∙ (identity-source ▷ zero)) ∙ invIso (comp-assoc zero identityArrow ev₀)
  source-after = ((constant-boundary zero zero) ∙ (MorphismExpression.source-frame min-expression ▷ zero)) ∙
    invIso (comp-assoc zero min̄ ev₀)
  target-before = (comp-unitˡ zero ∙ (identity-target ▷ zero)) ∙ invIso (comp-assoc zero identityArrow ev₁)
  target-after = (comp-unitˡ zero ∙ (MorphismExpression.target-frame min-expression ▷ zero)) ∙
    invIso (comp-assoc zero min̄ ev₁)

  before after : MorphismExpression (const zero) zero
  before = record { arrow = identityArrow ∘ zero ; source-frame = invIso (const-One zero) ∙ source-before ; target-frame = target-before }
  after = record { arrow = min̄ ∘ zero ; source-frame = invIso (const-One zero) ∙ source-after ; target-frame = target-after }

  comparison : ExpressionIso before after
  comparison = initial-comparison zero zero-isInitial zero before after
  value : =₁ (identityArrow ∘ zero) (min̄ ∘ zero)
  value = ExpressionIso.comparison comparison

  source-compatible : =₂ (source-after ∙ (ev₀ ◁ value)) source-before
  source-compatible = cancel-left-reflect (invIso (const-One zero))
    (ExpressionIso.source-compatible comparison ∙ invIso (isoComp-assoc-at (invIso (const-One zero)) source-after (ev₀ ◁ value)))
  target-compatible : =₂ (target-after ∙ (ev₁ ◁ value)) target-before
  target-compatible = ExpressionIso.target-compatible comparison

module Top where
  source-before = (comp-unitˡ one ∙ (MorphismExpression.source-frame max-expression ▷ one)) ∙
    invIso (comp-assoc one max̄ ev₀)
  source-after = (comp-unitˡ one ∙ (identity-source ▷ one)) ∙ invIso (comp-assoc one identityArrow ev₀)
  target-before = ((constant-boundary one one) ∙ (MorphismExpression.target-frame max-expression ▷ one)) ∙
    invIso (comp-assoc one max̄ ev₁)
  target-after = (comp-unitˡ one ∙ (identity-target ▷ one)) ∙ invIso (comp-assoc one identityArrow ev₁)

  before after : MorphismExpression one (const one)
  before = record { arrow = max̄ ∘ one ; source-frame = source-before ; target-frame = invIso (const-One one) ∙ target-before }
  after = record { arrow = identityArrow ∘ one ; source-frame = source-after ; target-frame = invIso (const-One one) ∙ target-after }

  comparison : ExpressionIso before after
  comparison = terminal-comparison one one-isTerminal one before after
  value : =₁ (max̄ ∘ one) (identityArrow ∘ one)
  value = ExpressionIso.comparison comparison

  source-compatible : =₂ (source-after ∙ (ev₀ ◁ value)) source-before
  source-compatible = ExpressionIso.source-compatible comparison
  target-compatible : =₂ (target-after ∙ (ev₁ ◁ value)) target-before
  target-compatible = cancel-left-reflect (invIso (const-One one))
    (ExpressionIso.target-compatible comparison ∙ invIso (isoComp-assoc-at (invIso (const-One one)) target-after (ev₁ ◁ value)))
```

