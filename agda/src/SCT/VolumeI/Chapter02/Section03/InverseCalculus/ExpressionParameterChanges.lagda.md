# Composition with changing parameters

Changing the parameter functor transports both endpoints. The comparison
for composition keeps the three endpoint identifications explicit, so it
can be applied to maps between pullback cones.

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

module SCT.VolumeI.Chapter02.Section03.InverseCalculus.ExpressionParameterChanges
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositePresentations 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S using (retarget-composition)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (substitution-square-projection)

restrict-parameter : {Γ Δ C : CAT} {x y : MAP Γ C}
  (f : MorphismExpression x y) {r s : MAP Δ Γ} (α : r =₁ s) →
  ExpressionIso (retarget-expression (restrict-expression f r) (x ◁ α) (y ◁ α))
    (restrict-expression f s)
restrict-parameter f α = record
  { comparison = F.arrow ◁ α
  ; source-compatible = substitution-square-projection ev₀ F.arrow _ F.source-frame α
  ; target-compatible = substitution-square-projection ev₁ F.arrow _ F.target-frame α }
  where module F = MorphismExpression f

composition-square : {Γ C : CAT} {x y z x′ y′ z′ : MAP Γ C}
  (f : MorphismExpression x y) (g : MorphismExpression y z)
  (f′ : MorphismExpression x′ y′) (g′ : MorphismExpression y′ z′)
  (α : x =₁ x′) (β : y =₁ y′) (γ : z =₁ z′) →
  ExpressionIso (retarget-expression f α β) f′ →
  ExpressionIso (retarget-expression g β γ) g′ →
  ExpressionIso (retarget-expression (compose-expression f g) α γ) (compose-expression f′ g′)
composition-square f g f′ g′ α β γ first second =
  expressionIso-compose (compose-expression-cong first second)
    (expressionIso-inverse (retarget-composition f g α β γ))
```
