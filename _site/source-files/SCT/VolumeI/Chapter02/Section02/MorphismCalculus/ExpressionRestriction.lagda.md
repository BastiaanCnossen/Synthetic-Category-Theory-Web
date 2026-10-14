# Restricting endpoint-preserving identifications

A change of parameters restricts the arrow comparison and both of its
endpoint equations. The associators in `restrict-expression` are retained.
This operation is one ingredient in specializing the universal unit laws;
compatibility of restriction with composition and identity expressions is
still needed for that specialization.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
open PN vocabulary terminal products productLaws composition vertical whiskering
  using (pre-square-projection; substitution-square-projection)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as RestrictionUnits
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as RestrictionAssociativity
open RestrictionUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (unit-square-projection)
open RestrictionAssociativity vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (transport-pre; transport-pre-assoc)

restrict-expressionIso : {Γ Δ C : CAT} {x y : MAP Γ C}
  {f g : MorphismExpression x y} → ExpressionIso f g → (r : MAP Δ Γ) →
  ExpressionIso (restrict-expression f r) (restrict-expression g r)
restrict-expressionIso {f = f} {g} α r = record
  { comparison = A.comparison ▷ r
  ; source-compatible = endpoint ev₀ F.source-frame G.source-frame A.source-compatible
  ; target-compatible = endpoint ev₁ F.target-frame G.target-frame A.target-compatible }
  where
  module F = MorphismExpression f
  module G = MorphismExpression g
  module A = ExpressionIso α

  endpoint : (v : MAP (Ar _) _) {z : MAP _ _}
    (p : (v ∘ F.arrow) =₁ z) (q : (v ∘ G.arrow) =₁ z) →
    (q ∙ (v ◁ A.comparison)) =₂ p →
    (((q ▷ r) ∙ (comp-assoc r G.arrow v) ⁻¹) ∙ (v ◁ (A.comparison ▷ r))) =₂
      ((p ▷ r) ∙ (comp-assoc r F.arrow v) ⁻¹)
  endpoint v {z} p q same =
    isoComp-unitˡ-at _ ∙
      (isoComp-cong (preWhisker-idIso z r) (idIso _) ∙
        pre-square-projection v A.comparison (idIso z) p q r
          ((isoComp-unitˡ-at p) ⁻¹ ∙ same))
```

The identity and successive restrictions compare full expressions. Their
endpoint retargetings are the external unitors and associators, so the
comparison statements display the change of endpoint explicitly.

```agda
restrict-expression-id : {Γ C : CAT} {x y : MAP Γ C}
  (f : MorphismExpression x y) →
  ExpressionIso
    (retarget-expression (restrict-expression f (id Γ)) (comp-unitʳ x) (comp-unitʳ y)) f
restrict-expression-id {x = x} {y} f = record
  { comparison = comp-unitʳ F.arrow
  ; source-compatible = (unit-square-projection ev₀ F.arrow x F.source-frame) ⁻¹
  ; target-compatible = (unit-square-projection ev₁ F.arrow y F.target-frame) ⁻¹ }
  where module F = MorphismExpression f

restrict-expression-compose : {Γ Δ Θ C : CAT} {x y : MAP Γ C}
  (f : MorphismExpression x y) (r : MAP Δ Γ) (s : MAP Θ Δ) →
  ExpressionIso
    (retarget-expression (restrict-expression (restrict-expression f r) s)
      (comp-assoc s r x) (comp-assoc s r y))
    (restrict-expression f (r ∘ s))
restrict-expression-compose {x = x} {y} f r s = record
  { comparison = comp-assoc s r F.arrow
  ; source-compatible = endpoint ev₀ x F.source-frame
  ; target-compatible = endpoint ev₁ y F.target-frame }
  where
  module F = MorphismExpression f
  endpoint : (v : MAP (Ar _) _) (z : MAP _ _)
    (p : (v ∘ F.arrow) =₁ z) →
    (transport-pre v F.arrow p (r ∘ s) ∙ (v ◁ comp-assoc s r F.arrow)) =₂
      (comp-assoc s r z ∙
        ((transport-pre v F.arrow p r ▷ s) ∙ (comp-assoc s (F.arrow ∘ r) v) ⁻¹))
  endpoint v z p =
    isoComp-assoc-at (comp-assoc s r z) (transport-pre v F.arrow p r ▷ s)
      ((comp-assoc s (F.arrow ∘ r) v) ⁻¹) ∙
    (transport-pre-assoc v F.arrow z p r s) ⁻¹
```

An identification of parameter maps also acts on a restricted expression.
Its endpoint changes are the images of that same identification.

```agda
restrict-expression-parameter : {Γ Δ C : CAT} {x y : MAP Γ C}
  (f : MorphismExpression x y) {r s : MAP Δ Γ} (α : r =₁ s) →
  ExpressionIso (retarget-expression (restrict-expression f r) (x ◁ α) (y ◁ α))
    (restrict-expression f s)
restrict-expression-parameter {x = x} {y} f α = record
  { comparison = F.arrow ◁ α
  ; source-compatible = substitution-square-projection ev₀ F.arrow x F.source-frame α
  ; target-compatible = substitution-square-projection ev₁ F.arrow y F.target-frame α }
  where module F = MorphismExpression f
```
