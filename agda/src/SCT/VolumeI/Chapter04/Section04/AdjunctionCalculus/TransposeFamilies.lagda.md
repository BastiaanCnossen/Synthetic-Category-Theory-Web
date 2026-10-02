# Transposition over a fixed base

For functors from a base category into the two sides of an adjunction,
these formulas transpose arrows in the corresponding endpoint pullbacks.
The associators convert between composite endpoint functors and component
expressions. Normalize the input endpoints, apply raw transposition, then
restore the output endpoints. The endpoint-family constructors carry the
restriction and parameter-change comparisons through this composition.
The explicit formulas below keep the mathematical action visible.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFamilies 𝒯 M ℱ I
  using (FamilyOperation; represented; post; associator-frame; identity-comparison;
    inverse-comparison; transport; compose-operations)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeComparisons as Comparisons
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeRestriction as Restriction

module Families {B C D : CAT} {l : MAP C D} {r : MAP D C}
  (adj : Adjunction l r) (x : MAP B C) (y : MAP B D) where
  private
    module A = Adjunction adj
    module N = Comparisons.Comparisons 𝒯 M ℱ P I E S adj
      using (transpose-cong; untranspose-cong; transpose-retarget; untranspose-retarget)
    module R = Restriction.RestrictionLaws 𝒯 M ℱ P I E S adj
      using (transpose-restrict-change; untranspose-restrict-change)

  left-normal : {Γ : CAT} (b : MAP Γ B) →
    MorphismExpression ((l ∘ x) ∘ b) (y ∘ b) → MorphismExpression (l ∘ (x ∘ b)) (y ∘ b)
  left-normal b f = retarget-expression f (comp-assoc b x l) (idIso (y ∘ b))

  right-normal : {Γ : CAT} (b : MAP Γ B) →
    MorphismExpression (x ∘ b) ((r ∘ y) ∘ b) → MorphismExpression (x ∘ b) (r ∘ (y ∘ b))
  right-normal b f = retarget-expression f (idIso (x ∘ b)) (comp-assoc b y r)

  forward : {Γ : CAT} (b : MAP Γ B) →
    MorphismExpression ((l ∘ x) ∘ b) (y ∘ b) → MorphismExpression (x ∘ b) ((r ∘ y) ∘ b)
  forward b f = retarget-expression (A.transpose (x ∘ b) (y ∘ b) (left-normal b f))
    (idIso (x ∘ b)) ((comp-assoc b y r) ⁻¹)

  backward : {Γ : CAT} (b : MAP Γ B) →
    MorphismExpression (x ∘ b) ((r ∘ y) ∘ b) → MorphismExpression ((l ∘ x) ∘ b) (y ∘ b)
  backward b f = retarget-expression (A.untranspose (x ∘ b) (y ∘ b) (right-normal b f))
    ((comp-assoc b x l) ⁻¹) (idIso (y ∘ b))

  raw-forward : FamilyOperation (post l (represented x)) (represented y)
    (represented x) (post r (represented y))
  raw-forward = record
    { apply = λ b f → A.transpose (x ∘ b) (y ∘ b) f
    ; on-comparison = λ b Φ → N.transpose-cong (x ∘ b) (y ∘ b) Φ
    ; on-restriction = λ b f h → R.transpose-restrict-change (x ∘ b) (y ∘ b) f h
        {x′ = x ∘ (b ∘ h)} {y′ = y ∘ (b ∘ h)} (comp-assoc h b x) (comp-assoc h b y)
    ; on-change = λ { {b = b} {d} f σ → N.transpose-retarget
        {x = x ∘ b} {x′ = x ∘ d} {y = y ∘ b} {y′ = y ∘ d} f (x ◁ σ) (y ◁ σ) } }

  raw-backward : FamilyOperation (represented x) (post r (represented y))
    (post l (represented x)) (represented y)
  raw-backward = record
    { apply = λ b f → A.untranspose (x ∘ b) (y ∘ b) f
    ; on-comparison = λ b Φ → N.untranspose-cong (x ∘ b) (y ∘ b) Φ
    ; on-restriction = λ b f h → R.untranspose-restrict-change (x ∘ b) (y ∘ b) f h
        {x′ = x ∘ (b ∘ h)} {y′ = y ∘ (b ∘ h)} (comp-assoc h b x) (comp-assoc h b y)
    ; on-change = λ { {b = b} {d} f σ → N.untranspose-retarget
        {x = x ∘ b} {x′ = x ∘ d} {y = y ∘ b} {y′ = y ∘ d} f (x ◁ σ) (y ◁ σ) } }

  normalize-left : FamilyOperation (represented (l ∘ x)) (represented y)
    (post l (represented x)) (represented y)
  normalize-left = transport
    {u = represented (l ∘ x)} {v = represented y}
    {s = post l (represented x)} {t = represented y}
    (associator-frame x l) (identity-comparison (represented y))

  normalize-right : FamilyOperation (represented x) (represented (r ∘ y))
    (represented x) (post r (represented y))
  normalize-right = transport
    {u = represented x} {v = represented (r ∘ y)}
    {s = represented x} {t = post r (represented y)}
    (identity-comparison (represented x)) (associator-frame y r)

  private
    restore-left : FamilyOperation (post l (represented x)) (represented y)
      (represented (l ∘ x)) (represented y)
    restore-left = transport
      {u = post l (represented x)} {v = represented y}
      {s = represented (l ∘ x)} {t = represented y}
      (inverse-comparison {u = represented (l ∘ x)} {v = post l (represented x)} (associator-frame x l))
      (identity-comparison (represented y))

    restore-right : FamilyOperation (represented x) (post r (represented y))
      (represented x) (represented (r ∘ y))
    restore-right = transport
      {u = represented x} {v = post r (represented y)}
      {s = represented x} {t = represented (r ∘ y)}
      (identity-comparison (represented x))
      (inverse-comparison {u = represented (r ∘ y)} {v = post r (represented y)} (associator-frame y r))

    normalized-forward : FamilyOperation (represented (l ∘ x)) (represented y)
      (represented x) (post r (represented y))
    normalized-forward = compose-operations
      {u = represented (l ∘ x)} {v = represented y}
      {s = post l (represented x)} {t = represented y}
      {x = represented x} {y = post r (represented y)} raw-forward normalize-left

    normalized-backward : FamilyOperation (represented x) (represented (r ∘ y))
      (post l (represented x)) (represented y)
    normalized-backward = compose-operations
      {u = represented x} {v = represented (r ∘ y)}
      {s = represented x} {t = post r (represented y)}
      {x = post l (represented x)} {y = represented y} raw-backward normalize-right

  forward-family : FamilyOperation (represented (l ∘ x)) (represented y)
    (represented x) (represented (r ∘ y))
  forward-family = compose-operations
    {u = represented (l ∘ x)} {v = represented y}
    {s = represented x} {t = post r (represented y)}
    {x = represented x} {y = represented (r ∘ y)} restore-right normalized-forward

  backward-family : FamilyOperation (represented x) (represented (r ∘ y))
    (represented (l ∘ x)) (represented y)
  backward-family = compose-operations
    {u = represented x} {v = represented (r ∘ y)}
    {s = post l (represented x)} {t = represented y}
    {x = represented (l ∘ x)} {y = represented y} restore-left normalized-backward

  abstract
    forward-cong : {Γ : CAT} (b : MAP Γ B)
      {f g : MorphismExpression ((l ∘ x) ∘ b) (y ∘ b)} → ExpressionIso f g →
      ExpressionIso (forward b f) (forward b g)
    forward-cong b Φ = FamilyOperation.on-comparison forward-family b Φ

    backward-cong : {Γ : CAT} (b : MAP Γ B)
      {f g : MorphismExpression (x ∘ b) ((r ∘ y) ∘ b)} → ExpressionIso f g →
      ExpressionIso (backward b f) (backward b g)
    backward-cong b Φ = FamilyOperation.on-comparison backward-family b Φ

    left-normal-change : {Γ : CAT} {b d : MAP Γ B}
      (f : MorphismExpression ((l ∘ x) ∘ b) (y ∘ b)) (σ : b =₁ d) →
      ExpressionIso (retarget-expression (left-normal b f) (l ◁ (x ◁ σ)) (y ◁ σ))
        (left-normal d (retarget-expression f ((l ∘ x) ◁ σ) (y ◁ σ)))
    left-normal-change f σ = FamilyOperation.on-change normalize-left f σ

    right-normal-change : {Γ : CAT} {b d : MAP Γ B}
      (f : MorphismExpression (x ∘ b) ((r ∘ y) ∘ b)) (σ : b =₁ d) →
      ExpressionIso (retarget-expression (right-normal b f) (x ◁ σ) (r ◁ (y ◁ σ)))
        (right-normal d (retarget-expression f (x ◁ σ) ((r ∘ y) ◁ σ)))
    right-normal-change f σ = FamilyOperation.on-change normalize-right f σ

    forward-change : {Γ : CAT} {b d : MAP Γ B}
      (f : MorphismExpression ((l ∘ x) ∘ b) (y ∘ b)) (σ : b =₁ d) →
      ExpressionIso (retarget-expression (forward b f) (x ◁ σ) ((r ∘ y) ◁ σ))
        (forward d (retarget-expression f ((l ∘ x) ◁ σ) (y ◁ σ)))
    forward-change f σ = FamilyOperation.on-change forward-family f σ

    backward-change : {Γ : CAT} {b d : MAP Γ B}
      (f : MorphismExpression (x ∘ b) ((r ∘ y) ∘ b)) (σ : b =₁ d) →
      ExpressionIso (retarget-expression (backward b f) ((l ∘ x) ◁ σ) (y ◁ σ))
        (backward d (retarget-expression f (x ◁ σ) ((r ∘ y) ◁ σ)))
    backward-change f σ = FamilyOperation.on-change backward-family f σ

```
