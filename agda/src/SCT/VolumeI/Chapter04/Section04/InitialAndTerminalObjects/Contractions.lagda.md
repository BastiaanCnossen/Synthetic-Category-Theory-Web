# Recognizing universal objects from a contraction

A transformation from the constant functor at an object to the identity
exhibits that object as initial if its component there is invertible.
Naturality compares any two arrows out of the object after composition
with that component; cancellation then proves they agree. This works on
the whole endpoint pullback, rather than only on absolute objects.
The dual argument proves the terminal-object statement.

These constructions prove conditions (3) and (4) of
`lem:Characterization_Initial_Objects` equivalent to initiality, and likewise
for terminality. Combined with `AdjunctionCharacterization` and
`AdjointSections`, they complete the four-condition characterization.
The general relaxation theorem for adjoint sections is not used here.

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

module SCT.VolumeI.Chapter04.Section04.InitialAndTerminalObjects.Contractions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section03.InverseCalculus.NaturalTransformationCancellation 𝒯 M ℱ P I E S Q public
open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.UniversalComparisons 𝒯 M ℱ P I
  using (initial-comparison; terminal-comparison)
open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.ExpressionComparisons 𝒯 M ℱ P I
  using (reflect-retarget-comparison)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityFunctorExpressions 𝒯 M ℱ P I E
  using (post-id)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ConstantFunctorExpressions 𝒯 M ℱ P I E
  using (constant-post-unique; constant-point-frame)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberContractibility as Contractibility

abstract
  post-identity-reflect : {Γ C : CAT} {x y : MAP Γ C} (f g : MorphismExpression x y) →
    ExpressionIso (post-expression (id C) f) (post-expression (id C) g) → ExpressionIso f g
  post-identity-reflect {x = x} {y} f g same = expressionIso-compose (post-id g)
    (expressionIso-compose (retarget-expressionIso same (comp-unitˡ x) (comp-unitˡ y))
      (expressionIso-inverse (post-id f)))

  component-at-constant : {Γ C D : CAT} {F G : MAP C D} (α : MorphismExpression F G)
    (x : Obj-abs C) (b : MAP Γ C) → IsInvertibleExpression (restrict-expression α x) →
    IsInvertibleExpression (restrict-expression α (const x ∘ b))
  component-at-constant {C = C} α x b w =
    restrict-parameter-invertible α ((comp-assoc b (terminate C) x) ⁻¹)
      (restrict-composite-invertible α x (terminate C ∘ b) w)

module InitialContraction {C : CAT} (x : Obj-abs C)
  (ε : MorphismExpression (const x) (id C)) where
  component : MorphismExpression x x
  component = retarget-expression (restrict-expression ε x) (constant-point-frame x x) (comp-unitˡ x)

  module Invertible (w : IsInvertibleExpression component) where
    private
      raw-invertible : IsInvertibleExpression (restrict-expression ε x)
      raw-invertible = retarget-reflects-invertible (restrict-expression ε x)
        (constant-point-frame x x) (comp-unitˡ x) w

    abstract
      unique : {Γ : CAT} (b : MAP Γ C)
        (f g : MorphismExpression ((const x) ∘ b) (id C ∘ b)) → ExpressionIso f g
      unique b f g = post-identity-reflect f g
        (cancel-source-component ε f g (component-at-constant ε x b raw-invertible)
          (constant-post-unique x f g))

    isInitial : IsInitial x
    isInitial = Contractibility.Recognition.projection-isEquiv 𝒯 M ℱ P I (const x) (id C) ε unique

  normalized-is-initial : ExpressionIso component (identity-expression x) → IsInitial x
  normalized-is-initial same = Invertible.isInitial
    (identified-invertible (expressionIso-inverse same) (identity-invertible x))

module TerminalContraction {C : CAT} (x : Obj-abs C)
  (η : MorphismExpression (id C) (const x)) where
  component : MorphismExpression x x
  component = retarget-expression (restrict-expression η x) (comp-unitˡ x) (constant-point-frame x x)

  module Invertible (w : IsInvertibleExpression component) where
    private
      raw-invertible : IsInvertibleExpression (restrict-expression η x)
      raw-invertible = retarget-reflects-invertible (restrict-expression η x)
        (comp-unitˡ x) (constant-point-frame x x) w

    abstract
      unique : {Γ : CAT} (b : MAP Γ C)
        (f g : MorphismExpression (id C ∘ b) ((const x) ∘ b)) → ExpressionIso f g
      unique b f g = post-identity-reflect f g
        (cancel-target-component η f g (component-at-constant η x b raw-invertible)
          (constant-post-unique x f g))

    isTerminal : IsTerminal x
    isTerminal = Contractibility.Recognition.projection-isEquiv 𝒯 M ℱ P I (id C) (const x) η unique

  normalized-is-terminal : ExpressionIso component (identity-expression x) → IsTerminal x
  normalized-is-terminal same = Invertible.isTerminal
    (identified-invertible (expressionIso-inverse same) (identity-invertible x))

module FromInitial {C : CAT} (x : Obj-abs C) (e : IsInitial x) where
  contraction : MorphismExpression (const x) (id C)
  contraction = initial-expression x e (id C)
  open InitialContraction x contraction using (component)

  abstract
    normalized : ExpressionIso component (identity-expression x)
    normalized = reflect-retarget-comparison component (identity-expression x) ((const-One x) ⁻¹) (idIso x)
      (initial-comparison x e x
        (retarget-expression component ((const-One x) ⁻¹) (idIso x))
        (retarget-expression (identity-expression x) ((const-One x) ⁻¹) (idIso x)))

  invertible : IsInvertibleExpression component
  invertible = identified-invertible (expressionIso-inverse normalized) (identity-invertible x)

module FromTerminal {C : CAT} (x : Obj-abs C) (e : IsTerminal x) where
  contraction : MorphismExpression (id C) (const x)
  contraction = terminal-expression x e (id C)
  open TerminalContraction x contraction using (component)

  abstract
    normalized : ExpressionIso component (identity-expression x)
    normalized = reflect-retarget-comparison component (identity-expression x) (idIso x) ((const-One x) ⁻¹)
      (terminal-comparison x e x
        (retarget-expression component (idIso x) ((const-One x) ⁻¹))
        (retarget-expression (identity-expression x) (idIso x) ((const-One x) ⁻¹)))

  invertible : IsInvertibleExpression component
  invertible = identified-invertible (expressionIso-inverse normalized) (identity-invertible x)
```
