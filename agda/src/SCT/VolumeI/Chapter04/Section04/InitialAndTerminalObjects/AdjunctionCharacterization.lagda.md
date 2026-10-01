# Adjunctions with the terminal functor detect universal objects

If an object is left adjoint to the terminal functor, its counit is a
universal family of outgoing arrows. Transposition identifies any two
such arrows: their transposes lie in the terminal category. The endpoint
pullback recognition lemma then proves that the coslice projection is
an equivalence. The terminal-object argument is dual.

Together with `AdjointSections`, this proves the equivalence of the
universal-object and adjoint-section conditions in
`lem:Characterization_Initial_Objects` and its dual. This proof uses
parameterized expression comparisons, without a later objectwise
recognition theorem or functoriality of universals.

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

module SCT.VolumeI.Chapter04.Section04.InitialAndTerminalObjects.AdjunctionCharacterization
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.AdjointSections 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.ExpressionComparisons 𝒯 M ℱ P I
  using (reflect-retarget-comparison)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ConstantFunctorExpressions 𝒯 M ℱ P I E
  using (terminal-expression-unique)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberContractibility as Contractibility
open import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.SealedTransposition 𝒯 M ℱ P I E S Q
  using (ExpressionEquivalence; transposition)

module Initial {C : CAT} (x : Obj-abs C) (adj : Adjunction x (terminate C)) where
  private
    module A = Adjunction adj

  abstract
    unique : {Γ : CAT} (b : MAP Γ C)
      (f g : MorphismExpression ((const x) ∘ b) (id C ∘ b)) → ExpressionIso f g
    unique {Γ} b f g = reflect-retarget-comparison f g (comp-assoc b (terminate C) x) (comp-unitˡ b)
      (T.reflect-forward (terminal-expression-unique (T.forward f′) (T.forward g′)))
      where
      module T = ExpressionEquivalence (transposition adj (terminate C ∘ b) b)
      f′ : MorphismExpression (x ∘ (terminate C ∘ b)) b
      f′ = retarget-expression f (comp-assoc b (terminate C) x) (comp-unitˡ b)
      g′ : MorphismExpression (x ∘ (terminate C ∘ b)) b
      g′ = retarget-expression g (comp-assoc b (terminate C) x) (comp-unitˡ b)

  isInitial : IsInitial x
  isInitial = Contractibility.Recognition.projection-isEquiv 𝒯 M ℱ P I (const x) (id C) A.counit unique

module Terminal {C : CAT} (x : Obj-abs C) (adj : Adjunction (terminate C) x) where
  private
    module A = Adjunction adj

  abstract
    unique : {Γ : CAT} (b : MAP Γ C)
      (f g : MorphismExpression (id C ∘ b) ((const x) ∘ b)) → ExpressionIso f g
    unique {Γ} b f g = reflect-retarget-comparison f g (comp-unitˡ b) (comp-assoc b (terminate C) x)
      (T.reflect-backward (terminal-expression-unique (T.backward f′) (T.backward g′)))
      where
      module T = ExpressionEquivalence (transposition adj b (terminate C ∘ b))
      f′ : MorphismExpression b (x ∘ (terminate C ∘ b))
      f′ = retarget-expression f (comp-unitˡ b) (comp-assoc b (terminate C) x)
      g′ : MorphismExpression b (x ∘ (terminate C ∘ b))
      g′ = retarget-expression g (comp-unitˡ b) (comp-assoc b (terminate C) x)

  isTerminal : IsTerminal x
  isTerminal = Contractibility.Recognition.projection-isEquiv 𝒯 M ℱ P I (id C) (const x) A.unit unique

left-adjoint-section-is-initial : {C : CAT} (x : Obj-abs C) →
  LeftAdjointSection (terminate C) x → IsInitial x
left-adjoint-section-is-initial x a = Initial.isInitial x (LeftAdjointSection.adjunction a)

right-adjoint-section-is-terminal : {C : CAT} (x : Obj-abs C) →
  RightAdjointSection (terminate C) x → IsTerminal x
right-adjoint-section-is-terminal x a = Terminal.isTerminal x (RightAdjointSection.adjunction a)
```
