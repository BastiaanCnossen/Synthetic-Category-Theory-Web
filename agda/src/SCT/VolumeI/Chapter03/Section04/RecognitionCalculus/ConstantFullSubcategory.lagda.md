# Constant arrows form a full subcategory

This is `(2) ⇒ (3)` in
`prop:Equivalent_Conditions_Geometric_Realization`. If the realization
of `[1]` is contractible, its localization universal property identifies
the full subcategory of inverting functors with the target category.
The comparison with the ambient arrow category is the constant-arrow
functor itself.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter03.Section04.RecognitionCalculus.ConstantFullSubcategory
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Walking.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section07.Currying 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M ℱ
  using (funPre; funPre-comp; funPre-cong; funPre-isEquiv; funPre-uncurry)
open import SCT.VolumeI.Chapter01.Section07.TerminalDomain 𝒯 M ℱ using (module TerminalContext)
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ using (constantDiagram)
open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I using (identityArrow)
open import SCT.VolumeI.Chapter03.Section01.MorphismCollections 𝒯 M P I using (allMorphisms)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section02.FullSubcategories 𝒯 M P using (IsFullSubcategory)
open import SCT.VolumeI.Chapter03.Section02.Factorization.FullSubcategoryEquivalences 𝒯 M P
  using (full-subcategory-precompose-equivalence)
open import SCT.VolumeI.Chapter03.Section03.Localizations 𝒯 M ℱ P I E S Q R using (module WithSubcategories)
open import SCT.VolumeI.Chapter03.Section03.MappingCalculus.LocalizationFullSubcategory 𝒯 M ℱ P I E S Q R
  using (localization-restriction-isFullSubcategory)

constant-restrict : {A B D : CAT} (f : MAP A B) →
  (funPre f ∘ constantDiagram B D) =₁ constantDiagram A D
constant-restrict f = funReflect _ _
  ((funCurry-β pr₁) ⁻¹ ∙
    (comp-unitˡ pr₁ ∙
      (pair-β₁ (id _ ∘ pr₁) (f ∘ pr₂) ∙
        ((funCurry-β pr₁ ▷ productMap (id _) f) ∙
          funPre-uncurry f (constantDiagram _ _)))))

module FromContractible (L : SubcategoryAxiom) (T : CAT) (l : MAP [1] T)
  (localization : WithSubcategories.IsLocalization L (allMorphisms [1]) l)
  (contractible : IsContractible T) where
  module At (D : CAT) where
    point = TerminalContext.forward D
    termination = funPre {D = D} (terminate T)
    comparison : MAP D (Fun T D)
    comparison = termination ∘ point

    comparison-isEquiv : IsEquiv comparison
    comparison-isEquiv = equiv-compose point termination (TerminalContext.forward-isEquiv D)
      (funPre-isEquiv (terminate T) contractible)

    over-arrows : (funPre l ∘ comparison) =₁ identityArrow
    over-arrows = constant-restrict {D = D} (terminate [1]) ∙
      ((funPre-cong {D = D} (terminal-iso (terminate T ∘ l) (terminate [1])) ▷ point) ∙
        ((funPre-comp l (terminate T) ▷ point) ∙
          (comp-assoc point termination (funPre l)) ⁻¹))

    identityArrow-isFullSubcategory : IsFullSubcategory (identityArrow {D})
    identityArrow-isFullSubcategory = full-subcategory-precompose-equivalence
      {A = D} {B = Fun T D} {C = Fun [1] D}
      identityArrow (funPre l) comparison comparison-isEquiv over-arrows
      (localization-restriction-isFullSubcategory L (allMorphisms [1]) l localization D)
```
