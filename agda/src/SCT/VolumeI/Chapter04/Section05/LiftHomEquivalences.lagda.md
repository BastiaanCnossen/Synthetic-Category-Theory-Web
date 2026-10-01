# Hom equivalences for chosen lifts

The adjoint section of directed evaluation identifies homs from a chosen
covariant lift with homs from its literal directed image. Taking an identity
arrow as target and using the evaluation hom equivalence gives an equivalence
from homs out of the endpoint of the lift. The source side of its filling
is precomposition with the original arrow. The cartesian case uses homs
from an identity arrow and the counit formula.

These are absolute hom equivalences. The directed images remain literal;
no section identification is silently made strict. Identifying the homs
in the directed pullback with a specified pullback of homs is a separate
step in the stronger extension property of cocartesian lifts.

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
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter04.Section05.LiftHomEquivalences
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section05.Fibrations 𝒯 M ℱ P I E S public
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.HomUnitFormula as Units
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.HomCounitFormula as Counits
import SCT.VolumeI.Chapter04.Section04.EvaluationHomEquivalences as Homs

module Covariant {A B : CAT} (f : MAP A B) (w : Fibration.CocartesianFibration f) where
  private
    module Eval = Evaluation f using (directed-ev₀; module Left)
    module W = Fibration.CocartesianFibration w using (lift; left-adjoint-section)

  module At (q : Obj-abs Eval.Left.category) (z : Obj-abs A) where
    arrow : Obj-abs (Ar A)
    arrow = W.lift ∘ q
    private
      module Identity = Homs.ToIdentity 𝒯 M ℱ P I E S Q R arrow z
        using (functor; isEquiv; source-functor; precompose; source-comparison)
    diagram : MAP (Hom (Ar A) arrow (identityArrow ∘ z))
      (Hom Eval.Left.category (Eval.directed-ev₀ ∘ arrow)
        (Eval.directed-ev₀ ∘ (identityArrow ∘ z)))
    diagram = hom-post Eval.directed-ev₀ arrow (identityArrow ∘ z)
    diagram-isEquiv : IsEquiv diagram
    diagram-isEquiv = Units.LeftSection.hom-post-isEquiv 𝒯 M ℱ P I E S Q
      W.left-adjoint-section q (identityArrow ∘ z)

    filling : MAP (Hom A (ev₁ ∘ arrow) z) (Hom (Ar A) arrow (identityArrow ∘ z))
    filling = IsEquiv.inverse Identity.isEquiv
    filling-isEquiv : IsEquiv filling
    filling-isEquiv = equiv-inverse Identity.isEquiv
    functor : MAP (Hom A (ev₁ ∘ arrow) z)
      (Hom Eval.Left.category (Eval.directed-ev₀ ∘ arrow)
        (Eval.directed-ev₀ ∘ (identityArrow ∘ z)))
    functor = diagram ∘ filling
    isEquiv : IsEquiv functor
    isEquiv = equiv-compose filling diagram filling-isEquiv diagram-isEquiv

    source-functor : MAP (Hom (Ar A) arrow (identityArrow ∘ z)) (Hom A (ev₀ ∘ arrow) z)
    source-functor = Identity.source-functor
    precompose : MAP (Hom A (ev₁ ∘ arrow) z) (Hom A (ev₀ ∘ arrow) z)
    precompose = Identity.precompose
    source-comparison-calculation : (source-functor ∘ filling) =₁ precompose
    source-comparison-calculation = comp-unitʳ precompose ∙
      ((precompose ◁ (IsEquiv.retractionIso Identity.isEquiv) ⁻¹) ∙
      (comp-assoc filling Identity.functor precompose ∙
        (Identity.source-comparison ▷ filling)))
    abstract
      source-comparison : (source-functor ∘ filling) =₁ precompose
      source-comparison = source-comparison-calculation
      source-comparison-computation : source-comparison =₂ source-comparison-calculation
      source-comparison-computation = idIso source-comparison-calculation

module Contravariant {A B : CAT} (f : MAP A B) (w : Fibration.CartesianFibration f) where
  private
    module Eval = Evaluation f using (directed-ev₁; module Right)
    module W = Fibration.CartesianFibration w using (lift; right-adjoint-section)

  module At (q : Obj-abs Eval.Right.category) (z : Obj-abs A) where
    arrow : Obj-abs (Ar A)
    arrow = W.lift ∘ q
    private
      module Identity = Homs.FromIdentity 𝒯 M ℱ P I E S Q R z arrow using (functor; isEquiv)
    diagram : MAP (Hom (Ar A) (identityArrow ∘ z) arrow)
      (Hom Eval.Right.category (Eval.directed-ev₁ ∘ (identityArrow ∘ z))
        (Eval.directed-ev₁ ∘ arrow))
    diagram = hom-post Eval.directed-ev₁ (identityArrow ∘ z) arrow
    diagram-isEquiv : IsEquiv diagram
    diagram-isEquiv = Counits.RightSection.hom-post-isEquiv 𝒯 M ℱ P I E S Q
      W.right-adjoint-section (identityArrow ∘ z) q

    filling : MAP (Hom A z (ev₀ ∘ arrow)) (Hom (Ar A) (identityArrow ∘ z) arrow)
    filling = IsEquiv.inverse Identity.isEquiv
    filling-isEquiv : IsEquiv filling
    filling-isEquiv = equiv-inverse Identity.isEquiv
    functor : MAP (Hom A z (ev₀ ∘ arrow))
      (Hom Eval.Right.category (Eval.directed-ev₁ ∘ (identityArrow ∘ z))
        (Eval.directed-ev₁ ∘ arrow))
    functor = diagram ∘ filling
    isEquiv : IsEquiv functor
    isEquiv = equiv-compose filling diagram filling-isEquiv diagram-isEquiv
```
