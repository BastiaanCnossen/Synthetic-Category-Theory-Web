# Universal-property comparisons

Preserving a constructor includes preserving its specified universal
property. The source and target of that universal property may themselves
contain constructors. We form their comparisons first, and then compare
the selected inverse, section, and retraction by the common rule for
equivalence witnesses.

The initial category, coproducts, and functor categories below illustrate
this rule with changing category expressions. None of these records
identifies the two selected witnesses by proof irrelevance.

The squares for the compound coproduct-restriction and evaluation
functors are supplied as data below. Their agreement with the recursive
expression comparisons is a separate, currently unproved obligation.
The certificate records are therefore relative to these supplied squares.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core using (Weakening)
open import SCT.VolumeI.Chapter05.Section01.Products using (PreservesProducts)
import SCT.VolumeI.Chapter05.Section01.Expressions.ComparisonObjects as Objects
import SCT.VolumeI.Chapter05.Section01.ComparisonWitnesses as Witnesses
import SCT.VolumeI.Chapter05.Section01.MappingPreservation as MappingPreservation
import SCT.VolumeI.Chapter05.Section01.FunctorPreservation as FunctorPreservation
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Initial as Initial
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Functors
import SCT.VolumeI.Chapter01.Section07.Evaluation as Evaluation

module SCT.VolumeI.Chapter05.Section01.ConstructorCertificates
  {l : Level} {S T : Theory l l l} (W : Weakening S T) (WP : PreservesProducts W)
  (MS : Mapping.MappingAnimae S) (MT : Mapping.MappingAnimae T)
  (MC : MappingPreservation.MappingComparison W WP MS MT) where

private
  module S = View S
  module T = View T
module W = Weakening W
module O = Objects W WP
module M = MappingPreservation.Comparisons W WP MS MT MC using (fixed; mapping; product)
open T using (_∘_; _◁_; _⁻¹)
open Calculus T using (_then_)

module InitialComparison (IS : Initial.InitialStructure S MS) (IT : Initial.InitialStructure T MT) where
  module IS = Initial.InitialStructure IS
  module IT = Initial.InitialStructure IT

  record Comparison : Set l where
    field
      category : T.Equiv (W.cat IS.Zero) IT.Zero
    initial-object : O.Object
    initial-object = record { source = IS.Zero ; target = IT.Zero ; comparison = category }
    field
      universal : (C : S.CAT)
        → Witnesses.EquivalenceComparison W WP (O.terminate (M.mapping initial-object (M.fixed C)))
          (IS.maps-from-zero-contractible C) (IT.maps-from-zero-contractible (W.cat C))

  record Strictness (K : Comparison)
    (SS : Initial.StrictInitial S MS IS) (ST : Initial.StrictInitial T MT IT) : Set l where
    open Comparison K
    into-zero : {C : S.CAT} (f : S.MAP C IS.Zero) → O.Arrow (M.fixed C) initial-object
    into-zero f = record { source = f ; target = O.Object.arrow initial-object ∘ W.map f
      ; square = (T.comp-unitʳ _) ⁻¹ }
    field
      certificate : {C : S.CAT} (f : S.MAP C IS.Zero)
        → Witnesses.EquivalenceComparison W WP (into-zero f)
          (Initial.StrictInitial.into-zero-isEquiv SS f)
          (Initial.StrictInitial.into-zero-isEquiv ST (O.Arrow.target (into-zero f)))

module CoproductComparison (CS : Coproducts.CoproductStructure S MS) (CT : Coproducts.CoproductStructure T MT) where
  module CS = Coproducts.CoproductStructure CS
  module CT = Coproducts.CoproductStructure CT

  record Comparison : Set l where
    field
      category : (C D : S.CAT) → T.Equiv (W.cat (CS._⊔_ C D)) (CT._⊔_ (W.cat C) (W.cat D))
    coproduct : (C D : S.CAT) → O.Object
    coproduct C D = record { source = CS._⊔_ C D ; target = CT._⊔_ (W.cat C) (W.cat D) ; comparison = category C D }
    field
      first : (C D : S.CAT) → T._=₁_
        (O.Object.arrow (coproduct C D) ∘ W.map (CS.in₁ {C} {D})) (CT.in₁ {W.cat C} {W.cat D})
      second : (C D : S.CAT) → T._=₁_
        (O.Object.arrow (coproduct C D) ∘ W.map (CS.in₂ {C} {D})) (CT.in₂ {W.cat C} {W.cat D})
      square : (C D E : S.CAT) → T._=₁_
        (O.Object.arrow (O.product (M.mapping (M.fixed C) (M.fixed E)) (M.mapping (M.fixed D) (M.fixed E)))
          ∘ W.map (CS.coproductRestriction C D E))
        (CT.coproductRestriction (W.cat C) (W.cat D) (W.cat E)
          ∘ O.Object.arrow (M.mapping (coproduct C D) (M.fixed E)))
    restriction : (C D E : S.CAT)
      → O.Arrow (M.mapping (coproduct C D) (M.fixed E))
          (O.product (M.mapping (M.fixed C) (M.fixed E)) (M.mapping (M.fixed D) (M.fixed E)))
    restriction C D E = record { source = CS.coproductRestriction C D E
      ; target = CT.coproductRestriction (W.cat C) (W.cat D) (W.cat E) ; square = square C D E }
    field
      universal : (C D E : S.CAT) → Witnesses.EquivalenceComparison W WP (restriction C D E)
        (CS.coproductRestriction-isEquiv C D E) (CT.coproductRestriction-isEquiv (W.cat C) (W.cat D) (W.cat E))

module FunctorComparison
  (FS : Functors.FunctorCategories S MS) (FT : Functors.FunctorCategories T MT)
  (FC : FunctorPreservation.FunctorComparison W MS MT FS FT) where
  module FS = Functors.FunctorCategories FS
  module FT = Functors.FunctorCategories FT
  module FC = FunctorPreservation.FunctorComparison FC

  functors : (C D : S.CAT) → O.Object
  functors C D = record { source = FS.Fun C D ; target = FT.Fun (W.cat C) (W.cat D) ; comparison = FC.functor C D }

  record Universal : Set l where
    field
      square : (C D X : S.CAT) → T._=₁_
        (O.Object.arrow (M.mapping (M.product X C) (M.fixed D))
          ∘ W.map (Evaluation.Evaluation.At.forward S MS (FS.funEval {C} {D}) X))
        (Evaluation.Evaluation.At.forward T MT (FT.funEval {W.cat C} {W.cat D}) (W.cat X)
          ∘ O.Object.arrow (M.mapping (M.fixed X) (functors C D)))
    evaluation : (C D X : S.CAT)
      → O.Arrow (M.mapping (M.fixed X) (functors C D)) (M.mapping (M.product X C) (M.fixed D))
    evaluation C D X = record
      { source = Evaluation.Evaluation.At.forward S MS (FS.funEval {C} {D}) X
      ; target = Evaluation.Evaluation.At.forward T MT (FT.funEval {W.cat C} {W.cat D}) (W.cat X)
      ; square = square C D X }
    field
      certificate : (C D X : S.CAT) → Witnesses.EquivalenceComparison W WP (evaluation C D X)
        (FS.funUniversal C D X) (FT.funUniversal (W.cat C) (W.cat D) (W.cat X))
```
