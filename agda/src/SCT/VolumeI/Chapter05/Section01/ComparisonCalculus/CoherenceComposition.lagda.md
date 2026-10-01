# Operation comparisons for a composite change

The operation-compatibility data for two weak changes compose. The proof constructs the new comparisons by pasting and does not assert preservation of every selected higher witness.

```agda
{-# OPTIONS --safe --without-K #-}
module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.CoherenceComposition where
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
open import SCT.VolumeI.Chapter05.Section01.Coherence
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Composition as Composition
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Operations as Operations
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Squares as Squares
import SCT.VolumeI.Chapter05.Section01.Products as Products

module Closure {l : Level} {R S T : Theory l l l}
  (V : Weakening S T) (W : Weakening R S)
  (kv : OperationCompatibility V) (kw : OperationCompatibility W) where
  private
    module R = View R
    module S = View S
    module T = View T
    module V = Weakening V
    module W = Weakening W
    module VW = Weakening (compose V W)
  open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
  open Calculus T

  map-square : {A B C D : S.CAT} (a : S.MAP A B) (b : S.MAP B D)
    (c : S.MAP A C) (d : S.MAP C D)
    → S._=₁_ (S._∘_ b a) (S._∘_ d c)
    → T._=₁_ (V.map b ∘ V.map a) (V.map d ∘ V.map c)
  map-square a b c d p = V.comp c d ∙ (V.term p ∙ (V.comp a b) ⁻¹)

  inversion : {C D : R.CAT} (f g : R.MAP C D)
    → T._=₁_ (VW.phi g f ∘ VW.map R.＝-inv) (T.＝-inv ∘ VW.phi f g)
  inversion f g =
    T.comp-assoc (V.map (W.phi f g)) (V.phi (W.map f) (W.map g)) T.＝-inv ∙
    (OperationCompatibility.inversion kv (W.map f) (W.map g) ▷ V.map (W.phi f g)) ∙
    (T.comp-assoc (V.map (W.phi f g)) (V.map S.＝-inv) (V.phi (W.map g) (W.map f))) ⁻¹ ∙
    (V.phi (W.map g) (W.map f) ◁
      map-square (W.map R.＝-inv) (W.phi g f) (W.phi f g) S.＝-inv
        (OperationCompatibility.inversion kw f g)) ∙
    T.comp-assoc (V.map (W.map R.＝-inv)) (V.map (W.phi g f)) (V.phi (W.map g) (W.map f))

  identityIso : {C D : R.CAT} (f : R.MAP C D)
    → T._=₂_ (VW.term (R.idIso f)) (T.idIso (VW.map f))
  identityIso f = OperationCompatibility.identityIso kv (W.map f) ∙
    (V.cell2 (OperationCompatibility.identityIso kw f) ∙
      (Composition.Two.sequential-term V W (R.idIso f)) ⁻¹)

  vertical : {C D : R.CAT} (f g h : R.MAP C D)
    → T._=₁_ (Boundaries.vertical-source (compose V W) f g h)
      (Boundaries.vertical-target (compose V W) f g h)
  vertical f g h =
    T.comp-assoc (V.map (W.map R.isoComp)) (V.map (W.phi f h)) (V.phi (W.map f) (W.map h)) then
    (V.phi (W.map f) (W.map h) ◁ (V.comp (W.map R.isoComp) (W.phi f h)) ⁻¹) then
    (V.phi (W.map f) (W.map h) ◁ V.term (OperationCompatibility.vertical kw f g h)) then
    Operations.vertical-family V kv (S._∘_ (W.phi g h) (W.map R.pr₁))
      (S._∘_ (W.phi f g) (W.map R.pr₂)) then
    isoComp-cong
      ((V.phi (W.map g) (W.map h) ◁ V.comp (W.map R.pr₁) (W.phi g h)) then
        (T.comp-assoc (V.map (W.map R.pr₁)) (V.map (W.phi g h)) (V.phi (W.map g) (W.map h))) ⁻¹)
      ((V.phi (W.map f) (W.map g) ◁ V.comp (W.map R.pr₂) (W.phi f g)) then
        (T.comp-assoc (V.map (W.map R.pr₂)) (V.map (W.phi f g)) (V.phi (W.map f) (W.map g))) ⁻¹)

  post : {C D E : R.CAT} (f g : R.MAP C D) (u : R.MAP D E)
    → T._=₁_ (Boundaries.post-source (compose V W) f g u)
      (Boundaries.post-target (compose V W) f g u)
  post f g u = Squares.solve T (VW.comp f u) (VW.comp g u) _ _
    (Squares.paste T (V.term (W.comp f u)) (V.comp (W.map f) (W.map u))
      (V.term (W.comp g u)) (V.comp (W.map g) (W.map u)) _ _ _
      (Squares.change T (V.term (W.comp f u)) (V.term (W.comp g u))
        (Operations.transport-square V kv (W.comp f u) (W.comp g u) _ _
          (Operations.post-square W kw f g u))
        (Operations.family-composite V (W.phi (R._∘_ u f) (R._∘_ u g)) (W.map (R.postWhisker u)))
        (T.idIso _))
      (Operations.post-family-square V kv (W.map u) (W.phi f g)))

  pre : {B C D : R.CAT} (f g : R.MAP C D) (k : R.MAP B C)
    → T._=₁_ (Boundaries.pre-source (compose V W) f g k)
      (Boundaries.pre-target (compose V W) f g k)
  pre f g k = Squares.solve T (VW.comp k f) (VW.comp k g) _ _
    (Squares.paste T (V.term (W.comp k f)) (V.comp (W.map k) (W.map f))
      (V.term (W.comp k g)) (V.comp (W.map k) (W.map g)) _ _ _
      (Squares.change T (V.term (W.comp k f)) (V.term (W.comp k g))
        (Operations.transport-square V kv (W.comp k f) (W.comp k g) _ _
          (Operations.pre-square W kw f g k))
        (Operations.family-composite V (W.phi (R._∘_ f k) (R._∘_ g k)) (W.map (R.preWhisker k)))
        (T.idIso _))
      (Operations.pre-family-square V kv (W.map k) (W.phi f g)))

  leftUnit : {C D : R.CAT} (f : R.MAP C D)
    → T._=₂_ (VW.term (R.comp-unitˡ f))
      (T.comp-unitˡ (VW.map f) ∙ ((VW.unit D ▷ VW.map f) ∙ VW.comp f (R.id D)))
  leftUnit {D = D} f =
    (Composition.Two.sequential-term V W (R.comp-unitˡ f)) ⁻¹ then
    V.cell2 (OperationCompatibility.leftUnit kw f) then
    Operations.vertical-term V kv (S.comp-unitˡ (W.map f))
      (S._∙_ (S._▷_ (W.unit D) (W.map f)) (W.comp f (R.id D))) then
    isoComp-cong (OperationCompatibility.leftUnit kv (W.map f))
      (Operations.vertical-term V kv (S._▷_ (W.unit D) (W.map f)) (W.comp f (R.id D))) then
    middle-square (T.comp-unitˡ (VW.map f)) (V.unit (W.cat D) ▷ VW.map f)
      (V.comp (W.map f) (S.id (W.cat D))) (V.term (S._▷_ (W.unit D) (W.map f)))
      (V.term (W.comp f (R.id D))) (V.term (W.unit D) ▷ VW.map f)
      (V.comp (W.map f) (W.map (R.id D)))
      (Operations.pre-term-square V kv (W.map f) (W.unit D)) then
    isoComp-cong (T.idIso _)
      (isoComp-cong ((preWhisker-isoComp-at (V.unit (W.cat D)) (V.term (W.unit D)) (VW.map f)) ⁻¹)
        (T.idIso _))

  rightUnit : {C D : R.CAT} (f : R.MAP C D)
    → T._=₂_ (VW.term (R.comp-unitʳ f))
      (T.comp-unitʳ (VW.map f) ∙ ((VW.map f ◁ VW.unit C) ∙ VW.comp (R.id C) f))
  rightUnit {C = C} f =
    (Composition.Two.sequential-term V W (R.comp-unitʳ f)) ⁻¹ then
    V.cell2 (OperationCompatibility.rightUnit kw f) then
    Operations.vertical-term V kv (S.comp-unitʳ (W.map f))
      (S._∙_ (S._◁_ (W.map f) (W.unit C)) (W.comp (R.id C) f)) then
    isoComp-cong (OperationCompatibility.rightUnit kv (W.map f))
      (Operations.vertical-term V kv (S._◁_ (W.map f) (W.unit C)) (W.comp (R.id C) f)) then
    middle-square (T.comp-unitʳ (VW.map f)) (VW.map f ◁ V.unit (W.cat C))
      (V.comp (S.id (W.cat C)) (W.map f)) (V.term (S._◁_ (W.map f) (W.unit C)))
      (V.term (W.comp (R.id C) f)) (VW.map f ◁ V.term (W.unit C))
      (V.comp (W.map (R.id C)) (W.map f))
      (Operations.post-term-square V kv (W.map f) (W.unit C)) then
    isoComp-cong (T.idIso _)
      (isoComp-cong ((postWhisker-isoComp-at (VW.map f) (V.unit (W.cat C)) (V.term (W.unit C))) ⁻¹)
        (T.idIso _))

  associator : {B C D E : R.CAT} (f : R.MAP B C) (g : R.MAP C D) (h : R.MAP D E)
    → T._=₂_ (Boundaries.assoc-source (compose V W) f g h)
      (Boundaries.assoc-target (compose V W) f g h)
  associator f g h =
    isoComp-cong
      (postWhisker-isoComp-at (VW.map h) (V.comp (W.map f) (W.map g)) (V.term (W.comp f g)))
      (isoComp-cong (T.idIso _) ((Composition.Two.sequential-term V W (R.comp-assoc f g h)) ⁻¹)) then
    five-middle (VW.map h ◁ V.comp (W.map f) (W.map g)) (VW.map h ◁ V.term (W.comp f g))
      (V.comp (W.map (R._∘_ g f)) (W.map h)) (V.term (W.comp (R._∘_ g f) h))
      (V.term (W.term (R.comp-assoc f g h)))
      (V.comp (S._∘_ (W.map g) (W.map f)) (W.map h))
      (V.term (S._◁_ (W.map h) (W.comp f g)))
      ((Operations.post-term-square V kv (W.map h) (W.comp f g)) ⁻¹) then
    isoComp-cong (T.idIso _) (isoComp-cong (T.idIso _)
      ((Operations.vertical-term V kv (S._◁_ (W.map h) (W.comp f g))
          (S._∙_ (W.comp (R._∘_ g f) h) (W.term (R.comp-assoc f g h))) then
        isoComp-cong (T.idIso _)
          (Operations.vertical-term V kv (W.comp (R._∘_ g f) h) (W.term (R.comp-assoc f g h)))) ⁻¹ then
      V.cell2 (OperationCompatibility.associator kw f g h) then
      Operations.vertical-term V kv (S.comp-assoc (W.map f) (W.map g) (W.map h))
        (S._∙_ (S._▷_ (W.comp g h) (W.map f)) (W.comp f (R._∘_ h g))) then
      isoComp-cong (T.idIso _)
        (Operations.vertical-term V kv (S._▷_ (W.comp g h) (W.map f)) (W.comp f (R._∘_ h g))))) then
    three-prefix _ _ _ _ then
    isoComp-cong (OperationCompatibility.associator kv (W.map f) (W.map g) (W.map h)) (T.idIso _) then
    middle-square (T.comp-assoc (VW.map f) (VW.map g) (VW.map h))
      (V.comp (W.map g) (W.map h) ▷ VW.map f)
      (V.comp (W.map f) (S._∘_ (W.map h) (W.map g)))
      (V.term (S._▷_ (W.comp g h) (W.map f))) (V.term (W.comp f (R._∘_ h g)))
      (V.term (W.comp g h) ▷ VW.map f) (V.comp (W.map f) (W.map (R._∘_ h g)))
      (Operations.pre-term-square V kv (W.map f) (W.comp g h)) then
    isoComp-cong (T.idIso _) (isoComp-cong
      ((preWhisker-isoComp-at (V.comp (W.map g) (W.map h)) (V.term (W.comp g h)) (VW.map f)) ⁻¹)
      (T.idIso _))

  operations : OperationCompatibility (compose V W)
  operations = record
    { products = Products.compose-products V W (OperationCompatibility.products kv) (OperationCompatibility.products kw)
    ; post = post ; pre = pre ; inversion = inversion ; identityIso = identityIso
    ; vertical = vertical ; associator = associator ; leftUnit = leftUnit ; rightUnit = rightUnit }
```
