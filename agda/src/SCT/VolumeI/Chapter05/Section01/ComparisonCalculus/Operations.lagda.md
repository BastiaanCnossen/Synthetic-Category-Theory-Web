# Transport of identification families

Identification families are mapped using the comparison for the whole identification anima. Compatibility with composition and whiskering is then expressed with their adjusted endpoints.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
open import SCT.VolumeI.Chapter05.Section01.Coherence
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Squares as Squares

module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Operations {l : Level} {S T : Theory l l l}
  (W : Weakening S T) where
private
  module S = View S
  module T = View T
open Weakening W
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T

family : {X C D : S.CAT} {f g : S.MAP C D}
  → S.MAP X (S._＝_ f g) → T.MAP (cat X) (T._＝_ (map f) (map g))
family {f = f} {g} alpha = phi f g ∘ map alpha

family-cong : {X C D : S.CAT} {f g : S.MAP C D}
  {alpha beta : S.MAP X (S._＝_ f g)} → S._=₁_ alpha beta
  → T._=₁_ (family alpha) (family beta)
family-cong {f = f} {g} p = phi f g ◁ term p

family-composite : {X Y C D : S.CAT} {f g : S.MAP C D}
  (alpha : S.MAP Y (S._＝_ f g)) (r : S.MAP X Y)
  → T._=₁_ (family (S._∘_ alpha r)) (family alpha ∘ map r)
family-composite {f = f} {g} alpha r = (phi f g ◁ comp r alpha) then
  (T.comp-assoc (map r) (map alpha) (phi f g)) ⁻¹

to-terminal : {X : T.CAT} (r : T.MAP X (cat S.One))
  → T._=₁_ r (back ∘ T.terminate X)
to-terminal r = (T.comp-unitˡ r) ⁻¹ then
  (T.IsEquiv.sectionIso (T.Equiv.isEquiv terminal) ▷ r) then
  T.comp-assoc r (T.Equiv.functor terminal) back then
  (back ◁ T.terminal-iso _ _)

family-const : {X C D : S.CAT} {f g : S.MAP C D} (alpha : S._=₁_ f g)
  → T._=₁_ (family (S.const {P = X} alpha)) (T.const (term alpha))
family-const {X} {f = f} {g} alpha = family-composite alpha (S.terminate X) then
  ((phi f g ∘ map alpha) ◁ to-terminal (map (S.terminate X))) then
  (T.comp-assoc (T.terminate (cat X)) back (phi f g ∘ map alpha)) ⁻¹

pair-map : {X A B : S.CAT} {A' B' : T.CAT}
  (a : T.MAP (cat A) A') (b : T.MAP (cat B) B')
  (x : S.MAP X A) (y : S.MAP X B)
  → T._=₁_ (T.pair (a ∘ map S.pr₁) (b ∘ map S.pr₂) ∘ map (S.pair x y))
      (T.pair (a ∘ map x) (b ∘ map y))
pair-map a b x y = pair-pre (a ∘ map S.pr₁) (b ∘ map S.pr₂) (map (S.pair x y)) then
  pair-cong
    (T.comp-assoc (map (S.pair x y)) (map S.pr₁) a then
      (a ◁ ((comp (S.pair x y) S.pr₁) ⁻¹ then term (S.pair-β₁ x y))))
    (T.comp-assoc (map (S.pair x y)) (map S.pr₂) b then
      (b ◁ ((comp (S.pair x y) S.pr₂) ⁻¹ then term (S.pair-β₂ x y))))

vertical-family : (K : OperationCompatibility W)
  {X C D : S.CAT} {f g h : S.MAP C D}
  (beta : S.MAP X (S._＝_ g h)) (alpha : S.MAP X (S._＝_ f g))
  → T._=₁_ (phi f h ∘ map (S._∙_ beta alpha))
      (T._∙_ (phi g h ∘ map beta) (phi f g ∘ map alpha))
vertical-family K {f = f} {g} {h} beta alpha =
  (phi f h ◁ comp (S.pair beta alpha) S.isoComp) then
  (T.comp-assoc (map (S.pair beta alpha)) (map S.isoComp) (phi f h)) ⁻¹ then
  (OperationCompatibility.vertical K f g h ▷ map (S.pair beta alpha)) then
  T.comp-assoc (map (S.pair beta alpha))
    (T.pair (phi g h ∘ map S.pr₁) (phi f g ∘ map S.pr₂)) T.isoComp then
  (T.isoComp ◁ pair-map (phi g h) (phi f g) beta alpha)

vertical-term : (K : OperationCompatibility W)
  {C D : S.CAT} {f g h : S.MAP C D}
  (beta : S._=₁_ g h) (alpha : S._=₁_ f g)
  → T._=₂_ (term (S._∙_ beta alpha)) (term beta ∙ term alpha)
vertical-term K beta alpha = (vertical-family K beta alpha ▷ back) then
  isoComp-pre _ _ back

transport-square : (K : OperationCompatibility W)
  {X C D : S.CAT} {f f' g g' : S.MAP C D}
  (p : S._=₁_ f f') (q : S._=₁_ g g')
  (alpha : S.MAP X (S._＝_ f g)) (beta : S.MAP X (S._＝_ f' g'))
  → S._=₁_ (S._∙_ (S.const q) alpha) (S._∙_ beta (S.const p))
  → T._=₁_ (T.const (term q) ∙ family alpha) (family beta ∙ T.const (term p))
transport-square K p q alpha beta square =
  (vertical-family K (S.const q) alpha then isoComp-cong (family-const q) (T.idIso _)) ⁻¹ then
  family-cong square then
  vertical-family K beta (S.const p) then isoComp-cong (T.idIso _) (family-const p)

post-square : (K : OperationCompatibility W)
  {C D E : S.CAT} (f g : S.MAP C D) (u : S.MAP D E)
  → T._=₁_ (T.const (comp g u) ∙ family (S.postWhisker u))
    ((T.postWhisker (map u) ∘ phi f g) ∙ T.const (comp f u))
post-square K f g u = Squares.unsolve T (comp f u) (comp g u) _ _
  (OperationCompatibility.post K f g u)

pre-square : (K : OperationCompatibility W)
  {B C D : S.CAT} (f g : S.MAP C D) (k : S.MAP B C)
  → T._=₁_ (T.const (comp k g) ∙ family (S.preWhisker k))
    ((T.preWhisker (map k) ∘ phi f g) ∙ T.const (comp k f))
pre-square K f g k = Squares.unsolve T (comp k f) (comp k g) _ _
  (OperationCompatibility.pre K f g k)

post-family-square : (K : OperationCompatibility W)
  {X C D E : S.CAT} {f g : S.MAP C D}
  (u : S.MAP D E) (alpha : S.MAP X (S._＝_ f g))
  → T._=₁_ (T.const (comp g u) ∙ family (S._◁_ u alpha))
      ((map u ◁ family alpha) ∙ T.const (comp f u))
post-family-square K {f = f} {g} u alpha =
  Squares.change T (comp f u) (comp g u)
    (Squares.precompose T (comp f u) (comp g u) _ _ (post-square K f g u) (map alpha))
    ((family-composite (S.postWhisker u) alpha) ⁻¹)
    (T.comp-assoc (map alpha) (phi f g) (T.postWhisker (map u)))

pre-family-square : (K : OperationCompatibility W)
  {X B C D : S.CAT} {f g : S.MAP C D}
  (k : S.MAP B C) (alpha : S.MAP X (S._＝_ f g))
  → T._=₁_ (T.const (comp k g) ∙ family (S._▷_ alpha k))
      ((family alpha ▷ map k) ∙ T.const (comp k f))
pre-family-square K {f = f} {g} k alpha =
  Squares.change T (comp k f) (comp k g)
    (Squares.precompose T (comp k f) (comp k g) _ _ (pre-square K f g k) (map alpha))
    ((family-composite (S.preWhisker k) alpha) ⁻¹)
    (T.comp-assoc (map alpha) (phi f g) (T.preWhisker (map k)))

post-term-square : (K : OperationCompatibility W)
  {C D E : S.CAT} {f g : S.MAP C D}
  (u : S.MAP D E) (alpha : S._=₁_ f g)
  → T._=₂_ (comp g u ∙ term (S._◁_ u alpha)) ((map u ◁ term alpha) ∙ comp f u)
post-term-square K {f = f} {g} u alpha =
  Squares.at T (comp f u) (comp g u) _ _ (post-family-square K u alpha) back then
  isoComp-cong (postWhisker-pre (map u) (family alpha) back) (T.idIso _)

pre-term-square : (K : OperationCompatibility W)
  {B C D : S.CAT} {f g : S.MAP C D}
  (k : S.MAP B C) (alpha : S._=₁_ f g)
  → T._=₂_ (comp k g ∙ term (S._▷_ alpha k)) ((term alpha ▷ map k) ∙ comp k f)
pre-term-square K {f = f} {g} k alpha =
  Squares.at T (comp k f) (comp k g) _ _ (pre-family-square K k alpha) back then
  isoComp-cong (preWhisker-pre (family alpha) (map k) back) (T.idIso _)
```
