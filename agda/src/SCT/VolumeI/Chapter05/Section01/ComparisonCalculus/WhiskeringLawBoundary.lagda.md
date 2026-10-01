# Boundaries of the whiskering laws

The source whiskering laws are transported after their input and output comparisons have been inserted. The constructed boundaries are used by ChosenWhiskering to state preservation of the selected witnesses.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
open import SCT.VolumeI.Chapter05.Section01.Coherence
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Operations as Operations
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Squares as Squares
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Whiskering as Whiskering
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.WitnessNormalization as WitnessNormalization
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.FamilyWitness as FamilyWitness
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.FamilyPasting as Pasting
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.ParameterizedWhiskering as Parameterized
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.VerticalBoundary as Vertical

module SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.WhiskeringLawBoundary {l : Level} {S T : Theory l l l}
  (W : Weakening S T) (K : OperationCompatibility W) where
private
  module S = View S
  module T = View T
open Weakening W
open T using (_∘_; _∙_; _◁_; _▷_; _⁻¹)
open Calculus T
open Operations W using (family; vertical-family; post-family-square; pre-family-square)
open Boundaries W using (conjugate)

opaque
  conjugate-identity : {C D : T.CAT} {f g : T.MAP C D} (p : T._=₁_ f g)
    → T._=₂_ (conjugate p p ∘ T.idIso f) (T.idIso g)
  conjugate-identity p = Squares.term-solve T p p (T.idIso _) (T.idIso _)
    (isoComp-unitʳ-at p then (isoComp-unitˡ-at p) ⁻¹)

module PostIdentity {C D E : S.CAT} (u : S.MAP D E) (f : S.MAP C D) where
  adjust = conjugate (comp f u) (comp f u)
  opaque
    left : T._=₂_ (adjust ∘ term (S._◁_ u (S.idIso f))) (map u ◁ T.idIso (map f))
    left = Whiskering.Normalized.post-identification W K u (S.idIso f) then
      (T.postWhisker (map u) ◁ OperationCompatibility.identityIso K f)
    right : T._=₂_ (adjust ∘ term (S.idIso (S._∘_ u f))) (T.idIso (map u ∘ map f))
    right = (adjust ◁ OperationCompatibility.identityIso K (S._∘_ u f)) then conjugate-identity (comp f u)
  module Law = WitnessNormalization W (S._◁_ u (S.idIso f)) (S.idIso (S._∘_ u f))
    adjust (map u ◁ T.idIso (map f)) (T.idIso (map u ∘ map f)) left right
  opaque
    transported : T._=₂_ (map u ◁ T.idIso (map f)) (T.idIso (map u ∘ map f))
    transported = Law.normalized (S.postWhisker-idIso u f)
    expansion : T._=₃_ transported (Law.normalized (S.postWhisker-idIso u f))
    expansion = T.idIso _

module PreIdentity {B C D : S.CAT} (f : S.MAP C D) (k : S.MAP B C) where
  adjust = conjugate (comp k f) (comp k f)
  opaque
    left : T._=₂_ (adjust ∘ term (S._▷_ (S.idIso f) k)) (T.idIso (map f) ▷ map k)
    left = Whiskering.Normalized.pre-identification W K k (S.idIso f) then
      (T.preWhisker (map k) ◁ OperationCompatibility.identityIso K f)
    right : T._=₂_ (adjust ∘ term (S.idIso (S._∘_ f k))) (T.idIso (map f ∘ map k))
    right = (adjust ◁ OperationCompatibility.identityIso K (S._∘_ f k)) then conjugate-identity (comp k f)
  module Law = WitnessNormalization W (S._▷_ (S.idIso f) k) (S.idIso (S._∘_ f k))
    adjust (T.idIso (map f) ▷ map k) (T.idIso (map f ∘ map k)) left right
  opaque
    transported : T._=₂_ (T.idIso (map f) ▷ map k) (T.idIso (map f ∘ map k))
    transported = Law.normalized (S.preWhisker-idIso f k)
    expansion : T._=₃_ transported (Law.normalized (S.preWhisker-idIso f k))
    expansion = T.idIso _

module PostVertical {C D E : S.CAT} (f g h : S.MAP C D) (u : S.MAP D E) where
  X = S._×_ (S._＝_ g h) (S._＝_ f g)
  alpha : S.MAP X (S._＝_ f g)
  alpha = S.pr₂
  beta : S.MAP X (S._＝_ g h)
  beta = S.pr₁
  a = S._◁_ u (S._∙_ beta alpha)
  b = S._∙_ (S._◁_ u beta) (S._◁_ u alpha)
  a' = map u ◁ (family beta ∙ family alpha)
  b' = (map u ◁ family beta) ∙ (map u ◁ family alpha)
  adjust = conjugate (comp f u) (comp h u)
  output = adjust ∘ phi (S._∘_ u f) (S._∘_ u h)
  opaque
    left : T._=₁_ (output ∘ map a) a'
    left = T.comp-assoc (map a) (phi (S._∘_ u f) (S._∘_ u h)) adjust then
      Squares.solve T (comp f u) (comp h u) (family a) (map u ◁ family (S._∙_ beta alpha))
        (post-family-square K u (S._∙_ beta alpha)) then
      (T.postWhisker (map u) ◁ vertical-family K beta alpha)
    right : T._=₁_ (output ∘ map b) b'
    right = T.comp-assoc (map b) (phi (S._∘_ u f) (S._∘_ u h)) adjust then
      Squares.solve T (comp f u) (comp h u) (family b) b'
        (Pasting.vertical W K (comp f u) (comp g u) (comp h u)
          (S._◁_ u alpha) (S._◁_ u beta) (map u ◁ family alpha) (map u ◁ family beta)
          (post-family-square K u alpha) (post-family-square K u beta))
    target : T._=₁_ a' b'
    target = Parameterized.post-comp T (map u) (family beta) (family alpha)
  module Law = FamilyWitness W a b output a' b' left right

module FixedOuter {B C D : S.CAT} (F G : S.MAP C D) (h k : S.MAP B C)
  (tau : S._=₁_ F G) where
  sigma = S.id (S._＝_ h k)
  a = S._∙_ (S.const (S._▷_ tau k)) (S._◁_ F sigma)
  b = S._∙_ (S._◁_ G sigma) (S.const (S._▷_ tau h))
  a' = T.const (term tau ▷ map k) ∙ (map F ◁ phi h k)
  b' = (map G ◁ phi h k) ∙ T.const (term tau ▷ map h)
  adjust = conjugate (comp h F) (comp k G)
  output = adjust ∘ phi (S._∘_ F h) (S._∘_ G k)
  opaque
    post-square : (H : S.MAP C D)
      → T._=₁_ (T.const (comp k H) ∙ family (S._◁_ H sigma))
        ((map H ◁ phi h k) ∙ T.const (comp h H))
    post-square H = Squares.change T (comp h H) (comp k H)
      (post-family-square K H sigma) (T.idIso _)
      (T.postWhisker (map H) ◁ Vertical.identity-family W K h k)
    left : T._=₁_ (output ∘ map a) a'
    left = T.comp-assoc (map a) (phi (S._∘_ F h) (S._∘_ G k)) adjust then
      Squares.solve T (comp h F) (comp k G) (family a) a'
        (Pasting.vertical W K (comp h F) (comp k F) (comp k G)
          (S._◁_ F sigma) (S.const (S._▷_ tau k)) (map F ◁ phi h k) (T.const (term tau ▷ map k))
          (post-square F)
          (Pasting.constant W K (comp k F) (comp k G) (S._▷_ tau k) (term tau ▷ map k)
            (Operations.pre-term-square W K k tau)))
    right : T._=₁_ (output ∘ map b) b'
    right = T.comp-assoc (map b) (phi (S._∘_ F h) (S._∘_ G k)) adjust then
      Squares.solve T (comp h F) (comp k G) (family b) b'
        (Pasting.vertical W K (comp h F) (comp h G) (comp k G)
          (S.const (S._▷_ tau h)) (S._◁_ G sigma) (T.const (term tau ▷ map h)) (map G ◁ phi h k)
          (Pasting.constant W K (comp h F) (comp h G) (S._▷_ tau h) (term tau ▷ map h)
            (Operations.pre-term-square W K h tau)) (post-square G))
    target : T._=₁_ a' b'
    target = Parameterized.fixed-outer T (term tau) (phi h k)
  module Law = FamilyWitness W a b output a' b' left right

module FixedInner {B C D : S.CAT} (F G : S.MAP C D) (h k : S.MAP B C)
  (sigma : S._=₁_ h k) where
  tau = S.id (S._＝_ F G)
  a = S._∙_ (S._▷_ tau k) (S.const (S._◁_ F sigma))
  b = S._∙_ (S.const (S._◁_ G sigma)) (S._▷_ tau h)
  a' = (phi F G ▷ map k) ∙ T.const (map F ◁ term sigma)
  b' = T.const (map G ◁ term sigma) ∙ (phi F G ▷ map h)
  adjust = conjugate (comp h F) (comp k G)
  output = adjust ∘ phi (S._∘_ F h) (S._∘_ G k)
  opaque
    pre-square : (i : S.MAP B C)
      → T._=₁_ (T.const (comp i G) ∙ family (S._▷_ tau i))
        ((phi F G ▷ map i) ∙ T.const (comp i F))
    pre-square i = Squares.change T (comp i F) (comp i G)
      (pre-family-square K i tau) (T.idIso _)
      (T.preWhisker (map i) ◁ Vertical.identity-family W K F G)
    left : T._=₁_ (output ∘ map a) a'
    left = T.comp-assoc (map a) (phi (S._∘_ F h) (S._∘_ G k)) adjust then
      Squares.solve T (comp h F) (comp k G) (family a) a'
        (Pasting.vertical W K (comp h F) (comp k F) (comp k G)
          (S.const (S._◁_ F sigma)) (S._▷_ tau k) (T.const (map F ◁ term sigma)) (phi F G ▷ map k)
          (Pasting.constant W K (comp h F) (comp k F) (S._◁_ F sigma) (map F ◁ term sigma)
            (Operations.post-term-square W K F sigma)) (pre-square k))
    right : T._=₁_ (output ∘ map b) b'
    right = T.comp-assoc (map b) (phi (S._∘_ F h) (S._∘_ G k)) adjust then
      Squares.solve T (comp h F) (comp k G) (family b) b'
        (Pasting.vertical W K (comp h F) (comp h G) (comp k G)
          (S._▷_ tau h) (S.const (S._◁_ G sigma)) (phi F G ▷ map h) (T.const (map G ◁ term sigma))
          (pre-square h)
          (Pasting.constant W K (comp h G) (comp k G) (S._◁_ G sigma) (map G ◁ term sigma)
            (Operations.post-term-square W K G sigma)))
    target : T._=₁_ a' b'
    target = Parameterized.fixed-inner T (phi F G) (term sigma)
  module Law = FamilyWitness W a b output a' b' left right

module PreVertical {B C D : S.CAT} (f g h : S.MAP C D) (k : S.MAP B C) where
  X = S._×_ (S._＝_ g h) (S._＝_ f g)
  alpha : S.MAP X (S._＝_ f g)
  alpha = S.pr₂
  beta : S.MAP X (S._＝_ g h)
  beta = S.pr₁
  a = S._▷_ (S._∙_ beta alpha) k
  b = S._∙_ (S._▷_ beta k) (S._▷_ alpha k)
  a' = (family beta ∙ family alpha) ▷ map k
  b' = (family beta ▷ map k) ∙ (family alpha ▷ map k)
  adjust = conjugate (comp k f) (comp k h)
  output = adjust ∘ phi (S._∘_ f k) (S._∘_ h k)
  opaque
    left : T._=₁_ (output ∘ map a) a'
    left = T.comp-assoc (map a) (phi (S._∘_ f k) (S._∘_ h k)) adjust then
      Squares.solve T (comp k f) (comp k h) (family a) (family (S._∙_ beta alpha) ▷ map k)
        (pre-family-square K k (S._∙_ beta alpha)) then
      (T.preWhisker (map k) ◁ vertical-family K beta alpha)
    right : T._=₁_ (output ∘ map b) b'
    right = T.comp-assoc (map b) (phi (S._∘_ f k) (S._∘_ h k)) adjust then
      Squares.solve T (comp k f) (comp k h) (family b) b'
        (Pasting.vertical W K (comp k f) (comp k g) (comp k h)
          (S._▷_ alpha k) (S._▷_ beta k) (family alpha ▷ map k) (family beta ▷ map k)
          (pre-family-square K k alpha) (pre-family-square K k beta))
    target : T._=₁_ a' b'
    target = Parameterized.pre-comp T (family beta) (family alpha) (map k)
  module Law = FamilyWitness W a b output a' b' left right
```
