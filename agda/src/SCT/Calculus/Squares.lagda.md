# Pasting comparison routes

A route through a commutative diagram can be normalized by its component
squares and a specified cancellation. The objects, arrows, and comparison
witnesses remain parameters; these calculations use no equality of proofs.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.Calculus.Composition using (Composition; Laws)

module SCT.Calculus.Squares {o h p : Level}
  (C : Composition o h p) (L : Laws C) where

open Composition C
open Laws L
```

For two routes joined by an intermediate comparison, first normalize their
initial segment, then paste the input square, and finally cancel the
specified inverse pair. Each supplied square occurs in the resulting witness.

```agda
abstract
  comparison-route-pasting : {s₀ s₁ s₂ s₃ s₄ t z₀ z₁ z₂ z : Obj}
    (T : Hom t z) (R : Hom s₄ t) (A : Hom s₃ s₄) (G : Hom s₂ s₃)
    (B : Hom s₁ s₂) (η : Hom s₀ s₁)
    (n : Hom s₄ z₀) (W : Hom z₀ z₁) (WQ : Hom s₂ z₂)
    (changed : Hom z₁ z) (corner : Hom z₂ z₁)
    (application : Hom z₂ z) (inverseApplication : Hom z z₂)
    (application-route : Hom s₀ z)
    → (T ∘ R) ≈ ((changed ∘ W) ∘ n)
    → (corner ∘ WQ) ≈ (W ∘ (n ∘ (A ∘ G)))
    → (changed ∘ corner) ≈ application
    → (WQ ∘ (B ∘ η)) ≈ (inverseApplication ∘ application-route)
    → (application ∘ inverseApplication) ≈ id z
    → (T ∘ (R ∘ (A ∘ (G ∘ (B ∘ η))))) ≈ application-route
  comparison-route-pasting T R A G B η n W WQ changed corner application inverseApplication application-route
    normal inputChange cancelCorner cancelEvaluation cancelApplication =
    let tail = B ∘ η
        finish = trans (unitˡ application-route)
          (trans (congr cancelApplication (refl application-route))
          (trans (sym (assoc application inverseApplication application-route))
            (congr (refl application) cancelEvaluation)))
        normalizeTail = trans (congr cancelCorner (refl (WQ ∘ tail)))
          (trans (sym (assoc changed corner (WQ ∘ tail)))
          (trans (congr (refl changed) (assoc corner WQ tail))
            (congr (refl changed) (congr (sym inputChange) (refl tail)))))
        regroupInner = trans (sym (assoc W (n ∘ (A ∘ G)) tail))
          (trans (congr (refl W) (sym (assoc n (A ∘ G) tail)))
            (congr (refl W) (congr (refl n) (sym (assoc A G tail)))))
        regroup = trans (congr (refl changed) regroupInner)
          (trans (assoc changed W (n ∘ (A ∘ (G ∘ tail))))
            (assoc (changed ∘ W) n (A ∘ (G ∘ tail))))
        normalizeStart = trans (congr normal (refl (A ∘ (G ∘ tail))))
          (sym (assoc T R (A ∘ (G ∘ tail))))
    in trans finish (trans normalizeTail (trans regroup normalizeStart))
```

A square may be pasted after a factored input. If the outer action cancels
the top comparison, the composite reduces to the remaining two sides.

```agda
abstract
  factored-square : {s a b c d z : Obj}
    (outer : Hom c z) (left : Hom b c) (right : Hom a d)
    (input : Hom a b) (action : Hom d c) (changed : Hom d z)
    (tail : Hom s a) (image : Hom s b)
    → (outer ∘ action) ≈ changed
    → (left ∘ input) ≈ (action ∘ right)
    → image ≈ (input ∘ tail)
    → ((outer ∘ left) ∘ image) ≈ ((changed ∘ right) ∘ tail)
  factored-square outer left right input action changed tail image cancelAction natural factor =
    trans (sym (assoc changed right tail))
      (trans (congr cancelAction (refl (right ∘ tail)))
      (trans (sym (assoc outer action (right ∘ tail)))
      (trans (congr (refl outer) (assoc action right tail))
      (trans (congr (refl outer) (congr natural (refl tail)))
      (trans (congr (refl outer) (sym (assoc left input tail)))
      (trans (assoc outer left (input ∘ tail))
        (congr (refl (outer ∘ left)) factor)))))))
```

For a common frame, paste the restriction square with the naturality square,
merge the two images, and cancel the supplied reverse frame comparison. The
fourfold reassociation and the frame cancellation are specified inputs, so
applications can retain their existing witnesses even when those arise from
a different realization of the elementary laws.

```agda
abstract
  common-frame-pasting : {s₀ s₁ s₂ s₃ s₄ r₀ r₁ r₂ z : Obj}
    (outer : Hom s₄ z) (G : Hom s₃ s₄) (A : Hom s₂ s₃) (N : Hom s₂ z)
    (pre : Hom s₁ s₂) (W : Hom s₀ s₁)
    (W₁ : Hom r₁ s₃) (W₂ : Hom r₂ s₄)
    (paired : Hom r₁ r₂) (pairPre : Hom r₀ r₁) (postB : Hom r₀ r₂)
    (frame : Hom s₀ r₀) (back : Hom r₀ s₀)
    → N ≈ (outer ∘ (G ∘ A))
    → (A ∘ (pre ∘ W)) ≈ (W₁ ∘ (pairPre ∘ frame))
    → (G ∘ W₁) ≈ (W₂ ∘ paired)
    → (paired ∘ pairPre) ≈ postB
    → ((W₂ ∘ paired) ∘ (pairPre ∘ frame)) ≈ (W₂ ∘ ((paired ∘ pairPre) ∘ frame))
    → ((((outer ∘ W₂) ∘ postB) ∘ frame) ∘ back) ≈ ((outer ∘ W₂) ∘ postB)
    → (N ∘ (pre ∘ (W ∘ back))) ≈ ((outer ∘ W₂) ∘ postB)
  common-frame-pasting outer G A N pre W W₁ W₂ paired pairPre postB frame back
    splitN restriction natural merge regroupFour cancellation =
    let lower = trans
          (congr (refl outer)
            (trans (congr (refl W₂) (congr merge (refl frame))) regroupFour))
          (congr (refl outer)
            (trans (congr natural (refl (pairPre ∘ frame)))
              (sym (assoc G W₁ (pairPre ∘ frame)))))
        beforeCancel = trans (sym (assoc (outer ∘ W₂) postB frame))
          (trans (sym (assoc outer W₂ (postB ∘ frame)))
          (trans lower
          (trans (congr (refl outer) (congr (refl G) restriction))
          (trans (congr (refl outer) (assoc G A (pre ∘ W)))
          (trans (assoc outer (G ∘ A) (pre ∘ W))
            (congr splitN (refl (pre ∘ W))))))))
        regroup = trans (sym (assoc N (pre ∘ W) back))
          (congr (refl N) (sym (assoc pre W back)))
    in trans cancellation (trans (congr beforeCancel (refl back)) regroup)
```

A normalized operation is a comparison of its inputs after restriction.
For its short route, use the substitution square, iterate restriction,
and combine the two input comparisons. The iteration and combination
witnesses are supplied by the operation under consideration.

```agda
abstract
  normalized-substitution-square : {s₀ s₁ s₂ t₀ t₁ b z : Obj}
    (paired : Hom t₁ z) (newPre : Hom s₂ t₁) (change : Hom s₁ s₂)
    (A : Hom s₀ s₁) (changed : Hom t₀ t₁) (oldPre : Hom s₁ t₀)
    (action : Hom b t₀) (base : Hom s₀ b) (inner : Hom b t₁) (whole : Hom b z)
    → (newPre ∘ change) ≈ (changed ∘ oldPre)
    → (oldPre ∘ A) ≈ (action ∘ base)
    → (changed ∘ (action ∘ base)) ≈ (inner ∘ base)
    → (paired ∘ (inner ∘ base)) ≈ (whole ∘ base)
    → ((paired ∘ newPre) ∘ (change ∘ A)) ≈ (whole ∘ base)
  normalized-substitution-square paired newPre change A changed oldPre action base inner whole
    substituteSquare iteration combineInner combineOuter =
    let substitute = trans (assoc changed oldPre A)
          (trans (congr substituteSquare (refl A))
            (sym (assoc newPre change A)))
        iterate = congr (refl changed) iteration
    in trans combineOuter
      (trans (congr (refl paired) (trans combineInner (trans iterate substitute)))
        (assoc paired newPre (change ∘ A)))
```

For the long route, distribute restriction over the existing normalization,
use the input square, then combine its output comparisons.

```agda
abstract
  normalized-input-square : {s a b c e z : Obj}
    (outer : Hom e z) (middle : Hom c e) (input : Hom a c)
    (before : Hom s a) (output : Hom b e) (pre : Hom a b)
    (image : Hom s c) (whole : Hom b z)
    → (middle ∘ input) ≈ (output ∘ pre)
    → image ≈ (input ∘ before)
    → (outer ∘ (output ∘ (pre ∘ before))) ≈ (whole ∘ (pre ∘ before))
    → (outer ∘ (middle ∘ image)) ≈ (whole ∘ (pre ∘ before))
  normalized-input-square outer middle input before output pre image whole natural split combine =
    let exchange = trans (assoc output pre before)
          (trans (congr natural (refl before))
            (sym (assoc middle input before)))
    in trans combine
      (trans (congr (refl outer) exchange)
        (congr (refl outer) (congr (refl middle) split)))
```

Changing an input and restricting it give adjacent squares. Expand the
specified source comparison, paste the change square with the restriction
square, then combine the two actions on the output.

```agda
abstract
  change-restriction-square : {s a b x y z₀ z₁ : Obj}
    (left′ : Hom b z₁) (change : Hom a b) (middle : Hom a z₀)
    (first : Hom z₀ z₁) (second : Hom x z₀) (pre : Hom y x)
    (retained : Hom s y) (tail : Hom s a) (source : Hom s b) (whole : Hom x z₁)
    → (first ∘ second) ≈ whole
    → (middle ∘ tail) ≈ (second ∘ (pre ∘ retained))
    → (left′ ∘ change) ≈ (first ∘ middle)
    → source ≈ (change ∘ tail)
    → (left′ ∘ source) ≈ ((whole ∘ pre) ∘ retained)
  change-restriction-square left′ change middle first second pre retained tail source whole
    normalizeAction restriction natural expandSource =
    let normalizeEnd = trans (sym (assoc whole pre retained))
          (trans (congr normalizeAction (refl (pre ∘ retained)))
            (sym (assoc first second (pre ∘ retained))))
        useRestriction = trans (congr (refl first) restriction)
          (assoc first middle tail)
        useChange = trans (congr natural (refl tail))
          (sym (assoc left′ change tail))
        expand = congr (refl left′) expandSource
    in trans normalizeEnd (trans useRestriction (trans useChange expand))
```

A factored input can be transported through a square and then combined
with an outer comparison. The factorization, naturality, and combination
witnesses are explicit; the calculation only supplies the reassociations.

```agda
abstract
  compose-input-square : {s a b c e z : Obj}
    (outer : Hom e z) (middle : Hom c e) (input : Hom a c)
    (before : Hom s a) (output : Hom b e) (pre : Hom a b)
    (image : Hom s c) (whole : Hom b z)
    → (middle ∘ input) ≈ (output ∘ pre)
    → (outer ∘ output) ≈ whole
    → image ≈ (input ∘ before)
    → (outer ∘ (middle ∘ image)) ≈ (whole ∘ (pre ∘ before))
  compose-input-square outer middle input before output pre image whole natural join split =
    let exchange = trans (assoc output pre before)
          (trans (congr natural (refl before))
            (sym (assoc middle input before)))
        expand = congr (refl middle) split
    in trans (congr join (refl (pre ∘ before)))
      (trans (sym (assoc outer output (pre ∘ before)))
        (congr (refl outer) (trans exchange expand)))
```

A square remains commutative after adjoining the same tail to both routes.
For a route with two initial comparisons, the second calculation includes
its additional reassociation explicitly.

```agda
abstract
  square-with-tail : {s a b c z : Obj}
    (left : Hom b z) (bottom : Hom a b)
    (top : Hom c z) (right : Hom a c) (tail : Hom s a)
    → (left ∘ bottom) ≈ (top ∘ right)
    → (left ∘ (bottom ∘ tail)) ≈ (top ∘ (right ∘ tail))
  square-with-tail left bottom top right tail square =
    trans (assoc top right tail)
      (trans (congr square (refl tail)) (sym (assoc left bottom tail)))

  composite-square-with-tail : {s a b c d z : Obj}
    (left : Hom c z) (middle : Hom b c) (bottom : Hom a b)
    (top : Hom d z) (right : Hom a d) (tail : Hom s a)
    → ((left ∘ middle) ∘ bottom) ≈ (top ∘ right)
    → (left ∘ (middle ∘ (bottom ∘ tail))) ≈ (top ∘ (right ∘ tail))
  composite-square-with-tail left middle bottom top right tail square =
    trans (assoc top right tail)
      (trans (congr square (refl tail))
        (trans (sym (assoc (left ∘ middle) bottom tail))
          (sym (assoc left middle (bottom ∘ tail)))))
```

Two successive input comparisons can be normalized along a naturality
square. Supply both combination comparisons separately, so the result
retains their prescribed witnesses.

```agda
abstract
  normalize-comparison-route : {s t a b c d z : Obj}
    (outer : Hom d z) (first : Hom c d) (second : Hom b c) (third : Hom a b)
    (after : Hom t c) (e : Hom s t) (sourceAfter : Hom s b) (tail : Hom s a)
    (inner : Hom a c) (whole : Hom a d)
    → (second ∘ (third ∘ tail)) ≈ (inner ∘ tail)
    → (first ∘ (inner ∘ tail)) ≈ (whole ∘ tail)
    → (after ∘ e) ≈ (second ∘ sourceAfter)
    → sourceAfter ≈ (third ∘ tail)
    → ((outer ∘ (first ∘ after)) ∘ e) ≈ (outer ∘ (whole ∘ tail))
  normalize-comparison-route outer first second third after e sourceAfter tail inner whole
    joinInner joinOuter natural restrict =
    let normalize = trans joinOuter
          (congr (refl first) (trans joinInner (congr (refl second) restrict)))
        expand = trans (congr (refl outer)
            (trans (congr (refl first) natural) (assoc first after e)))
          (assoc outer (first ∘ after) e)
    in trans (congr (refl outer) normalize) expand
```


For a nested input, keep the boundary routes as parameters while pasting
restriction, naturality, and the two input-combination comparisons. The
application-specific calculations supply these comparisons; the following
assembly only performs the displayed congruences and reassociations.

```agda
module NestedRoute {s n q r c d e u v z : Obj}
  (N : Hom n z) (Pg : Hom q n) (V : Hom s q)
  (changed : Hom c z) (restricted : Hom n c)
  (C₀ : Hom r q) (rest : Hom s r)
  (C₁ : Hom d c) (middle : Hom r d)
  (C₂ : Hom e z) (Qact : Hom d e)
  (Ract : Hom u d) (Uact : Hom v u) (base : Hom s v)
  (inner : Hom v d) (whole : Hom v e) where

  abstract
    finish : (middle ∘ rest) ≈ (Ract ∘ (Uact ∘ base))
      → (Ract ∘ (Uact ∘ base)) ≈ (inner ∘ base)
      → (Qact ∘ (inner ∘ base)) ≈ (whole ∘ base)
      → (C₂ ∘ (Qact ∘ (middle ∘ rest))) ≈ (C₂ ∘ (whole ∘ base))
    finish project combineInner combineOuter =
      congr (refl C₂)
        (trans combineOuter (congr (refl Qact) (trans combineInner project)))

    begin : N ≈ (changed ∘ restricted) → V ≈ (C₀ ∘ rest)
      → (N ∘ (Pg ∘ V)) ≈ (changed ∘ (restricted ∘ (Pg ∘ (C₀ ∘ rest))))
    begin split expand = trans (assoc changed restricted (Pg ∘ (C₀ ∘ rest)))
      (congr split (congr (refl Pg) expand))

    result : (C₂ ∘ (Qact ∘ (middle ∘ rest))) ≈ (C₂ ∘ (whole ∘ base))
      → (changed ∘ (C₁ ∘ (middle ∘ rest))) ≈ (C₂ ∘ (Qact ∘ (middle ∘ rest)))
      → (restricted ∘ (Pg ∘ (C₀ ∘ rest))) ≈ (C₁ ∘ (middle ∘ rest))
      → (N ∘ (Pg ∘ V)) ≈ (changed ∘ (restricted ∘ (Pg ∘ (C₀ ∘ rest))))
      → (N ∘ (Pg ∘ V)) ≈ (C₂ ∘ (whole ∘ base))
    result finish natural restrict begin =
      trans finish (trans natural (trans (congr (refl changed) restrict) begin))
```


Naturality can be transported between two chosen normalization routes.
The four route squares and the central naturality square remain explicit.
The conclusion retains the common final comparison, which a caller may
subsequently cancel using its chosen reflection operation.

```agda
abstract
  normalization-naturality : {x₀ x₁ y₀ y₁ u₀ u₁ v₀ v₁ : Obj}
    (a : Hom x₀ y₀) (a′ : Hom x₁ y₁) (S : Hom x₀ x₁) (T : Hom y₀ y₁)
    (L : Hom x₀ u₀) (L′ : Hom x₁ u₁) (R : Hom y₀ v₀) (R′ : Hom y₁ v₁)
    (l : Hom u₀ u₁) (r : Hom v₀ v₁) (A : Hom u₀ v₀) (A′ : Hom u₁ v₁)
    → (R ∘ a) ≈ (A ∘ L) → (R′ ∘ a′) ≈ (A′ ∘ L′)
    → (L′ ∘ S) ≈ (l ∘ L) → (R′ ∘ T) ≈ (r ∘ R)
    → (A′ ∘ l) ≈ (r ∘ A)
    → (R′ ∘ (a′ ∘ S)) ≈ (R′ ∘ (T ∘ a))
  normalization-naturality a a′ S T L L′ R R′ l r A A′
    route route′ left right central =
    trans (assoc R′ T a)
      (trans (congr (sym right) (refl a))
      (trans (sym (assoc r R a))
      (trans (congr (refl r) (sym route))
      (trans (assoc r A L)
      (trans (congr central (refl L))
      (trans (sym (assoc A′ l L))
      (trans (congr (refl A′) left)
      (trans (assoc A′ L′ S)
      (trans (congr route′ (refl S))
        (sym (assoc R′ a′ S)))))))))))
```

Changing the source and target frames of a square uses the prescribed
normalization of its input and the prescribed cancellation of the target
frame. No inverse operation or uniqueness of comparison proofs is assumed.

```agda
abstract
  normalized-frame-square : {x a b y d e : Obj}
    (k : Hom a d) (k′ : Hom b e) (back : Hom x a)
    (v : Hom b y) (reverse : Hom y b) (z : Hom a b) (w : Hom d e)
    (input : Hom x y)
    → (k′ ∘ z) ≈ (w ∘ k)
    → (reverse ∘ (v ∘ (z ∘ back))) ≈ (z ∘ back)
    → input ≈ (v ∘ (z ∘ back))
    → ((k′ ∘ reverse) ∘ input) ≈ (w ∘ (k ∘ back))
  normalized-frame-square k k′ back v reverse z w input natural cancel normalize =
    trans (assoc w k back)
      (trans (congr natural (refl back))
      (trans (sym (assoc k′ z back))
      (trans (congr (refl k′) cancel)
      (trans (assoc k′ reverse (v ∘ (z ∘ back)))
        (congr (refl (k′ ∘ reverse)) normalize)))))
```
