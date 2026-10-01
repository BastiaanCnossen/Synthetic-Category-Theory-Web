# Agda formalization of synthetic category theory

This directory contains the Agda formalization accompanying Volume I of
*Synthetic Category Theory*. The canonical sources are in `src/SCT/`,
organized by chapter and section. They contain developments for Chapters 1–3
and ongoing work on Chapters 4 and 5; the presence of a chapter directory does
not imply that every result in that chapter has been formalized.

The proofs are conditional on explicit interfaces for the book's axioms.
Checking a derivation does not construct a model of those interfaces or certify
its correspondence with every detail of the manuscript.

## Reading the source

Mathematical modules use literate Markdown (`.lagda.md`), combining explanation
with Agda code. Supporting calculations are grouped in subdirectories beside
the principal arguments. `Everything.agda` files are checking entry points,
not suggested reading orders.

Begin with:

1. [Vocabulary](src/SCT/VolumeI/Chapter01/Section01/Vocabulary.lagda.md),
   introducing `CAT`, `MAP`, animae, and primitive identifications.
2. [Coherence](src/SCT/VolumeI/Chapter01/Section02/Coherence.lagda.md),
   specifying the basic coherence data.
3. [Theory](src/SCT/VolumeI/Chapter01/Theory.lagda.md), collecting the foundational
   assumptions used by subsequent constructions.
4. [Equivalences](src/SCT/VolumeI/Chapter01/Section03/Equivalences.lagda.md),
   beginning the equivalence calculus.

The [reading guide](ReadingGuide.md) describes the principal arguments and
supporting libraries throughout the development.

## Source organization

1. `src/SCT/VolumeI/Chapter01/` through `Chapter05/` use the formalization's
   retained numbering. Here Chapter 4 concerns cartesian and cocartesian
   fibrations, and Chapter 5 concerns categories in context. These folder numbers
   are not yet synchronized with the latest manuscript ordering.
2. `src/SCT/Calculus/` contains reusable composition, pasting, and square
   calculations used by the chapter proofs.
3. `src/SCT/Investigations/` isolates conditional results and unresolved
   comparison questions. Its extra hypotheses are explicit.
4. `src/SCT/VolumeI/Deferred/` retains mathematical developments awaiting
   placement in the chapter structure.
5. [SCT.Everything](src/SCT/Everything.agda) is the main aggregate.
   [SCT.WebEdition](src/SCT/WebEdition.agda) selects the reader's source scope
   from Chapters 1–3. The published checked snapshot may lag behind these
   working sources.

## Checking

The development uses Agda 2.8.0, with `--safe --without-K` and no standard-library
dependency. Some modules also select local inference options. `sct.agda-lib`
sets `src` as the include root.

For a local edit, check the affected module and selected consumers, retaining
cached interfaces. From this `agda` directory, for example:

```powershell
agda --no-libraries --safe --without-K -i src src/SCT/VolumeI/Chapter01/Section03/Equivalences.lagda.md
```

For a chapter integration check, first inspect the scope. From the repository
root (one directory above this README):

```powershell
python scripts/check_agda.py --chapter 1 --plan
python scripts/check_agda.py --chapter 1
```

The checker reuses cached interfaces and records the selected scope and result.
Routine mode excludes the known expensive Chapter 3 uncurrying modules and
all their transitive consumers. Add `--full` only when intentionally checking
that excluded branch as well. Omitting `--chapter` selects the whole routine
scope and can still take substantial time. Routine checks are not publication
verification receipts.

Do not clear `_build/` or delete `.agdai` interfaces for ordinary incremental
checks. Historical local plans and coverage reports are retained privately; their old
numbering and verification claims do not describe the current sources.
