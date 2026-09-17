# Agda formalization of synthetic category theory

This directory contains the complete experimental formalization, organized by
volume, chapter and section under `src/SCT/`. The source includes developments
through Sections 1.1 to 1.8 and a separate investigations directory.

The web edition currently displays the checked dependency closure of Sections
1.1 and 1.2. The remaining modules are available here for inspection, but are
not yet part of the website's code browser.

## Reading the source

1. [Vocabulary](src/SCT/VolumeI/Chapter01/Section01/Vocabulary.lagda.md)
   introduces `CAT`, `isAn`, `MAP`, bundled `AN`, and primitive identifications.
2. [Coherence](src/SCT/VolumeI/Chapter01/Section01/Coherence.lagda.md)
   supplies the primitive coherence families; horizontal composition is derived.
3. [Specialization](src/SCT/VolumeI/Chapter01/Section01/Specialization.lagda.md)
   develops lifting, substitution and unit comparisons.
4. [Equivalences](src/SCT/VolumeI/Chapter01/Section02/Equivalences.lagda.md)
   begins the equivalence calculus.
5. [The main aggregate](src/SCT/Everything.agda) gives access to the broader
   development. [The web aggregate](src/SCT/WebEdition.agda) selects the
   modules currently displayed on the site.

## Checking

Every source declares `--safe --without-K`. The only external import is
`Agda.Primitive`; no standard library is required. The web selection was freshly
checked with Agda `2.8.0-3d04bac` during this migration. That run does not certify
all later modules afresh.

From this directory:

```powershell
agda --no-libraries --safe --without-K --ignore-interfaces -i src src/SCT/WebEdition.agda
```

To check the broader main development from source:

```powershell
agda --transliterate --no-libraries --ignore-interfaces -i src src/SCT/Everything.agda
```

The investigations have a separate aggregate:

```powershell
agda --no-libraries --ignore-interfaces -i src src/SCT/Investigations/Everything.agda
```

These are derivations conditional on explicit interfaces for the book's axioms.
A record of axioms does not construct an instance, and the checks are not a
consistency proof or a verification of the correspondence with the entire book.
The literate sources describe their assumptions and constructions. Internal
planning and audit records are retained privately.
