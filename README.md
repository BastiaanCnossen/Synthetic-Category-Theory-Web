# Synthetic category theory: experimental web edition

This repository contains an experimental web edition of the opening of *Synthetic category theory*, a book in preparation by Denis-Charles Cisinski, Bastiaan Cnossen and Tashi Walde. It currently covers the chapter introduction and Sections 1.1 and 1.2 together with an Agda formalization of the same material. It should eventually cover the entire book.

The site is hosted by GitHub Pages, directly from this repository: <https://bastiaancnossen.github.io/Synthetic-Category-Theory-Web/>

## About this experiment

For now, this website is an experiment carried out by Bastiaan Cnossen. I used substantial AI assistance in building the webpage, the automatic conversion of tex into html, the reader interface, and the presentation around the mathematics. My coauthors are aware of the experiment, but they do not necessarily endorse it; responsibility for this site rests with me alone, at least for now. In particular, I take full responsibility for the usage of AI for creating this site, and no inference should be made on this basis regarding my coauthors' opinions on AI.

The mathematics displayed on this website is directly taken from our joint project, automatically extracted via python scripts. Any error introduced by the conversion is mine.

Given the experimental nature of this webpage, I wish to mostly keep this webpage under the radar for now. The reason this is a public repository is only because GitHub Pages requires a public repository on a free plan.

## Terms

All rights reserved. No licence is granted for reuse of the manuscript text, the formalization, or the generated pages. The vendored MathJax runtime in `vendor/mathjax/` is redistributed under its own licence; see `vendor/mathjax/LICENSE` and [THIRD_PARTY.md](THIRD_PARTY.md) for the provenance of every borrowed asset.

## What is in this repository

The generated website is in `_site/`. GitHub Pages deploys exactly that directory through the repository's Pages workflow. It contains the HTML pages, reader assets, diagram SVGs, selected Agda module pages, and the self-contained MathJax runtime.

The complete Agda formalization lives in `agda/`, with modules under `agda/src/`. Its later and exploratory developments remain available in the repository even when they are outside the material displayed on the site. The site currently publishes the checked dependency closure for Sections 1.1 and 1.2.

The manuscript is read directly from a private SCT checkout on `codex/web-annotations`. This repository contains no maintained copies of the manuscript's TeX files. Passage comments remain private; `correspondence.json` connects passage IDs to Agda declarations and proof regions. `scripts/`, `assets/`, `docs/*.html`, and `vendor/` supply the conversion and reader.

## Reading a local copy

Everything needed to read the site is committed under `_site/`, so a clone can be read without installing LaTeX or Agda. On Windows, run `serve.ps1` and open `http://127.0.0.1:8765/index.html`. Any static HTTP server rooted at `_site/` will do as well. The book selection is also available as `_site/book.pdf`.

Rebuilding requires access to the private annotated manuscript, Python, Agda, and the TeX toolchain. `build.ps1` uses the adjacent `Synthetic Category Theory Web Annotations` checkout by default; `SCT_MANUSCRIPT` can specify its location. It verifies the annotation baseline before rebuilding `_site/`.

Build and annotation maintenance records are kept in the private editorial workspace, outside this public repository. Temporary inputs and build logs stay in ignored `_build/` directories.
